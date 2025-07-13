const std = @import("std");

const set = @import("ziglangSet");

pub const EntryId = usize;
pub const TypeId = usize;

pub const Ty = union(enum) {
    variable: EntryId, // Type variable. We want to solve for those.
    concrete: TypeId, // Primitives and similar.
    applicative: Applicative, // Stuff like `N<T1, ..., Tn>`.
    tuple: []TypeId, // Group of types, e.g. `(int, str, int)`. This can be used for structs.
    @"union": set.HashSetUnmanaged(TypeId), // E.g. `oneof [int, string]`.

    pub const Applicative = struct {
        id: usize,
        params: []TypeId,
    };

    pub fn format(
        self: Ty,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;

        switch (self) {
            .variable => |id| try writer.print("?T{d}", .{id}),
            .concrete => |id| try writer.print("C#{d}", .{id}),
            .applicative => |a| {
                try writer.print("%{d}<", .{a.id});
                for (a.params, 0..) |ty, i| {
                    try writer.print("{}", .{ty});
                    if (i < a.params.len - 1)
                        try writer.writeAll(", ");
                }
                try writer.writeByte('>');
            },
            .tuple => |tup| {
                try writer.writeAll("(");
                for (tup, 0..) |ty, i| {
                    try writer.print("{d}", .{ty});
                    if (i < tup.len - 1)
                        try writer.writeAll(", ");
                }
                try writer.writeByte(')');
            },
            .@"union" => |u| {
                try writer.writeAll("oneof{ ");
                var iter = u.iterator();
                var i: usize = 0;
                while (iter.next()) |ty| {
                    defer i += 1;
                    try writer.print("{d}", .{ty.*});
                    if (i < u.cardinality() - 1)
                        try writer.writeAll(", ");
                }
                try writer.writeAll(" }");
            },
        }
    }
};

pub const Solver = struct {
    self: *anyopaque,
    solve_fn: *const SolveFn,

    const SolveFn = fn (self: *anyopaque, cx: *Context, constraint: Constraint) anyerror![]const Constraint;
};

pub const Constraint = struct {
    solver: usize,
    params: []const TypeId,

    monomorphize_unions: bool = true,
    is_signature: bool = false,
    combine_groups: ?[]const TypeId = null,
};

pub const Signature = struct {
    params: []TypeId,
    constraints: []usize,
};

pub const Context = struct {
    arena: std.heap.ArenaAllocator,
    allocator: std.mem.Allocator,

    types: std.ArrayListUnmanaged(Ty) = .{},
    entries: std.ArrayListUnmanaged(Entry) = .{},

    solvers: std.ArrayListUnmanaged(Solver) = .{},
    worklist: std.ArrayListUnmanaged(Constraint) = .{},

    signature_stack: std.ArrayListUnmanaged(struct {
        params: std.ArrayListUnmanaged(TypeId) = .{},
        constraints: std.ArrayListUnmanaged(usize) = .{},
    }) = .{},

    pub const Entry = union(enum) {
        unresolved: void, // We know nothing about this type.
        parameter: void, // We do not want to know anything about this type as it is a placeholder.
        link: EntryId, // This type is the same as EntryId.
        resolved: TypeId, // We know the main element of this type, but some parts remain unresolved.
        qualified: TypeId, // This type is fully known.

        pub fn format(
            self: Entry,
            comptime fmt: []const u8,
            options: std.fmt.FormatOptions,
            writer: anytype,
        ) !void {
            _ = fmt;
            _ = options;

            switch (self) {
                .unresolved => try writer.writeAll("unresolved"),
                .parameter => try writer.writeAll("parameter"),
                .link => |link| try writer.print("link:{d}", .{link}),
                .resolved => |tid| try writer.print("resolved:{d}", .{tid}),
                .qualified => |tid| try writer.print("qualified:{d}", .{tid}),
            }
        }
    };

    const Self = @This();
    pub fn init(allocator: std.mem.Allocator) Self {
        return .{
            .arena = .init(allocator),
            .allocator = allocator,
        };
    }
    pub fn deinit(self: *Self) void {
        self.arena.deinit();
        self.types.deinit(self.allocator);
        self.entries.deinit(self.allocator);
        self.solvers.deinit(self.allocator);
        self.worklist.deinit(self.allocator);
    }

    pub fn newTypeVar(self: *Self) !TypeId {
        const id = self.entries.items.len;
        try self.entries.append(self.allocator, .unresolved);
        return try self.addType(.{ .variable = id });
    }
    pub fn newParam(self: *Self) !TypeId {
        const id = self.entries.items.len;
        try self.entries.append(self.allocator, .parameter);
        const type_id = try self.addType(.{ .variable = id });
        if (self.signature_stack.items.len > 0) {
            var last = &self.signature_stack.items[self.signature_stack.items.len - 1];
            try last.params.append(self.arena.allocator(), type_id);
        }
        return type_id;
    }
    pub fn newConcrete(self: *Self) !TypeId {
        return try self.addType(.{ .concrete = self.types.items.len + 1 });
    }
    pub fn newApplicative(self: *Self, id: usize, params: []const TypeId) !TypeId {
        return try self.addType(.{ .applicative = .{
            .id = id,
            .params = try self.arena.allocator().dupe(TypeId, params),
        } });
    }
    pub fn newTuple(self: *Self, elements: []const TypeId) !TypeId {
        return try self.addType(.{
            .tuple = try self.arena.allocator().dupe(TypeId, elements),
        });
    }
    pub fn newUnion(self: *Self, variants: []const TypeId) !TypeId {
        var u = set.HashSetUnmanaged(TypeId).init();
        const alloc = self.arena.allocator();
        for (variants) |ty|
            _ = try u.add(alloc, ty);
        return try self.addType(.{ .@"union" = u });
    }

    pub fn addType(self: *Self, ty: Ty) !TypeId {
        const current = self.types.items.len;
        try self.types.append(self.allocator, ty);
        return current;
    }

    pub fn findVariable(self: *Self, id: EntryId) !usize {
        for (self.types.items, 0..) |ty, i| {
            if (std.meta.activeTag(ty) == .variable and ty.variable == id)
                return i;
        }
        return try self.addType(.{ .variable = id });
    }

    fn newResolved(self: *Self, ty: TypeId) Entry {
        if (self.isQualified(ty))
            return .{ .qualified = ty }
        else
            return .{ .resolved = ty };
    }

    // Normalize type by resolving roots of variables,
    // following links, deeply exploring nested types, etc...
    pub fn normalize(self: *Self, t: TypeId) !TypeId {
        switch (self.types.items[t]) {
            .variable => |start| {
                var current = start;
                var path = std.ArrayList(EntryId).init(self.allocator);
                defer path.deinit();

                while (true) switch (self.entries.items[current]) {
                    .link => |next| {
                        try path.append(current);
                        current = next;
                    },
                    .unresolved, .parameter => {
                        self.compressPath(path.items, current);
                        return try self.findVariable(current);
                    },
                    .resolved, .qualified => |target| {
                        self.compressPath(path.items, current);
                        return target;
                    },
                };
            },
            .concrete => return t,
            .applicative => |app| {
                for (app.params, 0..) |typ, i|
                    app.params[i] = try self.normalize(typ);
                return t;
            },
            .tuple => |tup| {
                for (tup, 0..) |typ, i|
                    tup[i] = try self.normalize(typ);
                return t;
            },
            .@"union" => |*u| {
                // Re-create this union with new (normalized) types.
                var new = set.HashSetUnmanaged(TypeId).init();

                const alloc = self.arena.allocator();
                var iter = u.iterator();
                while (iter.next()) |typ| {
                    const norm = try self.normalize(typ.*);
                    switch (self.types.items[norm]) {
                        .@"union" => |nested| {
                            var nested_iter = nested.iterator();
                            while (nested_iter.next()) |nested_typ|
                                _ = try new.add(alloc, nested_typ.*);
                        },
                        else => _ = try new.add(alloc, norm),
                    }
                }
                return try self.addType(.{ .@"union" = new });
            },
        }
    }

    // Compress entries in path, so that they all point to root.
    // This does not validate whether types are links.
    fn compressPath(self: *Self, path: []const EntryId, root: EntryId) void {
        for (path) |seg|
            self.entries.items[seg] = .{ .link = root };
    }

    // Checks whether all leafs are concrete types.
    pub fn isQualified(self: *Self, t: TypeId) bool {
        switch (self.types.items[t]) {
            .variable => return false,
            .concrete => return true,
            .applicative => |app| {
                for (app.params) |typ| {
                    if (!self.isQualified(typ)) return false;
                }
                return true;
            },
            .tuple => |tup| {
                for (tup) |typ| {
                    if (!self.isQualified(typ)) return false;
                }
                return true;
            },
            .@"union" => |u| {
                var iter = u.iterator();
                while (iter.next()) |typ| {
                    if (!self.isQualified(typ.*)) return false;
                }
                return true;
            },
        }
    }

    // If (variable) true else false;
    pub fn isOpen(self: *Self, t: TypeId) !bool {
        const norm = try self.normalize(t);
        return switch (self.types.items[norm]) {
            .variable => true,
            else => false,
        };
    }

    pub fn unify(self: *Self, a: TypeId, b: TypeId) !void {
        const na = try self.normalize(a);
        const nb = try self.normalize(b);

        var ta = self.types.items[na];
        var tb = self.types.items[nb];

        if (std.meta.eql(ta, tb)) return;
        std.debug.print("unify {any} + {any}\n", .{ ta, tb });

        switch (ta) {
            .variable => |va| switch (tb) {
                .variable => |vb| self.entries.items[va] = .{ .link = vb },
                else => self.entries.items[va] = self.newResolved(nb),
            },

            .concrete => |ca| switch (tb) {
                .variable => |vb| self.entries.items[vb] = .{ .qualified = na },
                .concrete => |cb| if (ca != cb) {
                    var u = set.HashSetUnmanaged(usize).init();
                    const alloc = self.arena.allocator();
                    const old_t = try self.addType(ta);
                    _ = try u.add(alloc, old_t);
                    _ = try u.add(alloc, nb);
                    self.types.items[na] = .{ .@"union" = u }; // We only change A.
                },
                // TODO: Maybe this should support concrete + union -> union?
                else => return error.TypeMismatch,
            },

            .applicative => |appa| switch (tb) {
                .variable => |vb| self.entries.items[vb] = self.newResolved(nb),
                .applicative => |appb| {
                    if (appa.id != appb.id) return error.TypeMismatch;
                    if (appa.params.len != appb.params.len) return error.TypeArityMismatch;

                    for (appa.params, appb.params) |aty, bty|
                        try self.unify(aty, bty);
                },
                else => return error.TypeMismatch,
            },

            .tuple => |tupa| switch (tb) {
                .variable => |vb| self.entries.items[vb] = self.newResolved(nb),
                .tuple => |tupb| {
                    if (tupa.len != tupb.len) return error.TypeArityMismatch;

                    for (tupa, tupb) |aty, bty|
                        try self.unify(aty, bty);
                },
                else => return error.TypeMismatch,
            },

            .@"union" => |*ua| switch (tb) {
                .variable => |vb| self.entries.items[vb] = self.newResolved(nb),
                .@"union" => |*ub| {
                    const alloc = self.arena.allocator();

                    var b_iter = ub.iterator();
                    while (b_iter.next()) |key|
                        _ = try ua.add(alloc, key.*);
                },
                .concrete => |cb| {
                    const alloc = self.arena.allocator();
                    _ = try ua.add(alloc, cb);
                },
                else => return error.TypeMismatch,
            },
        }

        // Convert resolved -> qualified if possible.
        if (std.meta.activeTag(self.types.items[a]) == .variable and self.isQualified(na)) {
            self.entries.items[self.types.items[a].variable] = .{ .qualified = na };
        }
        if (std.meta.activeTag(self.types.items[b]) == .variable and self.isQualified(nb)) {
            self.entries.items[self.types.items[b].variable] = .{ .qualified = nb };
        }
    }

    pub fn beginSignature(self: *Self) !void {
        try self.signature_stack.append(self.arena.allocator(), .{});
    }

    pub fn endSignature(self: *Self) !Signature {
        var last = self.signature_stack.pop().?;
        return .{
            .params = try last.params.toOwnedSlice(self.arena.allocator()),
            .constraints = try last.constraints.toOwnedSlice(self.arena.allocator()),
        };
    }

    // Clone signature. This function assumes that everything passes as `ty` is a parameter.
    // It will clone all provided variables and constraints related to them.
    pub fn cloneSignature(self: *Self, sig: Signature) ![]const TypeId {
        const alloc = self.arena.allocator();
        var fresh_vars = try alloc.alloc(TypeId, sig.params.len);

        for (sig.params, 0..) |param, i| {
            fresh_vars[i] = blk: switch (self.types.items[param]) {
                .variable => |_| break :blk try self.newTypeVar(),
                else => unreachable,
            };
        }

        for (sig.constraints) |c| {
            const constraint = self.worklist.items[c];
            var new_params = try alloc.alloc(TypeId, constraint.params.len);
            for (constraint.params, 0..) |param, i| {
                const old_index = std.mem.indexOf(TypeId, sig.params, &.{param});
                if (old_index == null) return error.InvalidSignature;
                new_params[i] = fresh_vars[old_index.?];
            }

            try self.addConstraint(.{
                .solver = constraint.solver,
                .params = new_params,
                .monomorphize_unions = constraint.monomorphize_unions,
                .combine_groups = constraint.combine_groups,
            });
        }

        return fresh_vars;
    }

    pub fn registerSolver(self: *Self, solver: anytype) !usize {
        const current = self.solvers.items.len;
        try self.solvers.append(self.allocator, .{
            .self = @ptrCast(@constCast(solver)),
            .solve_fn = @ptrCast(&@typeInfo(@TypeOf(solver)).pointer.child.solve),
        });
        return current;
    }

    pub fn addConstraint(self: *Self, constraint: Constraint) !void {
        var c = constraint;
        if (self.signature_stack.items.len > 0) {
            var last = &self.signature_stack.items[self.signature_stack.items.len - 1];
            try last.constraints.append(self.arena.allocator(), self.worklist.items.len);
            c.is_signature = true;
        }
        try self.worklist.append(self.allocator, c);
    }

    pub fn solveConstraints(self: *Self) !void {
        var arena = std.heap.ArenaAllocator.init(self.allocator);
        const alloc = arena.allocator();
        defer arena.deinit();

        var result_groups = std.AutoHashMap(EntryId, std.ArrayList(TypeId)).init(self.allocator);
        defer result_groups.deinit();

        while (self.worklist.pop()) |c| {
            if (c.is_signature) continue;
            const solver = self.solvers.items[c.solver];

            if (c.monomorphize_unions) {
                const norm_params = try self.allocator.alloc(TypeId, c.params.len);
                defer self.allocator.free(norm_params);
                var params_vars = std.ArrayList(EntryId).init(alloc);
                for (c.params, 0..) |p, i| norm_params[i] = try self.normalize(p);
                for (0..c.params.len) |i| {
                    if (try self.isOpen(norm_params[i])) {
                        const t = self.types.items[norm_params[i]];
                        try params_vars.append(t.variable);
                    }
                }

                const combos = try self.allCombinations(norm_params, alloc);
                std.debug.print("combos: {any}\n", .{combos.items});

                for (combos.items, 1..) |combo, combo_i| {
                    // Generate fresh type-parameters.
                    const fresh = try alloc.alloc(TypeId, combo.len);
                    for (combo, 0..) |ty, i| {
                        if (try self.isOpen(ty)) {
                            const new_var = try self.newTypeVar();
                            fresh[i] = new_var;
                            if (result_groups.getPtr(self.types.items[ty].variable)) |t| {
                                try t.append(new_var);
                            } else {
                                var al = try std.ArrayList(TypeId).initCapacity(alloc, 1);
                                try al.append(new_var);
                                try result_groups.put(self.types.items[ty].variable, al);
                            }
                        } else fresh[i] = ty;
                    }

                    // Put new constraint.
                    const new_constraint = Constraint{
                        .solver = c.solver,
                        .params = fresh,
                        .monomorphize_unions = false,
                        .combine_groups = if (combo_i == combos.items.len) params_vars.items else null,
                    };
                    try self.worklist.append(self.allocator, new_constraint);
                }
            } else {
                const extra = solver.solve_fn(solver.self, self, c) catch |err| {
                    if (err == error.Unsat) {
                        std.debug.print("Solver {d} could not be satisfied with {any}.", .{ c.solver, c.params });
                    }
                    return err;
                };

                if (c.combine_groups) |cg| {
                    for (cg) |g| {
                        while (result_groups.fetchRemove(g)) |kv| {
                            std.debug.print("combining group #{d}: {any}\n", .{ g, kv.value.items });
                            const new_union = try self.newUnion(kv.value.items);
                            try self.unify(try self.findVariable(kv.key), new_union);
                        }
                    }
                }

                try self.worklist.appendSlice(self.allocator, extra);
            }
        }

        for (self.entries.items) |*entry| {
            switch (entry.*) {
                .link => |id| {
                    const item = self.entries.items[id];
                    switch (item) {
                        .resolved, .qualified => |ty| entry.* = self.newResolved(try self.normalize(ty)),
                        else => {},
                    }
                },
                .resolved => |ty| entry.* = self.newResolved(try self.normalize(ty)),
                .qualified, .unresolved, .parameter => {},
            }
        }

        for (self.entries.items, 0..) |entry, i| {
            const active = std.meta.activeTag(entry);
            if (active != .qualified and active != .parameter) {
                std.debug.print("Type variable ?T{d} remains unqualified.\n", .{i});
                return error.UnsatisfiedConstraints;
            }
        }
    }

    pub fn dump(self: *Self) void {
        for (self.entries.items, 0..) |entry, i|
            std.debug.print("ENTRY {d} := {}\n", .{ i, entry });
        for (self.types.items, 0..) |typ, i|
            std.debug.print("TYPE {d} := {}\n", .{ i, typ });
    }

    fn allCombinations(self: *Self, items: []const TypeId, arena: std.mem.Allocator) !std.ArrayList([]usize) {
        var combos = std.ArrayList([]usize).init(arena);

        var indices = try self.allocator.alloc(TypeId, items.len);
        defer self.allocator.free(indices);
        for (indices) |*i| i.* = 0;

        while (true) {
            var buf = try arena.alloc(usize, items.len);
            for (items, 0..) |item_i, i| {
                const item = self.types.items[item_i];
                buf[i] = blk: switch (item) {
                    .@"union" => |u| {
                        // Experimental implementation. To be optimized.
                        var iter = u.iterator();
                        for (0..indices[i]) |_| _ = iter.next();
                        break :blk iter.next().?.*;
                    },
                    else => break :blk item_i,
                };
            }
            try combos.append(buf);

            var pos: isize = @intCast(items.len - 1);
            while (pos >= 0) : (pos -= 1) {
                const pos_u: usize = @intCast(pos);
                if (std.meta.activeTag(self.types.items[items[pos_u]]) != .@"union") continue;
                const u = self.types.items[items[pos_u]].@"union";
                if (u.cardinality() == 1) continue;

                indices[pos_u] += 1;
                if (indices[pos_u] < u.cardinality())
                    break;
                indices[pos_u] = 0;
            }

            if (pos < 0) break;
        }

        return combos;
    }
};
