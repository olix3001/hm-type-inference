const std = @import("std");

pub const new = @import("new.zig");

pub const ApplicationId = usize;
pub const TypeId = usize;
pub const EntryId = usize;

fn DeepHashMapUnmanaged(comptime Key: type, comptime Value: type) type {
    const DeepHMContext = struct {
        pub fn hash(_: @This(), key: Key) u64 {
            var hasher = std.hash.Wyhash.init(0);
            std.hash.autoHashStrat(&hasher, key, .Shallow);
            return hasher.final();
        }

        pub fn eql(_: @This(), a: Key, b: Key) bool {
            return std.meta.eql(a, b);
        }
    };

    return std.hash_map.HashMapUnmanaged(Key, Value, DeepHMContext, 80);
}

pub const Ty = union(enum) {
    variable: EntryId, // Type variable. This is will be denoted by `?Tn`, where n is variable ID.
    concrete: TypeId, // Concrete/Known types. Those are mainly primitives.
    applicative: ApplicativeTy, // This is something like `N<T1, ..., Tn>`, where Tx is any other `Ty`.
    tuple: []Ty, // Group of types, e.g. `(int, str, int)`.
    @"union": DeepHashMapUnmanaged(Ty, void), // E.g. `oneof [int, string]`. This will check both possibilities.
    dict: std.AutoHashMapUnmanaged(usize, Ty), // Used when we have [key] -> T<key> mapping.

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
            .concrete => |id| try writer.print("#{d}", .{id}),
            .applicative => |a| {
                try writer.print("%{d}<", .{a.id});
                for (a.types, 0..) |ty, i| {
                    try writer.print("{}", .{ty});
                    if (i < a.types.len - 1)
                        try writer.writeAll(", ");
                }
                try writer.writeByte('>');
            },
            .tuple => |tup| {
                try writer.writeAll("tuple(");
                for (tup, 0..) |ty, i| {
                    try writer.print("{}", .{ty});
                    if (i < tup.len - 1)
                        try writer.writeAll(", ");
                }
                try writer.writeByte(')');
            },
            .@"union" => |u| {
                try writer.writeAll("union{ ");
                var iter = u.keyIterator();
                var i: usize = 0;
                while (iter.next()) |ty| {
                    defer i += 1;
                    try writer.print("{}", .{ty});
                    if (i < u.size - 1)
                        try writer.writeAll(", ");
                }
                try writer.writeAll(" }");
            },
            .dict => |dict| {
                try writer.writeAll("dict{ ");
                const len = dict.size;
                var iter = dict.iterator();
                var i: u32 = 0;
                while (iter.next()) |field| {
                    defer i += 1;
                    try writer.print("{d} -> {}", .{ field.key_ptr.*, field.value_ptr.* });
                    if (i < len - 1)
                        try writer.writeAll(", ");
                }
                try writer.writeAll(" }");
            },
        }
    }
};

pub const ApplicativeTy = struct {
    id: ApplicationId,
    types: []Ty,
};

const SolveFn = fn (self: *anyopaque, cx: *SolverContext, constraint: Constraint) anyerror![]const Constraint;
pub const Constraint = struct {
    solver: usize,
    params: []const Ty,

    monomorphize_unions: bool = true,
};
pub const ConstraintSolver = struct {
    self: *anyopaque,
    solve_fn: *const SolveFn,
};

pub const SolverContext = struct {
    arena: std.heap.ArenaAllocator,
    allocator: std.mem.Allocator,
    entries: std.ArrayListUnmanaged(Entry) = .{},
    solvers: std.ArrayListUnmanaged(ConstraintSolver) = .{},
    worklist: std.ArrayListUnmanaged(Constraint) = .{},
    concrete_amount: usize = 0,

    pub const Entry = union(enum) {
        unresolved: void,
        link: EntryId,
        resolved: Ty,
        qualified: Ty,
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
        self.entries.deinit(self.allocator);
        self.solvers.deinit(self.allocator);
        self.worklist.deinit(self.allocator);
    }

    // Creates fresh type variable with no constraints.
    pub fn newTypeVar(self: *Self) !Ty {
        const id = self.entries.items.len;
        try self.entries.append(self.allocator, .unresolved);
        return .{ .variable = id };
    }
    pub fn newConcrete(self: *Self) Ty {
        const current = self.concrete_amount;
        self.concrete_amount += 1;
        return .{ .concrete = current };
    }
    pub fn newApplicative(self: *Self, id: usize, params: []const Ty) !Ty {
        return .{ .applicative = .{
            .id = id,
            .types = try self.arena.allocator().dupe(Ty, params),
        } };
    }
    pub fn newTuple(self: *Self, elements: []const Ty) !Ty {
        return .{ .tuple = try self.arena.allocator().dupe(Ty, elements) };
    }
    pub fn newUnion(self: *Self, types: []const Ty) !Ty {
        var u = DeepHashMapUnmanaged(Ty, void){};
        const alloc = self.arena.allocator();
        for (types) |ty|
            try u.put(alloc, ty, void{});
        return .{ .@"union" = u };
    }
    pub fn newDict(self: *Self, entries: []const struct { usize, Ty }) !Ty {
        var dict = std.AutoHashMapUnmanaged(usize, Ty){};
        const alloc = self.arena.allocator();
        for (entries) |entry| {
            try dict.put(alloc, entry[0], entry[1]);
        }
        return .{ .dict = dict };
    }

    fn newResolved(self: *Self, ty: Ty) Entry {
        if (self.isFullyQualified(ty)) {
            return .{ .qualified = ty };
        } else {
            return .{ .resolved = ty };
        }
    }

    // Normalize type by resolving root of possible link chain.
    // This also compresses all traveled links into root.
    pub fn normalize(self: *Self, t: Ty) !Ty {
        switch (t) {
            .variable => |start| {
                var current = start;
                var path = std.ArrayList(EntryId).init(self.allocator);
                defer path.deinit();

                while (true) switch (self.entries.items[current]) {
                    .link => |next| {
                        try path.append(current);
                        current = next;
                    },
                    inline .resolved, .qualified => |typ| {
                        self.compressPath(path.items, current);
                        return typ;
                    },
                    .unresolved => {
                        self.compressPath(path.items, current);
                        return .{ .variable = current };
                    },
                };
            },
            .concrete => return t,
            .applicative => |app| {
                for (app.types, 0..) |typ, i| {
                    app.types[i] = try self.normalize(typ);
                }
                return .{ .applicative = app };
            },
            .tuple => |tuple| {
                for (tuple, 0..) |typ, i| {
                    tuple[i] = try self.normalize(typ);
                }
                return .{ .tuple = tuple };
            },
            .@"union" => |u| {
                // Can we avoid allocation here?
                var sub = DeepHashMapUnmanaged(Ty, void){};
                const alloc = self.arena.allocator();
                var iter = u.keyIterator();
                while (iter.next()) |key| {
                    const k: Ty = key.*;
                    const norm = try self.normalize(k);
                    switch (norm) {
                        .@"union" => |nested_union| {
                            var nested_iter = nested_union.keyIterator();
                            while (nested_iter.next()) |nested_key| {
                                const nk: Ty = nested_key.*;
                                try sub.put(alloc, nk, void{});
                            }
                        },
                        else => {
                            try sub.put(alloc, norm, void{});
                        },
                    }
                }
                return .{ .@"union" = sub };
            },
            .dict => |dict| {
                var iter = dict.valueIterator();
                while (iter.next()) |item| {
                    const norm = try self.normalize(item.*);
                    item.* = norm;
                }
                return .{ .dict = dict };
            },
        }
    }

    fn compressPath(self: *Self, path: []const EntryId, root: EntryId) void {
        for (path) |segment|
            self.entries.items[segment] = .{ .link = root };
    }

    // Checks whether all leaf types are concrete.
    pub fn isFullyQualified(self: *Self, ty: Ty) bool {
        switch (ty) {
            .variable => return false,
            .concrete => return true,
            .applicative => |app| {
                for (app.types) |typ| {
                    if (!self.isFullyQualified(typ)) return false;
                }
                return true;
            },
            .tuple => |tuple| {
                for (tuple) |typ| {
                    if (!self.isFullyQualified(typ)) return false;
                }
                return true;
            },
            .@"union" => |u| {
                var iter = u.keyIterator();
                while (iter.next()) |typ| {
                    if (!self.isFullyQualified(typ.*)) return false;
                }
                return true;
            },
            .dict => |dict| {
                var iter = dict.valueIterator();
                while (iter.next()) |typ| {
                    if (!self.isFullyQualified(typ.*)) return false;
                }
                return true;
            },
        }
    }

    pub fn isOpen(self: *Self, t: Ty) !bool {
        return switch (try self.normalize(t)) {
            .variable => true,
            else => false,
        };
    }

    // Try to unify two types into one.
    // For example if we use `unify(?T1, int)`, `?T1` will change its type into `int`.
    // This part is really complex, as it needs to handle all possible combinations of a and b types.
    pub fn unify(self: *Self, a: Ty, b: Ty) !void {
        var na = try self.normalize(a);
        var nb = try self.normalize(b);

        if (std.meta.eql(na, nb)) return;

        switch (na) {
            .variable => |va| switch (nb) {
                .variable => |vb| self.entries.items[va] = .{ .link = vb },
                else => self.entries.items[va] = self.newResolved(nb),
            },

            .concrete => |_| switch (nb) {
                .variable => |vb| self.entries.items[vb] = .{ .qualified = na },
                else => return error.TypeMismatch,
            },

            .applicative => |app_a| switch (nb) {
                .variable => |vb| self.entries.items[vb] = self.newResolved(nb),
                .applicative => |app_b| {
                    if (app_a.id != app_b.id) return error.TypeMismatch;
                    if (app_a.types.len != app_b.types.len) return error.TypeArityMismatch;

                    for (app_a.types, app_b.types) |a_ty, b_ty|
                        try self.unify(a_ty, b_ty);
                },
                else => return error.TypeMismatch,
            },

            .tuple => |*tup_a| switch (nb) {
                .variable => |vb| self.entries.items[vb] = self.newResolved(nb),
                .tuple => |*tup_b| {
                    if (tup_a.*.len != tup_b.*.len) return error.TypeArityMismatch;

                    for (tup_a.*, tup_b.*) |a_ty, b_ty|
                        try self.unify(a_ty, b_ty);

                    // Re-normalize tuples.
                    tup_a.* = (try self.normalize(.{ .tuple = tup_a.* })).tuple;
                    tup_b.* = (try self.normalize(.{ .tuple = tup_b.* })).tuple;
                },
                else => return error.TypeMismatch,
            },

            .@"union" => |*ua| switch (nb) {
                .variable => |vb| self.entries.items[vb] = self.newResolved(na),
                .@"union" => |*ub| {
                    var ua_iter = ua.keyIterator();
                    const alloc = self.arena.allocator();
                    while (ua_iter.next()) |key| {
                        try ub.put(alloc, key.*, void{});
                    }

                    var ub_iter = ub.keyIterator();
                    while (ub_iter.next()) |key| {
                        try ua.put(alloc, key.*, void{});
                    }
                },
                else => return error.TypeMismatch,
            },

            .dict => |da| switch (nb) {
                .variable => |vb| self.entries.items[vb] = self.newResolved(nb),
                .dict => |db| {
                    if (da.size != db.size) return error.TypeArityMismatch;

                    var iter = db.iterator();
                    while (iter.next()) |b_item| {
                        const maybe_a_item = da.getPtr(b_item.key_ptr.*);
                        if (maybe_a_item) |a_item| {
                            try self.unify(a_item.*, b_item.value_ptr.*);
                            a_item.* = try self.normalize(a_item.*);
                            b_item.value_ptr.* = try self.normalize(b_item.value_ptr.*);
                        } else {
                            return error.DictKeyMismatch;
                        }
                    }
                },
                else => return error.TypeMismatch,
            },
        }

        // Resolve possible variables.
        if (std.meta.activeTag(a) == .variable and self.isFullyQualified(na)) {
            self.entries.items[a.variable] = .{ .qualified = na };
        }
        if (std.meta.activeTag(b) == .variable and self.isFullyQualified(nb)) {
            self.entries.items[b.variable] = .{ .qualified = nb };
        }
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
        try self.worklist.append(self.allocator, constraint);
    }

    pub fn solveAll(self: *Self) !void {
        var arena = std.heap.ArenaAllocator.init(self.allocator);
        const alloc = arena.allocator();
        defer arena.deinit();

        var to_unionize = std.AutoHashMap(EntryId, std.ArrayList(Ty)).init(self.allocator);
        defer to_unionize.deinit();

        var stats_called: usize = 0;

        while (self.worklist.pop()) |c| {
            stats_called += 1;
            const solver = self.solvers.items[c.solver];

            if (c.monomorphize_unions) { // Break up union arguments into monomorphized checks.
                const norm_params = try self.allocator.alloc(Ty, c.params.len);
                defer self.allocator.free(norm_params);
                for (c.params, 0..) |p, i| norm_params[i] = try self.normalize(p);

                const combinations = try allCombinations(norm_params, alloc, self.allocator);

                for (combinations.items) |combo| {
                    // Replace open variables with fresh ones.
                    const fresh_params = try alloc.alloc(Ty, combo.len);
                    for (combo, 0..) |ty, i| {
                        if (try self.isOpen(ty)) {
                            const new_var = try self.newTypeVar();
                            fresh_params[i] = new_var;
                            if (to_unionize.getPtr(ty.variable)) |t| {
                                try t.append(new_var);
                            } else {
                                var al = try std.ArrayList(Ty).initCapacity(alloc, 1);
                                try al.append(new_var);
                                try to_unionize.put(ty.variable, al);
                            }
                        } else fresh_params[i] = ty;
                    }

                    const new_constraint = Constraint{
                        .solver = c.solver,
                        .params = fresh_params,
                        .monomorphize_unions = false,
                    };
                    try self.worklist.append(self.allocator, new_constraint);
                }
            } else { // We call this solver just once.
                const extra = solver.solve_fn(solver.self, self, c) catch |err| {
                    if (err == error.Unsat) {
                        std.debug.print("Solver {d} cannot be satisfied with {any}.\n", .{ c.solver, c.params });
                    }
                    return err; // Propagate.
                };
                try self.worklist.appendSlice(self.allocator, extra);
            }
        }

        var iter = to_unionize.iterator();
        while (iter.next()) |kv| {
            const new_union = try self.newUnion(kv.value_ptr.*.items);
            try self.unify(.{ .variable = kv.key_ptr.* }, new_union);
        }

        std.debug.print("Solver ran {d} times.\n", .{stats_called});

        for (self.entries.items) |*entry| {
            switch (entry.*) {
                .link => |id| entry.* = self.entries.items[id],
                .resolved => |ty| entry.* = self.newResolved(try self.normalize(ty)),
                .qualified, .unresolved => {},
            }
        }

        for (self.entries.items, 0..) |entry, i| {
            if (std.meta.activeTag(entry) != .qualified) {
                std.debug.print("Type variable ?T{d} remains unresolved\n", .{i});
                return error.UnsatisfiedConstraints;
            }
        }
    }

    pub fn dump(self: *Self) void {
        for (self.entries.items, 0..) |entry, i|
            std.debug.print("VAR {d} = {any}\n", .{ i, entry });
    }
};

fn allCombinations(items: []const Ty, allocator: std.mem.Allocator, temp_allocator: std.mem.Allocator) !std.ArrayList([]Ty) {
    var combos = std.ArrayList([]Ty).init(allocator);

    var indices = try temp_allocator.alloc(usize, items.len);
    defer temp_allocator.free(indices);
    for (indices) |*i| i.* = 0;

    while (true) {
        var buf = try allocator.alloc(Ty, items.len);
        for (items, 0..) |item, i|
            buf[i] = blk: switch (item) {
                .@"union" => |u| {
                    // Experimental implementation. To be optimized.
                    var iter = u.keyIterator();
                    for (0..indices[i]) |_| _ = iter.next();
                    break :blk iter.next().?.*;
                },
                else => break :blk item,
            };
        try combos.append(buf);

        var pos: isize = @intCast(items.len - 1);
        while (pos >= 0) : (pos -= 1) {
            const pos_u: usize = @intCast(pos);
            if (std.meta.activeTag(items[pos_u]) != .@"union") continue;
            const u = items[pos_u].@"union";
            if (u.size == 1) continue;

            indices[pos_u] += 1;
            if (indices[pos_u] < u.size)
                break;
            indices[pos_u] = 0;
        }

        if (pos < 0) break;
    }

    return combos;
}
