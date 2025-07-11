const std = @import("std");

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
                for (u.keyIterator().items, 0..u.size) |ty, i| {
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

pub const SolverContext = struct {
    arena: std.heap.ArenaAllocator,
    allocator: std.mem.Allocator,
    entries: std.ArrayListUnmanaged(Entry) = .{},
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
        self.entries.deinit(self.allocator);
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
            .types = try self.arena.allocator().dupe(params),
        } };
    }
    pub fn newTuple(self: *Self, elements: []const Ty) !Ty {
        return .{ .tuple = try self.arena.allocator().dupe(elements) };
    }
    pub fn newUnion(self: *Self, types: []const Ty) !Ty {
        var u = DeepHashMapUnmanaged(Ty, void){};
        const alloc = self.arena.allocator();
        for (types) |ty|
            try u.put(alloc, ty, void{});
        return .{ .@"union" = u };
    }
    // TODO: newDict.

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
                for (u.keyIterator().items[0..u.size]) |key| {
                    const norm = try self.normalize(key);
                    try sub.put(alloc, norm, void{});
                }
                return .{ .@"union" = sub };
            },
            .dict => |dict| {
                for (dict.valueIterator().items[0..dict.size]) |*item| {
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
                for (u.keyIterator().items[0..u.size]) |typ| {
                    if (!self.isFullyQualified(typ)) return false;
                }
                return true;
            },
            .dict => |dict| {
                for (dict.valueIterator().items[0..dict.size]) |typ| {
                    if (!self.isFullyQualified(typ)) return false;
                }
                return true;
            },
        }
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

            .tuple => |tup_a| switch (nb) {
                .variable => |vb| self.entries.items[vb] = self.newResolved(nb),
                .tuple => |tup_b| {
                    if (tup_a.len != tup_b.len) return error.TypeArityMismatch;

                    for (tup_a, tup_b) |a_ty, b_ty|
                        try self.unify(a_ty, b_ty);
                },
                else => return error.TypeMismatch,
            },

            .@"union" => |*ua| switch (nb) {
                .variable => |vb| self.entries.items[vb] = self.newResolved(nb),
                .@"union" => |*ub| {
                    if (ua.size != ub.size) return error.TypeArityMismatch;

                    // Unifying unions does not resolve anything.
                    // This must be done via constraints.

                    // Experimental implementation. May need refactoring.
                    const alloc = self.arena.allocator();
                    for (ub.keyIterator().items[0..ub.size]) |b_item|
                        try ua.put(alloc, b_item, void{});
                    ub.clearRetainingCapacity();
                    for (ua.keyIterator().items[0..ua.size]) |a_item|
                        try ub.put(alloc, a_item, void{});
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
                        } else {
                            return error.DictKeyMismatch;
                        }
                    }
                },
                else => return error.TypeMismatch,
            },
        }
    }

    pub fn dump(self: *Self) void {
        for (self.entries.items, 0..) |entry, i|
            std.debug.print("VAR {d} = {any}\n", .{ i, entry });
    }
};
