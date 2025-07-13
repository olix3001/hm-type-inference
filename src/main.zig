const std = @import("std");

const lib = @import("hm_type_inference_lib");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{
        .stack_trace_frames = 12,
    }){};
    const alloc = gpa.allocator();
    defer std.debug.assert(gpa.deinit() == .ok);

    var cx = lib.new.Context.init(alloc);
    defer cx.deinit();

    // Initialize primitive types.
    const int_t = try cx.newConcrete();
    const float_t = try cx.newConcrete();
    const str_t = try cx.newConcrete();

    // Initialize all variables.
    const TA = try cx.newTypeVar();
    const TB = try cx.newTypeVar();
    const TC = try cx.newTypeVar();

    const TX = try cx.newTypeVar();
    const TY = try cx.newTypeVar();

    // Play with them.
    const U = try cx.newUnion(&.{ int_t, str_t });

    const QT = try cx.newTuple(&.{ TA, int_t, float_t });
    const T = try cx.newTuple(&.{ TB, int_t, float_t });

    const QS = try cx.newApplicative(0, &.{QT});
    const S = try cx.newApplicative(0, &.{T});

    const QT2 = try cx.newTuple(&.{ str_t, QS });
    const T2 = try cx.newTuple(&.{ TC, S });

    try cx.unify(TX, QT2);
    try cx.unify(TY, T2);
    try cx.unify(TX, TY);

    const addable_c = try cx.registerSolver(&Addable{
        .combos = &.{
            .{ .a = int_t, .b = int_t, .r = int_t },
            .{ .a = float_t, .b = float_t, .r = float_t },
            .{ .a = str_t, .b = str_t, .r = str_t },

            .{ .a = str_t, .b = int_t, .r = str_t },
            .{ .a = str_t, .b = float_t, .r = str_t },
            .{ .a = float_t, .b = int_t, .r = float_t },
        },
    });

    try cx.addConstraint(.{
        .solver = addable_c,
        .params = &.{ U, int_t, TA },
    });

    cx.solveConstraints() catch |err| {
        cx.dump();
        return err;
    };

    cx.dump();
}

const Addable = struct {
    combos: []const struct { a: usize, b: usize, r: usize },

    pub fn solve(self: *Addable, cx: *lib.new.Context, c: lib.new.Constraint) anyerror![]const lib.new.Constraint {
        const p = c.params;

        if (p.len != 3) return error.Unsat;
        const lhs = p[0];
        const rhs = p[1];
        const out = p[2];

        for (self.combos) |row| {
            if (try matchType(cx, lhs, row.a) and try matchType(cx, rhs, row.b)) {
                try cx.unify(out, row.r);
                return &[_]lib.new.Constraint{};
            }
        }

        if (try cx.isOpen(lhs) or try cx.isOpen(rhs))
            return &[_]lib.new.Constraint{c}; // re-queue this.

        return error.Unsat;
    }

    fn matchType(cx: *lib.new.Context, t: lib.new.TypeId, wanted: usize) !bool {
        const r = try cx.normalize(t);
        switch (cx.types.items[r]) {
            .concrete => |tid| return tid == cx.types.items[wanted].concrete,
            .variable => |vid| {
                try cx.unify(try cx.findVariable(vid), wanted);
                return true;
            },
            else => unreachable,
        }
    }
};
