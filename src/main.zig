const std = @import("std");

const lib = @import("hm_type_inference_lib");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const alloc = gpa.allocator();
    defer std.debug.assert(gpa.deinit() == .ok);

    var cx = lib.SolverContext.init(alloc);
    defer cx.deinit();

    const vX = try cx.newTypeVar();
    const vY = try cx.newTypeVar();
    const vR = try cx.newTypeVar();

    const int = cx.newConcrete();
    const float = cx.newConcrete();
    const str = cx.newConcrete();

    try cx.unify(vX, int);

    const addable_c = try cx.registerSolver(&Addable{
        .combos = &.{
            .{ .a = int.concrete, .b = int.concrete, .r = int.concrete },
            .{ .a = float.concrete, .b = float.concrete, .r = float.concrete },
            .{ .a = str.concrete, .b = str.concrete, .r = str.concrete },
        },
    });
    try cx.addConstraint(.{
        .solver = addable_c,
        .params = &.{ vX, vY, vR },
    });

    try cx.solveAll();

    cx.dump();
}

// (lhs + rhs -> out)
const Addable = struct {
    combos: []const struct { a: usize, b: usize, r: usize },

    pub fn solve(self: *Addable, cx: *lib.SolverContext, c: lib.Constraint) anyerror![]const lib.Constraint {
        const p = c.params;
        if (p.len != 3) return error.Unsat;
        const lhs = p[0];
        const rhs = p[1];
        const out = p[2];

        for (self.combos) |row| {
            if (try matchType(cx, lhs, row.a) and try matchType(cx, rhs, row.b)) {
                try cx.unify(out, .{ .concrete = row.r });
                return &[_]lib.Constraint{};
            }
        }

        if (try cx.isOpen(lhs) or try cx.isOpen(rhs))
            return &[_]lib.Constraint{c}; // re-queue this.

        return error.Unsat;
    }

    fn matchType(cx: *lib.SolverContext, t: lib.Ty, wanted: lib.TypeId) !bool {
        const r = try cx.normalize(t);
        switch (r) {
            .concrete => |tid| return tid == wanted,
            .variable => |vid| {
                try cx.unify(.{ .variable = vid }, .{ .concrete = wanted });
                return true;
            },
            else => unreachable,
        }
    }
};
