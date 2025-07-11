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
    _ = vY;
    _ = vR;

    const int = cx.newConcrete();
    const float = cx.newConcrete();
    const str = cx.newConcrete();
    _ = float;
    _ = str;

    try cx.unify(vX, int);

    cx.dump();
}
