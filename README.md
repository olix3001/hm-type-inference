# What is this?
This library implements modular system for performing Hindley-Milner (HM) type inference.

## Goals and non-goals
This library aims to be very modular and handle all basic types. That is:
- concrete types (e.g. int, float, string),
- applicative types (e.g. `Array<?T>`),
- tuples,
- unions (types that may be one of [...]),
- dicts ([key] -> ?T)

Structures, enums, etc... can be treated like primitives or dicts, so there is no need to add them.
One of the goals is to provide generic interface for writing constraints, so that user can
implement constraints like `HasMethod`, `Addable`, and so on themselves.

## TODO:
- Solve constraints on unions. For example Addable(union{int, str}, int) -> ?T1 should return error after checking both possibilities separately.
- Implement missing cases for dicts.

## Resources
This project is based mainly on our past knowledge, but some other resources were also used during research:
- https://smallcultfollowing.com/babysteps/blog/2017/03/25/unification-in-chalk-part-1/
- https://smallcultfollowing.com/babysteps/blog/2017/04/23/unification-in-chalk-part-2/
