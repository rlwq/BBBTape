# BBBTape

[![Lean CI](https://github.com/rlwq/BBBTape/actions/workflows/ci.yml/badge.svg)](https://github.com/rlwq/BBBTape/actions/workflows/ci.yml)

Lean 4 formalisation and machine-checked proofs of Busy Beaver values for a binary tape machine with loops (`< > * [ ]`).

For the full write-up and explanation of the formalisation, Tree Normal Form search, and deciders, see the blog post: **[Busy Beaver for a binary tape machine](https://rlwq.github.io/blog/busy-beaver-binary-tape/)**.

## Verified values

| $n$ | Programs | $\mathrm{BB}(n)$ | Champion |
| ---: | ---: | ---: | --- |
| 1 | 3 | 1 | `<` |
| 2 | 10 | 2 | `<<` |
| 3 | 36 | 3 | `<<<` |
| 4 | 137 | 4 | `<<<<` |
| 5 | 543 | 5 | `<<<<<` |
| 6 | 2,219 | 8 | `*<*[>]` |
| 7 | 9,285 | 10 | `*<*[*>]` |
| 8 | 39,587 | 14 | `*[<*<*>]` |
| 9 | 171,369 | 18 | `*[[<]>>*]` |
| 10 | 751,236 | 30 | `*[<*[>]<<]` |
| 11 | 3,328,218 | 35 | `*[<*[>]*<<]` |
| 12 | 14,878,455 | 72 | `*[<*[>>*>]<]` |
| 13 | 67,030,785 | 120 | `*[<*<*[>*>]<]` |
| 14 | 304,036,170 | 158 | `*[<<*[>>>*>]<]` |
| 15 | 1,388,524,782 | 276 | `*[[<*[>>>]<]<<]` |
| 16 | 6,373,537,154 | 352 | `*[<<*[[>>>]*>]<]` |

## Structure

- `BBBTape/Core/` — language AST, tape interface, operational semantics, Busy Beaver statement, refinement, decider/expander interfaces, and TNF search
- `BBBTape/Tapes/` — concrete tape implementations (`Spec`, `Zipper`, `WordTape`)
- `BBBTape/Deciders/` — sound deciders (`Simulator`, `Windows`, `Translated`, `Blocks`) and decider chains (`Ξ₁`, `Ξ₂`, `Ξ₃`, `Ξ₄`)
- `BBBTape/Expanders/` — Tree Normal Form expander (`TNF` / `Φ₁`)
- `BBBTape/Macro/` — `bf"..."` syntax macro
- `BBBTape/Results/` — proved theorems `bb0` through `bb16`

## Verify locally

Requires [elan](https://github.com/leanprover/elan) (toolchain is pinned in `lean-toolchain`):

```sh
lake build
```
