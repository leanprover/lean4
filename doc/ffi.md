# Foreign Function Interface

NOTE: The current interface was designed for internal use in Lean and should be considered **unstable**.
It will be refined and extended in the future.

As Lean is written partially in Lean itself and partially in C++, it offers efficient interoperability between the two languages (or rather, between Lean and any language supporting C interfaces).
This support is however currently limited to transferring Lean data types; in particular, it is not possible yet to pass or return compound data structures such as C `struct`s by value from or to Lean.

There are two primary attributes for interoperating with other languages:
* `@[extern "sym"] constant leanSym : ...` binds a Lean declaration to the external symbol `sym`.
  It can also be used with `def` to provide an internal definition, but ensuring consistency of both definitions is up to the user.
* `@[export sym] def leanSym : ...` exports `leanSym` under the unmangled symbol name `sym`.

## The Lean ABI

The Lean Application Binary Interface (ABI) describes how the signature of a Lean declaration is encoded as a native calling convention.
It is based on the standard C ABI and calling convention of the target platform.
For a Lean declaration marked with either `@[extern "sym"]` or `@[export sym]` for some symbol name `sym`, let `α₁ → ... → αₙ → β` be the normalized declaration's type.
If `n` is 0, the corresponding C declaration is
```c
extern s sym;
```
where `s` is the C translation of `β` as specified in the next section.
In the case of an `@[extern]` definition, the symbol's value is guaranteed to be initialized only after calling the Lean module's initializer or that of an importing module; see [Initialization](.#init).

If `n` is greater than 0, the corresponding C declaration is
```c
s sym(t₁, ..., tₘ);
```
where the parameter types `tᵢ` are the C translation of the `αᵢ` as in the next section.
In the case of `@[extern]` all *irrelevant* types are removed first; see next section.

### Translating Types from Lean to C

* The integer types `UInt8`, ..., `UInt64`, `USize` are represented by the C types `uint8_t`, ..., `uint64_t`, `usize_t`, respectively
* `Char` is represented by `uint32_t`
* `Float` is represented by `double`
* An *enum* inductive type of at least 2 and at most 2^32 constructors, each of which with no parameters, is represented by the first type of `uint8_t`, `uint16_t`, `uint32_t` that is sufficient to represent all constructor indices.

  For example, the type `Bool` is represented as `uint8_t` with values `0` for `false` and `1` for `true`.
* `Decidable α` is represented the same way as `Bool`
* An inductive type with a *trivial structure*, that is,
  * it is none of the types described above
  * it is not marked `unsafe`
  * it has a single constructor with a single parameter of *relevant* type
  is represented by the representation of that parameter's type.
  
  For example, `{ x : α // p }`, the `Subtype` structure of a value of type `α` and an irrelevant proof, is represented by the representation of `α`.
* `Nat` is represented by `lean_object *`.
  Its runtime value is either a pointer to an opaque bignum object or, if the lowest bit of the "pointer" is 1 (`lean_is_scalar`), an encoded unboxed natural number (`lean_box`/`lean_unbox`).
* A universe `Sort u`, type constructor `... → Sort u`, or proposition `p : Prop` is *irrelevant* and is either statically erased (see above) or represented as a `lean_object *` with the runtime value `lean_box(0)`
* Any other type is represented by `lean_object *`.
  Its runtime value is a pointer to an object of a subtype of `lean_object` (see respective declarations in `lean.h`) or the unboxed value `lean_box(cidx)` for the `cidx`th constructor of an inductive type if this constructor does not have any relevant parameters.

  Example: the runtime value of `u : Unit` is always `lean_box(0)`.

### Borrowing

By default, all `lean_object *` parameters of an `@[extern]` function are considered *owned*, i.e. the external code is passed a "virtual RC token" and is responsible for passing this token along to another consuming function (exactly once) or freeing it via `lean_dec`.
To reduce reference counting overhead, parameters can be marked as *borrowed* by prefixing their type with `@&`.
Borrowed objects must only be passed to other non-consuming functions (arbitrarily often) or converted to owned values using `lean_inc`.
In `lean.h`, the `lean_object *` aliases `lean_obj_arg` and `b_lean_obj_arg` are used to mark this difference on the C side.

Return values and `@[export]` parameters are always owned at the moment.

## Initialization

When including Lean code as part of a larger program, modules must be *initialized* before accessing any of their declarations.
The initializer for module `A.B` is called `initialize_A_B` and will automatically initialize any imported modules.
Module initializers are idempotent, but not thread-safe.
Together with initialization of the Lean runtime, you should execute code like the following exactly once before accessing any Lean declarations:
```c
void lean_initialize_runtime_module();
void lean_initialize();
lean_object * initialize_A_B(lean_object *);
lean_object * initialize_C(lean_object *);
...

lean_initialize_runtime_module();
//lean_initialize();  // necessary if you (indirectly) access the `Lean` package

lean_object * res;
res = initialize_A_B(lean_io_mk_world());
if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
} else {
    lean_io_result_show_error(res);
    lean_dec(res);
    return ...; // do not access Lean declarations if initialization failed
}
res = initialize_C(lean_io_mk_world());
if (lean_io_result_is_ok(res)) {
...

//lean_init_task_manager(); // necessary if you (indirectly) use `Task`
lean_io_mark_end_initialization();
```
