// Lean compiler output
// Module: Lean.Fmt.FmtM.Layouts
// Imports: public import Lean.Fmt.FmtM.Primitives import Init.Data import Init.While import Std.Data.Iterators.Producers.Range import Std.Data.Iterators.Combinators.StepSize
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_space;
extern lean_object* l_Lean_Fmt_TaggedDoc_softSpace;
extern lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
extern lean_object* l_Lean_Fmt_TaggedDoc_nl;
lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_break;
lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_joinUsing(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillWith(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object*);
extern lean_object* l_Lean_Fmt_multiLineRawTagId;
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(uint8_t, uint8_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isBracketed(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(lean_object*);
lean_object* l_Lean_Fmt_Doc_hardNl___redArg();
uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object*);
lean_object* l_Array_popWhile___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_empty___redArg();
lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnHeight(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_array___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_array___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_lines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_lines___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_lines___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines___boxed(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedLines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value),((lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_sepArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_sepLines___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepLines___closed__0;
static lean_once_cell_t l_Lean_Fmt_Layouts_sepLines___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepLines___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_sepFill___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_sepFill___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_sepFill___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1;
static lean_once_cell_t l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_retainedWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_retainedWhitespace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Layouts_retainedWhitespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_retainedWhitespace___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_retainedWhitespace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_isAligned___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_isAligned___redArg___closed__0;
static lean_once_cell_t l_Lean_Fmt_Layouts_isAligned___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_isAligned___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_isAligned___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_isAligned(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_isAligned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0;
static lean_once_cell_t l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1;
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_permitDenseLayout(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_permitDenseLayout___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__0;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__1_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_nested, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__1_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Layouts"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "infixOperator"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__4_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "compactFirstOperationAssertion"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__5 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__5_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 54, 146, 101, 77, 208, 96, 214)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__4_value),LEAN_SCALAR_PTR_LITERAL(245, 49, 203, 135, 141, 45, 148, 127)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__5_value),LEAN_SCALAR_PTR_LITERAL(186, 171, 99, 10, 123, 142, 237, 98)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__7_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_infixOperator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Layouts_infixOperator___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_infixOperator___closed__0_value;
static const lean_array_object l_Lean_Fmt_Layouts_infixOperator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Layouts_infixOperator___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_infixOperator___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_bracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Layouts_bracketed___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_bracketed___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_parens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_parens___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_parens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_alts___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_alts___closed__0;
static lean_once_cell_t l_Lean_Fmt_Layouts_alts___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_alts___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_sepFill___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_sepFill___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_Layouts_metaApplication___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_Layouts_metaApplication___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_metaApplication___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_pipeOperator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_pipeOperator___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_pipeOperator___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_instInhabitedBlock;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0(lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock = (const lean_object*)&l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_blocks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_blocks___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_blocks___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_tuple___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_tuple___closed__0;
static const lean_ctor_object l_Lean_Fmt_Layouts_tuple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_tuple___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_tuple___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_localSignature___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_localSignature___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_Layouts_localSignature___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_localSignature___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Layouts_localSignature___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_localSignature___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_localSignature___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_globalSignature___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_globalSignature___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_globalSignature___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_globalSignature___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_whereDeclaration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_whereDeclaration___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_whereDeclaration___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_binder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_fill___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_binder___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_binder___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_letDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_letDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_letDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_quantified(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_subtype___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_subtype___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_subtype___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_subtype(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_conditional___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_conditional___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_conditional___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_strLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 3)
{
uint8_t v_allowFlattening_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_allowFlattening_7_ = lean_ctor_get_uint8(v_t_5_, 0);
v___x_8_ = lean_box(v_allowFlattening_7_);
v___x_9_ = lean_apply_1(v_k_6_, v___x_8_);
return v___x_9_;
}
else
{
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg___boxed(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_10_, v_k_11_);
lean_dec(v_t_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_t_21_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(lean_object* v_t_25_, lean_object* v_join_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_25_, v_join_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg___boxed(lean_object* v_t_28_, lean_object* v_join_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(v_t_28_, v_join_29_);
lean_dec(v_t_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_join_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_32_, v_join_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_join_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(v_motive_36_, v_t_37_, v_h_38_, v_join_39_);
lean_dec(v_t_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(lean_object* v_t_41_, lean_object* v_joinUsingSpace_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_41_, v_joinUsingSpace_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg___boxed(lean_object* v_t_44_, lean_object* v_joinUsingSpace_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(v_t_44_, v_joinUsingSpace_45_);
lean_dec(v_t_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_joinUsingSpace_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_48_, v_joinUsingSpace_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___boxed(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_joinUsingSpace_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(v_motive_52_, v_t_53_, v_h_54_, v_joinUsingSpace_55_);
lean_dec(v_t_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg(lean_object* v_t_57_, lean_object* v_joinUsingSoftSpace_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_57_, v_joinUsingSoftSpace_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg___boxed(lean_object* v_t_60_, lean_object* v_joinUsingSoftSpace_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg(v_t_60_, v_joinUsingSoftSpace_61_);
lean_dec(v_t_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_joinUsingSoftSpace_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_64_, v_joinUsingSoftSpace_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_joinUsingSoftSpace_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim(v_motive_68_, v_t_69_, v_h_70_, v_joinUsingSoftSpace_71_);
lean_dec(v_t_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(lean_object* v_t_73_, lean_object* v_joinUsingNl_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_73_, v_joinUsingNl_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg___boxed(lean_object* v_t_76_, lean_object* v_joinUsingNl_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(v_t_76_, v_joinUsingNl_77_);
lean_dec(v_t_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(lean_object* v_motive_79_, lean_object* v_t_80_, lean_object* v_h_81_, lean_object* v_joinUsingNl_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_80_, v_joinUsingNl_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___boxed(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_joinUsingNl_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(v_motive_84_, v_t_85_, v_h_86_, v_joinUsingNl_87_);
lean_dec(v_t_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(lean_object* v_t_89_, lean_object* v_joinUsingBreak_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_89_, v_joinUsingBreak_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg___boxed(lean_object* v_t_92_, lean_object* v_joinUsingBreak_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(v_t_92_, v_joinUsingBreak_93_);
lean_dec(v_t_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(lean_object* v_motive_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_joinUsingBreak_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_96_, v_joinUsingBreak_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___boxed(lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_joinUsingBreak_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(v_motive_100_, v_t_101_, v_h_102_, v_joinUsingBreak_103_);
lean_dec(v_t_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(lean_object* v_t_105_, lean_object* v_fill_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_105_, v_fill_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg___boxed(lean_object* v_t_108_, lean_object* v_fill_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(v_t_108_, v_fill_109_);
lean_dec(v_t_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(lean_object* v_motive_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_fill_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_112_, v_fill_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___boxed(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_fill_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(v_motive_116_, v_t_117_, v_h_118_, v_fill_119_);
lean_dec(v_t_117_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(lean_object* v___y_121_){
_start:
{
lean_inc_ref(v___y_121_);
return v___y_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0___boxed(lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(v___y_122_);
lean_dec_ref(v___y_122_);
return v_res_123_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1(void){
_start:
{
lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___f_125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_126_ = l_Lean_Fmt_TaggedDoc_space;
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___f_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(size_t v_sz_128_, size_t v_i_129_, lean_object* v_bs_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = lean_usize_dec_lt(v_i_129_, v_sz_128_);
if (v___x_131_ == 0)
{
return v_bs_130_;
}
else
{
lean_object* v_v_132_; lean_object* v___x_133_; lean_object* v_bs_x27_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; size_t v___x_138_; size_t v___x_139_; lean_object* v___x_140_; 
v_v_132_ = lean_array_uget(v_bs_130_, v_i_129_);
v___x_133_ = lean_unsigned_to_nat(0u);
v_bs_x27_134_ = lean_array_uset(v_bs_130_, v_i_129_, v___x_133_);
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v_v_132_);
v___x_136_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_137_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_135_, v___x_136_);
v___x_138_ = ((size_t)1ULL);
v___x_139_ = lean_usize_add(v_i_129_, v___x_138_);
v___x_140_ = lean_array_uset(v_bs_x27_134_, v_i_129_, v___x_137_);
v_i_129_ = v___x_139_;
v_bs_130_ = v___x_140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___boxed(lean_object* v_sz_142_, lean_object* v_i_143_, lean_object* v_bs_144_){
_start:
{
size_t v_sz_boxed_145_; size_t v_i_boxed_146_; lean_object* v_res_147_; 
v_sz_boxed_145_ = lean_unbox_usize(v_sz_142_);
lean_dec(v_sz_142_);
v_i_boxed_146_ = lean_unbox_usize(v_i_143_);
lean_dec(v_i_143_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(v_sz_boxed_145_, v_i_boxed_146_, v_bs_144_);
return v_res_147_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0(void){
_start:
{
lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___f_148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_149_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___f_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(size_t v_sz_151_, size_t v_i_152_, lean_object* v_bs_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_usize_dec_lt(v_i_152_, v_sz_151_);
if (v___x_154_ == 0)
{
return v_bs_153_;
}
else
{
lean_object* v_v_155_; lean_object* v___x_156_; lean_object* v_bs_x27_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; 
v_v_155_ = lean_array_uget(v_bs_153_, v_i_152_);
v___x_156_ = lean_unsigned_to_nat(0u);
v_bs_x27_157_ = lean_array_uset(v_bs_153_, v_i_152_, v___x_156_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v_v_155_);
v___x_159_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0);
v___x_160_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_158_, v___x_159_);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_usize_add(v_i_152_, v___x_161_);
v___x_163_ = lean_array_uset(v_bs_x27_157_, v_i_152_, v___x_160_);
v_i_152_ = v___x_162_;
v_bs_153_ = v___x_163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___boxed(lean_object* v_sz_165_, lean_object* v_i_166_, lean_object* v_bs_167_){
_start:
{
size_t v_sz_boxed_168_; size_t v_i_boxed_169_; lean_object* v_res_170_; 
v_sz_boxed_168_ = lean_unbox_usize(v_sz_165_);
lean_dec(v_sz_165_);
v_i_boxed_169_ = lean_unbox_usize(v_i_166_);
lean_dec(v_i_166_);
v_res_170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(v_sz_boxed_168_, v_i_boxed_169_, v_bs_167_);
return v_res_170_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0(void){
_start:
{
lean_object* v___f_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___f_171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_172_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___f_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(size_t v_sz_174_, size_t v_i_175_, lean_object* v_bs_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = lean_usize_dec_lt(v_i_175_, v_sz_174_);
if (v___x_177_ == 0)
{
return v_bs_176_;
}
else
{
lean_object* v_v_178_; lean_object* v___x_179_; lean_object* v_bs_x27_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; size_t v___x_184_; size_t v___x_185_; lean_object* v___x_186_; 
v_v_178_ = lean_array_uget(v_bs_176_, v_i_175_);
v___x_179_ = lean_unsigned_to_nat(0u);
v_bs_x27_180_ = lean_array_uset(v_bs_176_, v_i_175_, v___x_179_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_v_178_);
v___x_182_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0);
v___x_183_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_181_, v___x_182_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_add(v_i_175_, v___x_184_);
v___x_186_ = lean_array_uset(v_bs_x27_180_, v_i_175_, v___x_183_);
v_i_175_ = v___x_185_;
v_bs_176_ = v___x_186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___boxed(lean_object* v_sz_188_, lean_object* v_i_189_, lean_object* v_bs_190_){
_start:
{
size_t v_sz_boxed_191_; size_t v_i_boxed_192_; lean_object* v_res_193_; 
v_sz_boxed_191_ = lean_unbox_usize(v_sz_188_);
lean_dec(v_sz_188_);
v_i_boxed_192_ = lean_unbox_usize(v_i_189_);
lean_dec(v_i_189_);
v_res_193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(v_sz_boxed_191_, v_i_boxed_192_, v_bs_190_);
return v_res_193_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0(void){
_start:
{
lean_object* v___f_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___f_194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_195_ = l_Lean_Fmt_TaggedDoc_break;
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___f_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(size_t v_sz_197_, size_t v_i_198_, lean_object* v_bs_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = lean_usize_dec_lt(v_i_198_, v_sz_197_);
if (v___x_200_ == 0)
{
return v_bs_199_;
}
else
{
lean_object* v_v_201_; lean_object* v___x_202_; lean_object* v_bs_x27_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; 
v_v_201_ = lean_array_uget(v_bs_199_, v_i_198_);
v___x_202_ = lean_unsigned_to_nat(0u);
v_bs_x27_203_ = lean_array_uset(v_bs_199_, v_i_198_, v___x_202_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v_v_201_);
v___x_205_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0);
v___x_206_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_204_, v___x_205_);
v___x_207_ = ((size_t)1ULL);
v___x_208_ = lean_usize_add(v_i_198_, v___x_207_);
v___x_209_ = lean_array_uset(v_bs_x27_203_, v_i_198_, v___x_206_);
v_i_198_ = v___x_208_;
v_bs_199_ = v___x_209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___boxed(lean_object* v_sz_211_, lean_object* v_i_212_, lean_object* v_bs_213_){
_start:
{
size_t v_sz_boxed_214_; size_t v_i_boxed_215_; lean_object* v_res_216_; 
v_sz_boxed_214_ = lean_unbox_usize(v_sz_211_);
lean_dec(v_sz_211_);
v_i_boxed_215_ = lean_unbox_usize(v_i_212_);
lean_dec(v_i_212_);
v_res_216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(v_sz_boxed_214_, v_i_boxed_215_, v_bs_213_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(lean_object* v_as_217_, size_t v_i_218_, size_t v_stop_219_, lean_object* v_b_220_){
_start:
{
lean_object* v___y_222_; uint8_t v___x_226_; 
v___x_226_ = lean_usize_dec_eq(v_i_218_, v_stop_219_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = lean_array_uget_borrowed(v_as_217_, v_i_218_);
v___x_228_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
lean_inc(v___x_227_);
v___x_229_ = lean_array_push(v_b_220_, v___x_227_);
v___y_222_ = v___x_229_;
goto v___jp_221_;
}
else
{
v___y_222_ = v_b_220_;
goto v___jp_221_;
}
}
else
{
return v_b_220_;
}
v___jp_221_:
{
size_t v___x_223_; size_t v___x_224_; 
v___x_223_ = ((size_t)1ULL);
v___x_224_ = lean_usize_add(v_i_218_, v___x_223_);
v_i_218_ = v___x_224_;
v_b_220_ = v___y_222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6___boxed(lean_object* v_as_230_, lean_object* v_i_231_, lean_object* v_stop_232_, lean_object* v_b_233_){
_start:
{
size_t v_i_boxed_234_; size_t v_stop_boxed_235_; lean_object* v_res_236_; 
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_stop_boxed_235_ = lean_unbox_usize(v_stop_232_);
lean_dec(v_stop_232_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_as_230_, v_i_boxed_234_, v_stop_boxed_235_, v_b_233_);
lean_dec_ref(v_as_230_);
return v_res_236_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0(void){
_start:
{
lean_object* v___f_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___f_237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_238_ = l_Lean_Fmt_TaggedDoc_softSpace;
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___f_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(size_t v_sz_240_, size_t v_i_241_, lean_object* v_bs_242_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = lean_usize_dec_lt(v_i_241_, v_sz_240_);
if (v___x_243_ == 0)
{
return v_bs_242_;
}
else
{
lean_object* v_v_244_; lean_object* v___x_245_; lean_object* v_bs_x27_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; 
v_v_244_ = lean_array_uget(v_bs_242_, v_i_241_);
v___x_245_ = lean_unsigned_to_nat(0u);
v_bs_x27_246_ = lean_array_uset(v_bs_242_, v_i_241_, v___x_245_);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_v_244_);
v___x_248_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0);
v___x_249_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_247_, v___x_248_);
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_add(v_i_241_, v___x_250_);
v___x_252_ = lean_array_uset(v_bs_x27_246_, v_i_241_, v___x_249_);
v_i_241_ = v___x_251_;
v_bs_242_ = v___x_252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___boxed(lean_object* v_sz_254_, lean_object* v_i_255_, lean_object* v_bs_256_){
_start:
{
size_t v_sz_boxed_257_; size_t v_i_boxed_258_; lean_object* v_res_259_; 
v_sz_boxed_257_ = lean_unbox_usize(v_sz_254_);
lean_dec(v_sz_254_);
v_i_boxed_258_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_res_259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(v_sz_boxed_257_, v_i_boxed_258_, v_bs_256_);
return v_res_259_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0(void){
_start:
{
lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___f_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_261_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___f_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(size_t v_sz_263_, size_t v_i_264_, lean_object* v_bs_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_lt(v_i_264_, v_sz_263_);
if (v___x_266_ == 0)
{
return v_bs_265_;
}
else
{
lean_object* v_v_267_; lean_object* v___x_268_; lean_object* v_bs_x27_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; size_t v___x_273_; size_t v___x_274_; lean_object* v___x_275_; 
v_v_267_ = lean_array_uget(v_bs_265_, v_i_264_);
v___x_268_ = lean_unsigned_to_nat(0u);
v_bs_x27_269_ = lean_array_uset(v_bs_265_, v_i_264_, v___x_268_);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v_v_267_);
v___x_271_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_272_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_270_, v___x_271_);
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_add(v_i_264_, v___x_273_);
v___x_275_ = lean_array_uset(v_bs_x27_269_, v_i_264_, v___x_272_);
v_i_264_ = v___x_274_;
v_bs_265_ = v___x_275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___boxed(lean_object* v_sz_277_, lean_object* v_i_278_, lean_object* v_bs_279_){
_start:
{
size_t v_sz_boxed_280_; size_t v_i_boxed_281_; lean_object* v_res_282_; 
v_sz_boxed_280_ = lean_unbox_usize(v_sz_277_);
lean_dec(v_sz_277_);
v_i_boxed_281_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_boxed_280_, v_i_boxed_281_, v_bs_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array(lean_object* v_array_285_, lean_object* v_format_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___y_290_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_287_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_array_get_size(v_array_285_);
v___x_326_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_327_ = lean_nat_dec_lt(v___x_288_, v___x_325_);
if (v___x_327_ == 0)
{
v___y_290_ = v___x_326_;
goto v___jp_289_;
}
else
{
size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
v___x_328_ = ((size_t)0ULL);
v___x_329_ = lean_usize_of_nat(v___x_325_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_array_285_, v___x_328_, v___x_329_, v___x_326_);
v___y_290_ = v___x_330_;
goto v___jp_289_;
}
v___jp_289_:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_array_get_size(v___y_290_);
v___x_292_ = lean_nat_dec_eq(v___x_291_, v___x_288_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_dec_eq(v___x_291_, v___x_293_);
if (v___x_294_ == 0)
{
switch(lean_obj_tag(v_format_286_))
{
case 0:
{
size_t v_sz_295_; size_t v___x_296_; lean_object* v_terms_297_; lean_object* v___x_298_; 
v_sz_295_ = lean_array_size(v___y_290_);
v___x_296_ = ((size_t)0ULL);
v_terms_297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(v_sz_295_, v___x_296_, v___y_290_);
v___x_298_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_297_);
lean_dec_ref(v_terms_297_);
return v___x_298_;
}
case 1:
{
size_t v_sz_299_; size_t v___x_300_; lean_object* v_terms_301_; lean_object* v___x_302_; 
v_sz_299_ = lean_array_size(v___y_290_);
v___x_300_ = ((size_t)0ULL);
v_terms_301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(v_sz_299_, v___x_300_, v___y_290_);
v___x_302_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_301_);
lean_dec_ref(v_terms_301_);
return v___x_302_;
}
case 2:
{
size_t v_sz_303_; size_t v___x_304_; lean_object* v_terms_305_; lean_object* v___x_306_; 
v_sz_303_ = lean_array_size(v___y_290_);
v___x_304_ = ((size_t)0ULL);
v_terms_305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(v_sz_303_, v___x_304_, v___y_290_);
v___x_306_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_305_);
lean_dec_ref(v_terms_305_);
return v___x_306_;
}
case 3:
{
uint8_t v_allowFlattening_307_; 
v_allowFlattening_307_ = lean_ctor_get_uint8(v_format_286_, 0);
if (v_allowFlattening_307_ == 0)
{
size_t v_sz_308_; size_t v___x_309_; lean_object* v_terms_310_; lean_object* v___x_311_; 
v_sz_308_ = lean_array_size(v___y_290_);
v___x_309_ = ((size_t)0ULL);
v_terms_310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(v_sz_308_, v___x_309_, v___y_290_);
v___x_311_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_310_);
lean_dec_ref(v_terms_310_);
return v___x_311_;
}
else
{
size_t v_sz_312_; size_t v___x_313_; lean_object* v_terms_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_sz_312_ = lean_array_size(v___y_290_);
v___x_313_ = ((size_t)0ULL);
v_terms_314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_312_, v___x_313_, v___y_290_);
v___x_315_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_314_);
lean_dec_ref(v_terms_314_);
v___x_316_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_315_);
return v___x_316_;
}
}
case 4:
{
size_t v_sz_317_; size_t v___x_318_; lean_object* v_terms_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_sz_317_ = lean_array_size(v___y_290_);
v___x_318_ = ((size_t)0ULL);
v_terms_319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(v_sz_317_, v___x_318_, v___y_290_);
v___x_320_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_319_);
lean_dec_ref(v_terms_319_);
v___x_321_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_320_);
return v___x_321_;
}
default: 
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___y_290_);
return v___x_322_;
}
}
}
else
{
lean_object* v___x_323_; 
v___x_323_ = lean_array_get(v___x_287_, v___y_290_, v___x_288_);
lean_dec_ref(v___y_290_);
return v___x_323_;
}
}
else
{
lean_object* v___x_324_; 
lean_dec_ref(v___y_290_);
v___x_324_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array___boxed(lean_object* v_array_331_, lean_object* v_format_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Fmt_Layouts_array(v_array_331_, v_format_332_);
lean_dec(v_format_332_);
lean_dec_ref(v_array_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines(lean_object* v_lines_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l_Lean_Fmt_Layouts_lines___closed__0));
v___x_338_ = l_Lean_Fmt_Layouts_array(v_lines_336_, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines___boxed(lean_object* v_lines_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Fmt_Layouts_lines(v_lines_339_);
lean_dec_ref(v_lines_339_);
return v_res_340_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_342_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(size_t v_sz_343_, size_t v_i_344_, lean_object* v_bs_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_usize_dec_lt(v_i_344_, v_sz_343_);
if (v___x_346_ == 0)
{
return v_bs_345_;
}
else
{
lean_object* v___f_347_; lean_object* v_v_348_; lean_object* v___x_349_; lean_object* v_bs_x27_350_; lean_object* v___x_351_; lean_object* v___y_353_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___f_347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v_v_348_ = lean_array_uget(v_bs_345_, v_i_344_);
v___x_349_ = lean_unsigned_to_nat(0u);
v_bs_x27_350_ = lean_array_uset(v_bs_345_, v_i_344_, v___x_349_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_v_348_);
v___x_360_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_361_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0);
if (v___x_361_ == 0)
{
lean_object* v_doc_362_; uint8_t v___x_363_; 
v_doc_362_ = lean_ctor_get(v___x_360_, 0);
v___x_363_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_inc_n(v_doc_362_, 2);
v___x_364_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_362_, v_doc_362_);
v___x_365_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_364_);
v___y_353_ = v___x_365_;
goto v___jp_352_;
}
else
{
lean_object* v___x_366_; 
lean_inc(v_doc_362_);
v___x_366_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_362_);
v___y_353_ = v___x_366_;
goto v___jp_352_;
}
}
else
{
v___y_353_ = v___x_360_;
goto v___jp_352_;
}
v___jp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___y_353_);
lean_ctor_set(v___x_354_, 1, v___f_347_);
v___x_355_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_351_, v___x_354_);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_344_, v___x_356_);
v___x_358_ = lean_array_uset(v_bs_x27_350_, v_i_344_, v___x_355_);
v_i_344_ = v___x_357_;
v_bs_345_ = v___x_358_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___boxed(lean_object* v_sz_367_, lean_object* v_i_368_, lean_object* v_bs_369_){
_start:
{
size_t v_sz_boxed_370_; size_t v_i_boxed_371_; lean_object* v_res_372_; 
v_sz_boxed_370_ = lean_unbox_usize(v_sz_367_);
lean_dec(v_sz_367_);
v_i_boxed_371_ = lean_unbox_usize(v_i_368_);
lean_dec(v_i_368_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(v_sz_boxed_370_, v_i_boxed_371_, v_bs_369_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedLines(lean_object* v_lines_373_){
_start:
{
size_t v_sz_374_; size_t v___x_375_; lean_object* v_lines_376_; lean_object* v___x_377_; 
v_sz_374_ = lean_array_size(v_lines_373_);
v___x_375_ = ((size_t)0ULL);
v_lines_376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(v_sz_374_, v___x_375_, v_lines_373_);
v___x_377_ = l_Lean_Fmt_TaggedDoc_combine(v_lines_376_);
lean_dec_ref(v_lines_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic(lean_object* v_terms_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_box(0);
v___x_380_ = l_Lean_Fmt_Layouts_array(v_terms_378_, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic___boxed(lean_object* v_terms_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Fmt_Layouts_atomic(v_terms_381_);
lean_dec_ref(v_terms_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object* v_terms_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___y_387_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_384_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_array_get_size(v_terms_383_);
v___x_395_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_396_ = lean_nat_dec_lt(v___x_385_, v___x_394_);
if (v___x_396_ == 0)
{
v___y_387_ = v___x_395_;
goto v___jp_386_;
}
else
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_394_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_terms_383_, v___x_397_, v___x_398_, v___x_395_);
v___y_387_ = v___x_399_;
goto v___jp_386_;
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_388_ = lean_array_get_size(v___y_387_);
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_dec_eq(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_Lean_Fmt_Layouts_atomic(v___y_387_);
lean_dec_ref(v___y_387_);
v___x_392_ = l_Lean_Fmt_TaggedDoc_nested(v___x_391_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = lean_array_get(v___x_384_, v___y_387_, v___x_385_);
lean_dec_ref(v___y_387_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator___boxed(lean_object* v_terms_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Fmt_Layouts_atomicInfixOperator(v_terms_400_);
lean_dec_ref(v_terms_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object* v_terms_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_box(1);
v___x_404_ = l_Lean_Fmt_Layouts_array(v_terms_402_, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic___boxed(lean_object* v_terms_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Fmt_Layouts_spacedAtomic(v_terms_405_);
lean_dec_ref(v_terms_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object* v_terms_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_box(2);
v___x_409_ = l_Lean_Fmt_Layouts_array(v_terms_407_, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic___boxed(lean_object* v_terms_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v_terms_410_);
lean_dec_ref(v_terms_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill(lean_object* v_terms_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_box(5);
v___x_414_ = l_Lean_Fmt_Layouts_array(v_terms_412_, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill___boxed(lean_object* v_terms_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Fmt_Layouts_fill(v_terms_415_);
lean_dec_ref(v_terms_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object* v_terms_417_, uint8_t v_spacing_418_){
_start:
{
if (v_spacing_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_box(4);
v___x_420_ = l_Lean_Fmt_Layouts_array(v_terms_417_, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_alloc_ctor(3, 0, 1);
lean_ctor_set_uint8(v___x_421_, 0, v_spacing_418_);
v___x_422_ = l_Lean_Fmt_Layouts_array(v_terms_417_, v___x_421_);
lean_dec_ref_known(v___x_421_, 0);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical___boxed(lean_object* v_terms_423_, lean_object* v_spacing_424_){
_start:
{
uint8_t v_spacing_boxed_425_; lean_object* v_res_426_; 
v_spacing_boxed_425_ = lean_unbox(v_spacing_424_);
v_res_426_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_423_, v_spacing_boxed_425_);
lean_dec_ref(v_terms_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___impl(uint8_t v_x_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_box(v_x_427_);
v___x_429_ = lean_obj_tag_nat(v___x_428_);
lean_dec(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___impl___boxed(lean_object* v_x_430_){
_start:
{
uint8_t v_x_4__boxed_431_; lean_object* v_res_432_; 
v_x_4__boxed_431_ = lean_unbox(v_x_430_);
v_res_432_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___impl(v_x_4__boxed_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(lean_object* v_k_433_){
_start:
{
lean_inc(v_k_433_);
return v_k_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg___boxed(lean_object* v_k_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(v_k_434_);
lean_dec(v_k_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(lean_object* v_motive_436_, lean_object* v_ctorIdx_437_, uint8_t v_t_438_, lean_object* v_h_439_, lean_object* v_k_440_){
_start:
{
lean_inc(v_k_440_);
return v_k_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___boxed(lean_object* v_motive_441_, lean_object* v_ctorIdx_442_, lean_object* v_t_443_, lean_object* v_h_444_, lean_object* v_k_445_){
_start:
{
uint8_t v_t_boxed_446_; lean_object* v_res_447_; 
v_t_boxed_446_ = lean_unbox(v_t_443_);
v_res_447_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(v_motive_441_, v_ctorIdx_442_, v_t_boxed_446_, v_h_444_, v_k_445_);
lean_dec(v_k_445_);
lean_dec(v_ctorIdx_442_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(lean_object* v_includeTrailingSep_448_){
_start:
{
lean_inc(v_includeTrailingSep_448_);
return v_includeTrailingSep_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg___boxed(lean_object* v_includeTrailingSep_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(v_includeTrailingSep_449_);
lean_dec(v_includeTrailingSep_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(lean_object* v_motive_451_, uint8_t v_t_452_, lean_object* v_h_453_, lean_object* v_includeTrailingSep_454_){
_start:
{
lean_inc(v_includeTrailingSep_454_);
return v_includeTrailingSep_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___boxed(lean_object* v_motive_455_, lean_object* v_t_456_, lean_object* v_h_457_, lean_object* v_includeTrailingSep_458_){
_start:
{
uint8_t v_t_boxed_459_; lean_object* v_res_460_; 
v_t_boxed_459_ = lean_unbox(v_t_456_);
v_res_460_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(v_motive_455_, v_t_boxed_459_, v_h_457_, v_includeTrailingSep_458_);
lean_dec(v_includeTrailingSep_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(lean_object* v_excludeTrailingSep_461_){
_start:
{
lean_inc(v_excludeTrailingSep_461_);
return v_excludeTrailingSep_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg___boxed(lean_object* v_excludeTrailingSep_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(v_excludeTrailingSep_462_);
lean_dec(v_excludeTrailingSep_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(lean_object* v_motive_464_, uint8_t v_t_465_, lean_object* v_h_466_, lean_object* v_excludeTrailingSep_467_){
_start:
{
lean_inc(v_excludeTrailingSep_467_);
return v_excludeTrailingSep_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___boxed(lean_object* v_motive_468_, lean_object* v_t_469_, lean_object* v_h_470_, lean_object* v_excludeTrailingSep_471_){
_start:
{
uint8_t v_t_boxed_472_; lean_object* v_res_473_; 
v_t_boxed_472_ = lean_unbox(v_t_469_);
v_res_473_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(v_motive_468_, v_t_boxed_472_, v_h_470_, v_excludeTrailingSep_471_);
lean_dec(v_excludeTrailingSep_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(lean_object* v_retainTrailingSep_474_){
_start:
{
lean_inc(v_retainTrailingSep_474_);
return v_retainTrailingSep_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg___boxed(lean_object* v_retainTrailingSep_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(v_retainTrailingSep_475_);
lean_dec(v_retainTrailingSep_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(lean_object* v_motive_477_, uint8_t v_t_478_, lean_object* v_h_479_, lean_object* v_retainTrailingSep_480_){
_start:
{
lean_inc(v_retainTrailingSep_480_);
return v_retainTrailingSep_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___boxed(lean_object* v_motive_481_, lean_object* v_t_482_, lean_object* v_h_483_, lean_object* v_retainTrailingSep_484_){
_start:
{
uint8_t v_t_boxed_485_; lean_object* v_res_486_; 
v_t_boxed_485_ = lean_unbox(v_t_482_);
v_res_486_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(v_motive_481_, v_t_boxed_485_, v_h_483_, v_retainTrailingSep_484_);
lean_dec(v_retainTrailingSep_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___impl(lean_object* v_x_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_tag_nat(v_x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___impl___boxed(lean_object* v_x_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___impl(v_x_489_);
lean_dec_ref(v_x_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(lean_object* v_t_491_, lean_object* v_k_492_){
_start:
{
switch(lean_obj_tag(v_t_491_))
{
case 1:
{
uint8_t v_allowFlattening_493_; lean_object* v_afterElem_x3f_494_; uint8_t v_trailingSep_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_allowFlattening_493_ = lean_ctor_get_uint8(v_t_491_, sizeof(void*)*1);
v_afterElem_x3f_494_ = lean_ctor_get(v_t_491_, 0);
lean_inc(v_afterElem_x3f_494_);
v_trailingSep_495_ = lean_ctor_get_uint8(v_t_491_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_491_, 1);
v___x_496_ = lean_box(v_allowFlattening_493_);
v___x_497_ = lean_box(v_trailingSep_495_);
v___x_498_ = lean_apply_3(v_k_492_, v___x_496_, v_afterElem_x3f_494_, v___x_497_);
return v___x_498_;
}
case 3:
{
lean_object* v_afterElem_x3f_499_; uint8_t v_trailingSep_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_afterElem_x3f_499_ = lean_ctor_get(v_t_491_, 0);
lean_inc(v_afterElem_x3f_499_);
v_trailingSep_500_ = lean_ctor_get_uint8(v_t_491_, sizeof(void*)*1);
lean_dec_ref_known(v_t_491_, 1);
v___x_501_ = lean_box(v_trailingSep_500_);
v___x_502_ = lean_apply_2(v_k_492_, v_afterElem_x3f_499_, v___x_501_);
return v___x_502_;
}
default: 
{
lean_object* v_afterElem_x3f_503_; lean_object* v_afterSep_x3f_504_; uint8_t v_trailingSep_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_afterElem_x3f_503_ = lean_ctor_get(v_t_491_, 0);
lean_inc(v_afterElem_x3f_503_);
v_afterSep_x3f_504_ = lean_ctor_get(v_t_491_, 1);
lean_inc(v_afterSep_x3f_504_);
v_trailingSep_505_ = lean_ctor_get_uint8(v_t_491_, sizeof(void*)*2);
lean_dec_ref(v_t_491_);
v___x_506_ = lean_box(v_trailingSep_505_);
v___x_507_ = lean_apply_3(v_k_492_, v_afterElem_x3f_503_, v_afterSep_x3f_504_, v___x_506_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(lean_object* v_motive_508_, lean_object* v_ctorIdx_509_, lean_object* v_t_510_, lean_object* v_h_511_, lean_object* v_k_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_510_, v_k_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___boxed(lean_object* v_motive_514_, lean_object* v_ctorIdx_515_, lean_object* v_t_516_, lean_object* v_h_517_, lean_object* v_k_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(v_motive_514_, v_ctorIdx_515_, v_t_516_, v_h_517_, v_k_518_);
lean_dec(v_ctorIdx_515_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim___redArg(lean_object* v_t_520_, lean_object* v_joinUsingSep_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_520_, v_joinUsingSep_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim(lean_object* v_motive_523_, lean_object* v_t_524_, lean_object* v_h_525_, lean_object* v_joinUsingSep_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_524_, v_joinUsingSep_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim___redArg(lean_object* v_t_528_, lean_object* v_joinUsingNl_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_528_, v_joinUsingNl_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim(lean_object* v_motive_531_, lean_object* v_t_532_, lean_object* v_h_533_, lean_object* v_joinUsingNl_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_532_, v_joinUsingNl_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim___redArg(lean_object* v_t_536_, lean_object* v_fillUsingSep_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_536_, v_fillUsingSep_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim(lean_object* v_motive_539_, lean_object* v_t_540_, lean_object* v_h_541_, lean_object* v_fillUsingSep_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_540_, v_fillUsingSep_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim___redArg(lean_object* v_t_544_, lean_object* v_fillUsingSpacedSep_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_544_, v_fillUsingSpacedSep_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim(lean_object* v_motive_547_, lean_object* v_t_548_, lean_object* v_h_549_, lean_object* v_fillUsingSpacedSep_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_548_, v_fillUsingSpacedSep_550_);
return v___x_551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(lean_object* v_x_552_){
_start:
{
switch(lean_obj_tag(v_x_552_))
{
case 1:
{
uint8_t v_trailingSep_553_; 
v_trailingSep_553_ = lean_ctor_get_uint8(v_x_552_, sizeof(void*)*1 + 1);
return v_trailingSep_553_;
}
case 3:
{
uint8_t v_trailingSep_554_; 
v_trailingSep_554_ = lean_ctor_get_uint8(v_x_552_, sizeof(void*)*1);
return v_trailingSep_554_;
}
default: 
{
uint8_t v_trailingSep_555_; 
v_trailingSep_555_ = lean_ctor_get_uint8(v_x_552_, sizeof(void*)*2);
return v_trailingSep_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep___boxed(lean_object* v_x_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(v_x_556_);
lean_dec_ref(v_x_556_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(lean_object* v_sepArray_559_, lean_object* v_sep_560_, uint8_t v_trailingSep_561_, lean_object* v___x_562_, lean_object* v_a_563_, lean_object* v_b_564_){
_start:
{
lean_object* v_inner_565_; lean_object* v_next_566_; 
v_inner_565_ = lean_ctor_get(v_a_563_, 2);
lean_inc(v_inner_565_);
v_next_566_ = lean_ctor_get(v_inner_565_, 0);
lean_inc(v_next_566_);
if (lean_obj_tag(v_next_566_) == 0)
{
lean_dec(v_inner_565_);
lean_dec_ref(v_a_563_);
lean_dec_ref(v_sep_560_);
return v_b_564_;
}
else
{
lean_object* v_nextIdx_567_; lean_object* v_n_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_617_; 
v_nextIdx_567_ = lean_ctor_get(v_a_563_, 0);
v_n_568_ = lean_ctor_get(v_a_563_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_a_563_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v_a_563_, 2);
lean_dec(v_unused_618_);
v___x_570_ = v_a_563_;
v_isShared_571_ = v_isSharedCheck_617_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_n_568_);
lean_inc(v_nextIdx_567_);
lean_dec(v_a_563_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_617_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_upperBound_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_615_; 
v_upperBound_572_ = lean_ctor_get(v_inner_565_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_inner_565_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_inner_565_, 0);
lean_dec(v_unused_616_);
v___x_574_ = v_inner_565_;
v_isShared_575_ = v_isSharedCheck_615_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_upperBound_572_);
lean_dec(v_inner_565_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_615_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_614_; 
v_val_576_ = lean_ctor_get(v_next_566_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_next_566_);
if (v_isSharedCheck_614_ == 0)
{
v___x_578_ = v_next_566_;
v_isShared_579_ = v_isSharedCheck_614_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v_next_566_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_614_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_nat_add(v_val_576_, v_nextIdx_567_);
lean_dec(v_nextIdx_567_);
lean_dec(v_val_576_);
v___x_581_ = lean_nat_dec_lt(v___x_580_, v_upperBound_572_);
if (v___x_581_ == 0)
{
lean_dec(v___x_580_);
lean_del_object(v___x_578_);
lean_del_object(v___x_574_);
lean_dec(v_upperBound_572_);
lean_del_object(v___x_570_);
lean_dec(v_n_568_);
lean_dec_ref(v_sep_560_);
return v_b_564_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_582_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v___x_580_, v___x_583_);
lean_inc(v___x_584_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_584_);
v___x_586_ = v___x_578_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_613_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_586_);
v___x_588_ = v___x_574_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_upperBound_572_);
v___x_588_ = v_reuseFailAlloc_612_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; 
lean_inc(v_n_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 2, v___x_588_);
lean_ctor_set(v___x_570_, 0, v_n_568_);
v___x_590_ = v___x_570_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_n_568_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_n_568_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v___x_588_);
v___x_590_ = v_reuseFailAlloc_611_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_array_get_borrowed(v___x_582_, v_sepArray_559_, v___x_580_);
v___x_592_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___y_595_; lean_object* v___y_599_; 
lean_inc(v___x_591_);
v___x_593_ = lean_array_push(v_b_564_, v___x_591_);
if (v_trailingSep_561_ == 2)
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_nat_sub(v___x_562_, v___x_583_);
v___x_609_ = lean_nat_dec_eq(v___x_580_, v___x_608_);
lean_dec(v___x_608_);
lean_dec(v___x_580_);
if (v___x_609_ == 0)
{
goto v___jp_603_;
}
else
{
lean_dec_ref(v___x_590_);
lean_dec(v___x_584_);
lean_dec_ref(v_sep_560_);
return v___x_593_;
}
}
else
{
lean_dec(v___x_580_);
goto v___jp_603_;
}
v___jp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_array_push(v___x_593_, v___y_595_);
v_a_563_ = v___x_590_;
v_b_564_ = v___x_596_;
goto _start;
}
v___jp_598_:
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_599_);
if (v___x_600_ == 0)
{
v___y_595_ = v___y_599_;
goto v___jp_594_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec_ref(v___y_599_);
lean_inc_ref(v_sep_560_);
v___x_601_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_560_);
v___x_602_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_601_);
v___y_595_ = v___x_602_;
goto v___jp_594_;
}
}
v___jp_603_:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_sepArray_559_);
v___x_605_ = lean_nat_dec_lt(v___x_584_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
lean_dec(v___x_584_);
v___x_606_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_599_ = v___x_606_;
goto v___jp_598_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = lean_array_fget_borrowed(v_sepArray_559_, v___x_584_);
lean_dec(v___x_584_);
lean_inc(v___x_607_);
v___y_599_ = v___x_607_;
goto v___jp_598_;
}
}
}
else
{
lean_dec(v___x_584_);
lean_dec(v___x_580_);
v_a_563_ = v___x_590_;
goto _start;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg___boxed(lean_object* v_sepArray_619_, lean_object* v_sep_620_, lean_object* v_trailingSep_621_, lean_object* v___x_622_, lean_object* v_a_623_, lean_object* v_b_624_){
_start:
{
uint8_t v_trailingSep_boxed_625_; lean_object* v_res_626_; 
v_trailingSep_boxed_625_ = lean_unbox(v_trailingSep_621_);
v_res_626_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_619_, v_sep_620_, v_trailingSep_boxed_625_, v___x_622_, v_a_623_, v_b_624_);
lean_dec(v___x_622_);
lean_dec_ref(v_sepArray_619_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(lean_object* v_sep_629_, lean_object* v_sepArray_630_, uint8_t v_trailingSep_631_){
_start:
{
lean_object* v___x_632_; lean_object* v_r_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v_r_633_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_634_ = lean_array_get_size(v_sepArray_630_);
v___x_635_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0));
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_634_);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v___x_632_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
lean_ctor_set(v___x_638_, 2, v___x_636_);
v___x_639_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_630_, v_sep_629_, v_trailingSep_631_, v___x_634_, v___x_638_, v_r_633_);
if (v_trailingSep_631_ == 1)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_640_ = lean_unsigned_to_nat(2u);
v___x_641_ = lean_array_get_size(v___x_639_);
v___x_642_ = lean_nat_mod(v___x_641_, v___x_640_);
v___x_643_ = lean_nat_dec_eq(v___x_642_, v___x_632_);
lean_dec(v___x_642_);
if (v___x_643_ == 0)
{
return v___x_639_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = lean_array_pop(v___x_639_);
return v___x_644_;
}
}
else
{
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___boxed(lean_object* v_sep_645_, lean_object* v_sepArray_646_, lean_object* v_trailingSep_647_){
_start:
{
uint8_t v_trailingSep_boxed_648_; lean_object* v_res_649_; 
v_trailingSep_boxed_648_ = lean_unbox(v_trailingSep_647_);
v_res_649_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_645_, v_sepArray_646_, v_trailingSep_boxed_648_);
lean_dec_ref(v_sepArray_646_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(lean_object* v_sepArray_650_, lean_object* v_sep_651_, uint8_t v_trailingSep_652_, lean_object* v___x_653_, lean_object* v_inst_654_, lean_object* v_R_655_, lean_object* v_a_656_, lean_object* v_b_657_, lean_object* v_c_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_650_, v_sep_651_, v_trailingSep_652_, v___x_653_, v_a_656_, v_b_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___boxed(lean_object* v_sepArray_660_, lean_object* v_sep_661_, lean_object* v_trailingSep_662_, lean_object* v___x_663_, lean_object* v_inst_664_, lean_object* v_R_665_, lean_object* v_a_666_, lean_object* v_b_667_, lean_object* v_c_668_){
_start:
{
uint8_t v_trailingSep_boxed_669_; lean_object* v_res_670_; 
v_trailingSep_boxed_669_ = lean_unbox(v_trailingSep_662_);
v_res_670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(v_sepArray_660_, v_sep_661_, v_trailingSep_boxed_669_, v___x_663_, v_inst_664_, v_R_665_, v_a_666_, v_b_667_, v_c_668_);
lean_dec(v___x_663_);
lean_dec_ref(v_sepArray_660_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(lean_object* v_sepArray_671_, lean_object* v_sep_672_, lean_object* v_afterSep_x3f_673_, lean_object* v_afterElem_x3f_674_, size_t v_sz_675_, size_t v_i_676_, lean_object* v_bs_677_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_lt(v_i_676_, v_sz_675_);
if (v___x_678_ == 0)
{
lean_dec(v_afterElem_x3f_674_);
lean_dec(v_afterSep_x3f_673_);
lean_dec_ref(v_sep_672_);
return v_bs_677_;
}
else
{
lean_object* v_v_679_; lean_object* v___x_680_; lean_object* v_bs_x27_681_; lean_object* v___y_683_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_v_679_ = lean_array_uget(v_bs_677_, v_i_676_);
v___x_680_ = lean_unsigned_to_nat(0u);
v_bs_x27_681_ = lean_array_uset(v_bs_677_, v_i_676_, v___x_680_);
v___x_702_ = lean_usize_to_nat(v_i_676_);
v___x_703_ = lean_array_get_size(v_sepArray_671_);
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_sub(v___x_703_, v___x_704_);
v___x_706_ = lean_nat_dec_eq(v___x_702_, v___x_705_);
lean_dec(v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v_isElem_709_; lean_object* v___y_711_; 
v___x_707_ = lean_unsigned_to_nat(2u);
v___x_708_ = lean_nat_mod(v___x_702_, v___x_707_);
lean_dec(v___x_702_);
v_isElem_709_ = lean_nat_dec_eq(v___x_708_, v___x_680_);
lean_dec(v___x_708_);
if (v_isElem_709_ == 0)
{
lean_inc(v_afterSep_x3f_673_);
v___y_711_ = v_afterSep_x3f_673_;
goto v___jp_710_;
}
else
{
lean_inc(v_afterElem_x3f_674_);
v___y_711_ = v_afterElem_x3f_674_;
goto v___jp_710_;
}
v___jp_710_:
{
if (v_isElem_709_ == 0)
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_679_);
if (v___x_712_ == 0)
{
v___y_689_ = v___y_711_;
v___y_690_ = v_v_679_;
goto v___jp_688_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v_v_679_);
lean_inc_ref(v_sep_672_);
v___x_713_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_672_);
v___x_714_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_713_);
v___y_689_ = v___y_711_;
v___y_690_ = v___x_714_;
goto v___jp_688_;
}
}
else
{
v___y_689_ = v___y_711_;
v___y_690_ = v_v_679_;
goto v___jp_688_;
}
}
}
else
{
lean_dec(v___x_702_);
v___y_683_ = v_v_679_;
goto v___jp_682_;
}
v___jp_682_:
{
size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_add(v_i_676_, v___x_684_);
v___x_686_ = lean_array_uset(v_bs_x27_681_, v_i_676_, v___y_683_);
v_i_676_ = v___x_685_;
v_bs_677_ = v___x_686_;
goto _start;
}
v___jp_688_:
{
if (lean_obj_tag(v___y_689_) == 1)
{
lean_object* v_val_691_; uint8_t v___x_692_; 
v_val_691_ = lean_ctor_get(v___y_689_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v___y_689_, 1);
v___x_692_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_690_);
if (v___x_692_ == 0)
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_691_);
if (v___x_693_ == 0)
{
lean_object* v_doc_694_; lean_object* v_doc_695_; uint8_t v___x_696_; 
v_doc_694_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_doc_694_);
lean_dec_ref(v___y_690_);
v_doc_695_ = lean_ctor_get(v_val_691_, 0);
lean_inc(v_doc_695_);
lean_dec(v_val_691_);
v___x_696_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_694_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; 
v___x_697_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_695_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_694_, v_doc_695_);
v___x_699_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_698_);
v___y_683_ = v___x_699_;
goto v___jp_682_;
}
else
{
lean_object* v___x_700_; 
lean_dec(v_doc_695_);
v___x_700_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_694_);
v___y_683_ = v___x_700_;
goto v___jp_682_;
}
}
else
{
lean_object* v___x_701_; 
lean_dec(v_doc_694_);
v___x_701_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_695_);
v___y_683_ = v___x_701_;
goto v___jp_682_;
}
}
else
{
lean_dec(v_val_691_);
v___y_683_ = v___y_690_;
goto v___jp_682_;
}
}
else
{
lean_dec_ref(v___y_690_);
v___y_683_ = v_val_691_;
goto v___jp_682_;
}
}
else
{
lean_dec(v___y_689_);
v___y_683_ = v___y_690_;
goto v___jp_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg___boxed(lean_object* v_sepArray_715_, lean_object* v_sep_716_, lean_object* v_afterSep_x3f_717_, lean_object* v_afterElem_x3f_718_, lean_object* v_sz_719_, lean_object* v_i_720_, lean_object* v_bs_721_){
_start:
{
size_t v_sz_boxed_722_; size_t v_i_boxed_723_; lean_object* v_res_724_; 
v_sz_boxed_722_ = lean_unbox_usize(v_sz_719_);
lean_dec(v_sz_719_);
v_i_boxed_723_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_res_724_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_715_, v_sep_716_, v_afterSep_x3f_717_, v_afterElem_x3f_718_, v_sz_boxed_722_, v_i_boxed_723_, v_bs_721_);
lean_dec_ref(v_sepArray_715_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(lean_object* v_sep_725_, lean_object* v_sepArray_726_, lean_object* v_afterElem_x3f_727_, lean_object* v_afterSep_x3f_728_){
_start:
{
size_t v_sz_729_; size_t v___x_730_; lean_object* v_docs_731_; lean_object* v___x_732_; 
v_sz_729_ = lean_array_size(v_sepArray_726_);
v___x_730_ = ((size_t)0ULL);
lean_inc_ref(v_sepArray_726_);
v_docs_731_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_726_, v_sep_725_, v_afterSep_x3f_728_, v_afterElem_x3f_727_, v_sz_729_, v___x_730_, v_sepArray_726_);
lean_dec_ref(v_sepArray_726_);
v___x_732_ = l_Lean_Fmt_TaggedDoc_join(v_docs_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(lean_object* v_sepArray_733_, lean_object* v_sep_734_, lean_object* v_afterSep_x3f_735_, lean_object* v_afterElem_x3f_736_, lean_object* v_as_737_, size_t v_sz_738_, size_t v_i_739_, lean_object* v_bs_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_733_, v_sep_734_, v_afterSep_x3f_735_, v_afterElem_x3f_736_, v_sz_738_, v_i_739_, v_bs_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___boxed(lean_object* v_sepArray_742_, lean_object* v_sep_743_, lean_object* v_afterSep_x3f_744_, lean_object* v_afterElem_x3f_745_, lean_object* v_as_746_, lean_object* v_sz_747_, lean_object* v_i_748_, lean_object* v_bs_749_){
_start:
{
size_t v_sz_boxed_750_; size_t v_i_boxed_751_; lean_object* v_res_752_; 
v_sz_boxed_750_ = lean_unbox_usize(v_sz_747_);
lean_dec(v_sz_747_);
v_i_boxed_751_ = lean_unbox_usize(v_i_748_);
lean_dec(v_i_748_);
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(v_sepArray_742_, v_sep_743_, v_afterSep_x3f_744_, v_afterElem_x3f_745_, v_as_746_, v_sz_boxed_750_, v_i_boxed_751_, v_bs_749_);
lean_dec_ref(v_as_746_);
lean_dec_ref(v_sepArray_742_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(lean_object* v_upperBound_753_, lean_object* v___x_754_, lean_object* v_sep_755_, lean_object* v_a_756_, lean_object* v_b_757_){
_start:
{
lean_object* v_a_759_; uint8_t v___x_763_; 
v___x_763_ = lean_nat_dec_lt(v_a_756_, v_upperBound_753_);
if (v___x_763_ == 0)
{
lean_dec(v_a_756_);
lean_dec_ref(v_sep_755_);
return v_b_757_;
}
else
{
lean_object* v_fst_764_; lean_object* v_snd_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_785_; 
v_fst_764_ = lean_ctor_get(v_b_757_, 0);
v_snd_765_ = lean_ctor_get(v_b_757_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_b_757_);
if (v_isSharedCheck_785_ == 0)
{
v___x_767_ = v_b_757_;
v_isShared_768_ = v_isSharedCheck_785_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snd_765_);
lean_inc(v_fst_764_);
lean_dec(v_b_757_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_785_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___y_770_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_array_fget_borrowed(v___x_754_, v_a_756_);
v___x_777_ = lean_unsigned_to_nat(2u);
v___x_778_ = lean_nat_mod(v_a_756_, v___x_777_);
v___x_779_ = lean_nat_dec_eq(v___x_778_, v___x_775_);
lean_dec(v___x_778_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; 
v___x_780_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_776_);
if (v___x_780_ == 0)
{
lean_inc(v___x_776_);
v___y_770_ = v___x_776_;
goto v___jp_769_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_inc_ref(v_sep_755_);
v___x_781_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_755_);
v___x_782_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_781_);
v___y_770_ = v___x_782_;
goto v___jp_769_;
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_del_object(v___x_767_);
lean_inc(v___x_776_);
v___x_783_ = lean_array_push(v_fst_764_, v___x_776_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v_snd_765_);
v_a_759_ = v___x_784_;
goto v___jp_758_;
}
v___jp_769_:
{
lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_771_ = lean_array_push(v_snd_765_, v___y_770_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_771_);
v___x_773_ = v___x_767_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_fst_764_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
v_a_759_ = v___x_773_;
goto v___jp_758_;
}
}
}
}
v___jp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v_a_756_, v___x_760_);
lean_dec(v_a_756_);
v_a_756_ = v___x_761_;
v_b_757_ = v_a_759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg___boxed(lean_object* v_upperBound_786_, lean_object* v___x_787_, lean_object* v_sep_788_, lean_object* v_a_789_, lean_object* v_b_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v_upperBound_786_, v___x_787_, v_sep_788_, v_a_789_, v_b_790_);
lean_dec_ref(v___x_787_);
lean_dec(v_upperBound_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(lean_object* v_sep_794_, lean_object* v_sepArray_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_fst_800_; lean_object* v_snd_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_array_get_size(v_sepArray_795_);
v___x_798_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0));
v___x_799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v___x_797_, v_sepArray_795_, v_sep_794_, v___x_796_, v___x_798_);
v_fst_800_ = lean_ctor_get(v___x_799_, 0);
v_snd_801_ = lean_ctor_get(v___x_799_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_799_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_snd_801_);
lean_inc(v_fst_800_);
lean_dec(v___x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_fst_800_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___boxed(lean_object* v_sep_809_, lean_object* v_sepArray_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_809_, v_sepArray_810_);
lean_dec_ref(v_sepArray_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(lean_object* v_upperBound_812_, lean_object* v___x_813_, lean_object* v_sep_814_, lean_object* v_inst_815_, lean_object* v_R_816_, lean_object* v_a_817_, lean_object* v_b_818_, lean_object* v_c_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v_upperBound_812_, v___x_813_, v_sep_814_, v_a_817_, v_b_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___boxed(lean_object* v_upperBound_821_, lean_object* v___x_822_, lean_object* v_sep_823_, lean_object* v_inst_824_, lean_object* v_R_825_, lean_object* v_a_826_, lean_object* v_b_827_, lean_object* v_c_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(v_upperBound_821_, v___x_822_, v_sep_823_, v_inst_824_, v_R_825_, v_a_826_, v_b_827_, v_c_828_);
lean_dec_ref(v___x_822_);
lean_dec(v_upperBound_821_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(lean_object* v_fst_830_, lean_object* v_val_831_, size_t v_sz_832_, size_t v_i_833_, lean_object* v_bs_834_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_lt(v_i_833_, v_sz_832_);
if (v___x_835_ == 0)
{
lean_dec_ref(v_val_831_);
return v_bs_834_;
}
else
{
lean_object* v_v_836_; lean_object* v___x_837_; lean_object* v_bs_x27_838_; lean_object* v___y_840_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_v_836_ = lean_array_uget(v_bs_834_, v_i_833_);
v___x_837_ = lean_unsigned_to_nat(0u);
v_bs_x27_838_ = lean_array_uset(v_bs_834_, v_i_833_, v___x_837_);
v___x_845_ = lean_usize_to_nat(v_i_833_);
v___x_846_ = lean_array_get_size(v_fst_830_);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_sub(v___x_846_, v___x_847_);
v___x_849_ = lean_nat_dec_eq(v___x_845_, v___x_848_);
lean_dec(v___x_848_);
lean_dec(v___x_845_);
if (v___x_849_ == 0)
{
uint8_t v___x_850_; 
v___x_850_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_836_);
if (v___x_850_ == 0)
{
uint8_t v___x_851_; 
v___x_851_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_831_);
if (v___x_851_ == 0)
{
lean_object* v_doc_852_; lean_object* v_doc_853_; uint8_t v___x_854_; 
v_doc_852_ = lean_ctor_get(v_v_836_, 0);
lean_inc(v_doc_852_);
lean_dec(v_v_836_);
v_doc_853_ = lean_ctor_get(v_val_831_, 0);
v___x_854_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_852_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; 
v___x_855_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_853_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc(v_doc_853_);
v___x_856_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_852_, v_doc_853_);
v___x_857_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_856_);
v___y_840_ = v___x_857_;
goto v___jp_839_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_852_);
v___y_840_ = v___x_858_;
goto v___jp_839_;
}
}
else
{
lean_object* v___x_859_; 
lean_dec(v_doc_852_);
lean_inc(v_doc_853_);
v___x_859_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_853_);
v___y_840_ = v___x_859_;
goto v___jp_839_;
}
}
else
{
v___y_840_ = v_v_836_;
goto v___jp_839_;
}
}
else
{
lean_dec(v_v_836_);
lean_inc_ref(v_val_831_);
v___y_840_ = v_val_831_;
goto v___jp_839_;
}
}
else
{
v___y_840_ = v_v_836_;
goto v___jp_839_;
}
v___jp_839_:
{
size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; 
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_add(v_i_833_, v___x_841_);
v___x_843_ = lean_array_uset(v_bs_x27_838_, v_i_833_, v___y_840_);
v_i_833_ = v___x_842_;
v_bs_834_ = v___x_843_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg___boxed(lean_object* v_fst_860_, lean_object* v_val_861_, lean_object* v_sz_862_, lean_object* v_i_863_, lean_object* v_bs_864_){
_start:
{
size_t v_sz_boxed_865_; size_t v_i_boxed_866_; lean_object* v_res_867_; 
v_sz_boxed_865_ = lean_unbox_usize(v_sz_862_);
lean_dec(v_sz_862_);
v_i_boxed_866_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_res_867_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_860_, v_val_861_, v_sz_boxed_865_, v_i_boxed_866_, v_bs_864_);
lean_dec_ref(v_fst_860_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(lean_object* v_sep_868_, lean_object* v_sepArray_869_, lean_object* v_afterElem_x3f_870_){
_start:
{
lean_object* v_elems_872_; lean_object* v___x_875_; 
v___x_875_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_868_, v_sepArray_869_);
if (lean_obj_tag(v_afterElem_x3f_870_) == 1)
{
lean_object* v_fst_876_; lean_object* v_val_877_; size_t v_sz_878_; size_t v___x_879_; lean_object* v_elems_880_; 
v_fst_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc_n(v_fst_876_, 2);
lean_dec_ref(v___x_875_);
v_val_877_ = lean_ctor_get(v_afterElem_x3f_870_, 0);
lean_inc(v_val_877_);
lean_dec_ref_known(v_afterElem_x3f_870_, 1);
v_sz_878_ = lean_array_size(v_fst_876_);
v___x_879_ = ((size_t)0ULL);
v_elems_880_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_876_, v_val_877_, v_sz_878_, v___x_879_, v_fst_876_);
lean_dec(v_fst_876_);
v_elems_872_ = v_elems_880_;
goto v___jp_871_;
}
else
{
lean_object* v_fst_881_; 
lean_dec(v_afterElem_x3f_870_);
v_fst_881_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_fst_881_);
lean_dec_ref(v___x_875_);
v_elems_872_ = v_fst_881_;
goto v___jp_871_;
}
v___jp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_874_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_873_, v_elems_872_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl___boxed(lean_object* v_sep_882_, lean_object* v_sepArray_883_, lean_object* v_afterElem_x3f_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(v_sep_882_, v_sepArray_883_, v_afterElem_x3f_884_);
lean_dec_ref(v_sepArray_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(lean_object* v_fst_886_, lean_object* v_val_887_, lean_object* v_as_888_, size_t v_sz_889_, size_t v_i_890_, lean_object* v_bs_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_886_, v_val_887_, v_sz_889_, v_i_890_, v_bs_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___boxed(lean_object* v_fst_893_, lean_object* v_val_894_, lean_object* v_as_895_, lean_object* v_sz_896_, lean_object* v_i_897_, lean_object* v_bs_898_){
_start:
{
size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v_sz_boxed_899_ = lean_unbox_usize(v_sz_896_);
lean_dec(v_sz_896_);
v_i_boxed_900_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(v_fst_893_, v_val_894_, v_as_895_, v_sz_boxed_899_, v_i_boxed_900_, v_bs_898_);
lean_dec_ref(v_as_895_);
lean_dec_ref(v_fst_893_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep(lean_object* v_sep_902_, lean_object* v_sepArray_903_, lean_object* v_afterElem_904_){
_start:
{
lean_object* v___x_905_; lean_object* v_fst_906_; lean_object* v_snd_907_; lean_object* v___y_909_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_905_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_902_, v_sepArray_903_);
v_fst_906_ = lean_ctor_get(v___x_905_, 0);
v_snd_907_ = lean_ctor_get(v___x_905_, 1);
v___x_912_ = lean_array_get_size(v_snd_907_);
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_nat_dec_eq(v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_array_get_size(v_fst_906_);
v___x_916_ = lean_nat_dec_eq(v___x_912_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec_ref(v_afterElem_904_);
return v___x_905_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
lean_inc(v_snd_907_);
lean_inc(v_fst_906_);
lean_dec_ref(v___x_905_);
v___x_917_ = lean_unsigned_to_nat(1u);
v___x_918_ = lean_nat_sub(v___x_915_, v___x_917_);
v___x_919_ = lean_nat_dec_lt(v___x_918_, v___x_915_);
if (v___x_919_ == 0)
{
lean_dec(v___x_918_);
lean_dec_ref(v_afterElem_904_);
v___y_909_ = v_fst_906_;
goto v___jp_908_;
}
else
{
lean_object* v___x_920_; lean_object* v_v_921_; lean_object* v___x_922_; lean_object* v_xs_x27_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_920_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_v_921_ = lean_array_fget(v_fst_906_, v___x_918_);
v___x_922_ = lean_box(0);
v_xs_x27_923_ = lean_array_fset(v_fst_906_, v___x_918_, v___x_922_);
v___x_924_ = lean_nat_sub(v___x_912_, v___x_917_);
v___x_925_ = lean_array_get_borrowed(v___x_920_, v_snd_907_, v___x_924_);
lean_dec(v___x_924_);
v___x_926_ = lean_unsigned_to_nat(3u);
v___x_927_ = lean_mk_empty_array_with_capacity(v___x_926_);
v___x_928_ = lean_array_push(v___x_927_, v_v_921_);
v___x_929_ = lean_array_push(v___x_928_, v_afterElem_904_);
lean_inc(v___x_925_);
v___x_930_ = lean_array_push(v___x_929_, v___x_925_);
v___x_931_ = l_Lean_Fmt_TaggedDoc_join(v___x_930_);
v___x_932_ = lean_array_fset(v_xs_x27_923_, v___x_918_, v___x_931_);
lean_dec(v___x_918_);
v___y_909_ = v___x_932_;
goto v___jp_908_;
}
}
}
else
{
lean_dec_ref(v_afterElem_904_);
return v___x_905_;
}
v___jp_908_:
{
lean_object* v_seps_910_; lean_object* v___x_911_; 
v_seps_910_ = lean_array_pop(v_snd_907_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___y_909_);
lean_ctor_set(v___x_911_, 1, v_seps_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep___boxed(lean_object* v_sep_933_, lean_object* v_sepArray_934_, lean_object* v_afterElem_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep(v_sep_933_, v_sepArray_934_, v_afterElem_935_);
lean_dec_ref(v_sepArray_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0(lean_object* v___x_937_, lean_object* v_snd_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v_i_941_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_sep_948_; lean_object* v___x_949_; 
v___x_942_ = lean_array_get_borrowed(v___x_937_, v_snd_938_, v_i_941_);
v___x_943_ = lean_unsigned_to_nat(3u);
v___x_944_ = lean_mk_empty_array_with_capacity(v___x_943_);
v___x_945_ = lean_array_push(v___x_944_, v___y_939_);
lean_inc(v___x_942_);
v___x_946_ = lean_array_push(v___x_945_, v___x_942_);
v___x_947_ = lean_array_push(v___x_946_, v___y_940_);
v_sep_948_ = l_Lean_Fmt_TaggedDoc_join(v___x_947_);
lean_inc_ref(v_sep_948_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_sep_948_);
lean_ctor_set(v___x_949_, 1, v_sep_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0___boxed(lean_object* v___x_950_, lean_object* v_snd_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v_i_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0(v___x_950_, v_snd_951_, v___y_952_, v___y_953_, v_i_954_);
lean_dec(v_i_954_);
lean_dec_ref(v_snd_951_);
lean_dec_ref(v___x_950_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(lean_object* v_sep_956_, lean_object* v_sepArray_957_, lean_object* v_afterElem_x3f_958_, lean_object* v_afterSep_x3f_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_970_; 
v___x_960_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (lean_obj_tag(v_afterElem_x3f_958_) == 0)
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_970_ = v___x_973_;
goto v___jp_969_;
}
else
{
lean_object* v_val_974_; 
v_val_974_ = lean_ctor_get(v_afterElem_x3f_958_, 0);
lean_inc(v_val_974_);
lean_dec_ref_known(v_afterElem_x3f_958_, 1);
v___y_970_ = v_val_974_;
goto v___jp_969_;
}
v___jp_961_:
{
lean_object* v___x_964_; lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___f_967_; lean_object* v___x_968_; 
lean_inc_ref(v___y_962_);
v___x_964_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep(v_sep_956_, v_sepArray_957_, v___y_962_);
v_fst_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_fst_965_);
v_snd_966_ = lean_ctor_get(v___x_964_, 1);
lean_inc(v_snd_966_);
lean_dec_ref(v___x_964_);
v___f_967_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0___boxed), 5, 4);
lean_closure_set(v___f_967_, 0, v___x_960_);
lean_closure_set(v___f_967_, 1, v_snd_966_);
lean_closure_set(v___f_967_, 2, v___y_962_);
lean_closure_set(v___f_967_, 3, v___y_963_);
v___x_968_ = l_Lean_Fmt_TaggedDoc_fillWith(v_fst_965_, v___f_967_);
return v___x_968_;
}
v___jp_969_:
{
if (lean_obj_tag(v_afterSep_x3f_959_) == 0)
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_962_ = v___y_970_;
v___y_963_ = v___x_971_;
goto v___jp_961_;
}
else
{
lean_object* v_val_972_; 
v_val_972_ = lean_ctor_get(v_afterSep_x3f_959_, 0);
lean_inc(v_val_972_);
lean_dec_ref_known(v_afterSep_x3f_959_, 1);
v___y_962_ = v___y_970_;
v___y_963_ = v_val_972_;
goto v___jp_961_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___boxed(lean_object* v_sep_975_, lean_object* v_sepArray_976_, lean_object* v_afterElem_x3f_977_, lean_object* v_afterSep_x3f_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(v_sep_975_, v_sepArray_976_, v_afterElem_x3f_977_, v_afterSep_x3f_978_);
lean_dec_ref(v_sepArray_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0(lean_object* v___x_980_, lean_object* v_snd_981_, lean_object* v___y_982_, lean_object* v_i_983_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_sep_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_984_ = lean_array_get_borrowed(v___x_980_, v_snd_981_, v_i_983_);
v___x_985_ = lean_unsigned_to_nat(2u);
v___x_986_ = lean_mk_empty_array_with_capacity(v___x_985_);
lean_inc_ref(v___x_986_);
v___x_987_ = lean_array_push(v___x_986_, v___y_982_);
lean_inc(v___x_984_);
v___x_988_ = lean_array_push(v___x_987_, v___x_984_);
v_sep_989_ = l_Lean_Fmt_TaggedDoc_join(v___x_988_);
v___x_990_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v_sep_989_);
v___x_991_ = lean_array_push(v___x_986_, v_sep_989_);
v___x_992_ = lean_array_push(v___x_991_, v___x_990_);
v___x_993_ = l_Lean_Fmt_TaggedDoc_join(v___x_992_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v_sep_989_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0___boxed(lean_object* v___x_995_, lean_object* v_snd_996_, lean_object* v___y_997_, lean_object* v_i_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0(v___x_995_, v_snd_996_, v___y_997_, v_i_998_);
lean_dec(v_i_998_);
lean_dec_ref(v_snd_996_);
lean_dec_ref(v___x_995_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(lean_object* v_sep_1000_, lean_object* v_sepArray_1001_, lean_object* v_afterElem_x3f_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___y_1005_; 
v___x_1003_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (lean_obj_tag(v_afterElem_x3f_1002_) == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1005_ = v___x_1011_;
goto v___jp_1004_;
}
else
{
lean_object* v_val_1012_; 
v_val_1012_ = lean_ctor_get(v_afterElem_x3f_1002_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v_afterElem_x3f_1002_, 1);
v___y_1005_ = v_val_1012_;
goto v___jp_1004_;
}
v___jp_1004_:
{
lean_object* v___x_1006_; lean_object* v_fst_1007_; lean_object* v_snd_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; 
lean_inc_ref(v___y_1005_);
v___x_1006_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep(v_sep_1000_, v_sepArray_1001_, v___y_1005_);
v_fst_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_fst_1007_);
v_snd_1008_ = lean_ctor_get(v___x_1006_, 1);
lean_inc(v_snd_1008_);
lean_dec_ref(v___x_1006_);
v___f_1009_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1009_, 0, v___x_1003_);
lean_closure_set(v___f_1009_, 1, v_snd_1008_);
lean_closure_set(v___f_1009_, 2, v___y_1005_);
v___x_1010_ = l_Lean_Fmt_TaggedDoc_fillWith(v_fst_1007_, v___f_1009_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___boxed(lean_object* v_sep_1013_, lean_object* v_sepArray_1014_, lean_object* v_afterElem_x3f_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(v_sep_1013_, v_sepArray_1014_, v_afterElem_x3f_1015_);
lean_dec_ref(v_sepArray_1014_);
return v_res_1016_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepArray___closed__0(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = l_Lean_Fmt_TaggedDoc_space;
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object* v_sep_1019_, lean_object* v_sepArray_1020_, lean_object* v_format_1021_){
_start:
{
lean_object* v___x_1022_; uint8_t v___y_1024_; 
v___x_1022_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
switch(lean_obj_tag(v_format_1021_))
{
case 1:
{
uint8_t v_trailingSep_1052_; 
v_trailingSep_1052_ = lean_ctor_get_uint8(v_format_1021_, sizeof(void*)*1 + 1);
v___y_1024_ = v_trailingSep_1052_;
goto v___jp_1023_;
}
case 3:
{
uint8_t v_trailingSep_1053_; 
v_trailingSep_1053_ = lean_ctor_get_uint8(v_format_1021_, sizeof(void*)*1);
v___y_1024_ = v_trailingSep_1053_;
goto v___jp_1023_;
}
default: 
{
uint8_t v_trailingSep_1054_; 
v_trailingSep_1054_ = lean_ctor_get_uint8(v_format_1021_, sizeof(void*)*2);
v___y_1024_ = v_trailingSep_1054_;
goto v___jp_1023_;
}
}
v___jp_1023_:
{
lean_object* v_sepArray_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
lean_inc_ref(v_sep_1019_);
v_sepArray_1025_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_1019_, v_sepArray_1020_, v___y_1024_);
v___x_1026_ = lean_array_get_size(v_sepArray_1025_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_nat_dec_eq(v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_dec_eq(v___x_1026_, v___x_1029_);
if (v___x_1030_ == 0)
{
switch(lean_obj_tag(v_format_1021_))
{
case 0:
{
lean_object* v_afterElem_x3f_1031_; lean_object* v_afterSep_x3f_1032_; lean_object* v___x_1033_; 
v_afterElem_x3f_1031_ = lean_ctor_get(v_format_1021_, 0);
lean_inc(v_afterElem_x3f_1031_);
v_afterSep_x3f_1032_ = lean_ctor_get(v_format_1021_, 1);
lean_inc(v_afterSep_x3f_1032_);
lean_dec_ref_known(v_format_1021_, 2);
v___x_1033_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(v_sep_1019_, v_sepArray_1025_, v_afterElem_x3f_1031_, v_afterSep_x3f_1032_);
return v___x_1033_;
}
case 1:
{
uint8_t v_allowFlattening_1034_; lean_object* v_afterElem_x3f_1035_; lean_object* v_joinedUsingNl_1036_; 
v_allowFlattening_1034_ = lean_ctor_get_uint8(v_format_1021_, sizeof(void*)*1);
v_afterElem_x3f_1035_ = lean_ctor_get(v_format_1021_, 0);
lean_inc_n(v_afterElem_x3f_1035_, 2);
lean_dec_ref_known(v_format_1021_, 1);
lean_inc_ref(v_sep_1019_);
v_joinedUsingNl_1036_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(v_sep_1019_, v_sepArray_1025_, v_afterElem_x3f_1035_);
if (v_allowFlattening_1034_ == 0)
{
lean_dec(v_afterElem_x3f_1035_);
lean_dec_ref(v_sepArray_1025_);
lean_dec_ref(v_sep_1019_);
return v_joinedUsingNl_1036_;
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1037_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepArray___closed__0, &l_Lean_Fmt_Layouts_sepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_sepArray___closed__0);
v___x_1038_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(v_sep_1019_, v_sepArray_1025_, v_afterElem_x3f_1035_, v___x_1037_);
v___x_1039_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1038_);
v___x_1040_ = lean_unsigned_to_nat(2u);
v___x_1041_ = lean_mk_empty_array_with_capacity(v___x_1040_);
v___x_1042_ = lean_array_push(v___x_1041_, v___x_1039_);
v___x_1043_ = lean_array_push(v___x_1042_, v_joinedUsingNl_1036_);
v___x_1044_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1043_);
return v___x_1044_;
}
}
case 2:
{
lean_object* v_afterElem_x3f_1045_; lean_object* v_afterSep_x3f_1046_; lean_object* v___x_1047_; 
v_afterElem_x3f_1045_ = lean_ctor_get(v_format_1021_, 0);
lean_inc(v_afterElem_x3f_1045_);
v_afterSep_x3f_1046_ = lean_ctor_get(v_format_1021_, 1);
lean_inc(v_afterSep_x3f_1046_);
lean_dec_ref_known(v_format_1021_, 2);
v___x_1047_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(v_sep_1019_, v_sepArray_1025_, v_afterElem_x3f_1045_, v_afterSep_x3f_1046_);
lean_dec_ref(v_sepArray_1025_);
return v___x_1047_;
}
default: 
{
lean_object* v_afterElem_x3f_1048_; lean_object* v___x_1049_; 
v_afterElem_x3f_1048_ = lean_ctor_get(v_format_1021_, 0);
lean_inc(v_afterElem_x3f_1048_);
lean_dec_ref_known(v_format_1021_, 1);
v___x_1049_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(v_sep_1019_, v_sepArray_1025_, v_afterElem_x3f_1048_);
lean_dec_ref(v_sepArray_1025_);
return v___x_1049_;
}
}
}
else
{
lean_object* v___x_1050_; 
lean_dec_ref(v_format_1021_);
lean_dec_ref(v_sep_1019_);
v___x_1050_ = lean_array_get(v___x_1022_, v_sepArray_1025_, v___x_1027_);
lean_dec_ref(v_sepArray_1025_);
return v___x_1050_;
}
}
else
{
lean_object* v___x_1051_; 
lean_dec_ref(v_sepArray_1025_);
lean_dec_ref(v_format_1021_);
lean_dec_ref(v_sep_1019_);
v___x_1051_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray___boxed(lean_object* v_sep_1055_, lean_object* v_sepArray_1056_, lean_object* v_format_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1055_, v_sepArray_1056_, v_format_1057_);
lean_dec_ref(v_sepArray_1056_);
return v_res_1058_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepLines___closed__0(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepLines___closed__1(void){
_start:
{
uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = 1;
v___x_1062_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepLines___closed__0, &l_Lean_Fmt_Layouts_sepLines___closed__0_once, _init_l_Lean_Fmt_Layouts_sepLines___closed__0);
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1062_);
lean_ctor_set_uint8(v___x_1064_, sizeof(void*)*2, v___x_1061_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines(lean_object* v_sep_1065_, lean_object* v_lines_1066_, uint8_t v_includeSeps_1067_){
_start:
{
if (v_includeSeps_1067_ == 0)
{
lean_object* v___x_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = 1;
v___x_1070_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set_uint8(v___x_1070_, sizeof(void*)*1, v_includeSeps_1067_);
lean_ctor_set_uint8(v___x_1070_, sizeof(void*)*1 + 1, v___x_1069_);
v___x_1071_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1065_, v_lines_1066_, v___x_1070_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepLines___closed__1, &l_Lean_Fmt_Layouts_sepLines___closed__1_once, _init_l_Lean_Fmt_Layouts_sepLines___closed__1);
v___x_1073_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1065_, v_lines_1066_, v___x_1072_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines___boxed(lean_object* v_sep_1074_, lean_object* v_lines_1075_, lean_object* v_includeSeps_1076_){
_start:
{
uint8_t v_includeSeps_boxed_1077_; lean_object* v_res_1078_; 
v_includeSeps_boxed_1077_ = lean_unbox(v_includeSeps_1076_);
v_res_1078_ = l_Lean_Fmt_Layouts_sepLines(v_sep_1074_, v_lines_1075_, v_includeSeps_boxed_1077_);
lean_dec_ref(v_lines_1075_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object* v_sep_1082_, lean_object* v_elems_1083_){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_Fmt_Layouts_sepFill___closed__0));
v___x_1085_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1082_, v_elems_1083_, v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill___boxed(lean_object* v_sep_1086_, lean_object* v_elems_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Fmt_Layouts_sepFill(v_sep_1086_, v_elems_1087_);
lean_dec_ref(v_elems_1087_);
return v_res_1088_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2(void){
_start:
{
uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1095_ = 1;
v___x_1096_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1);
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v___x_1096_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*2, v___x_1095_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical(lean_object* v_sep_1099_, lean_object* v_elems_1100_, uint8_t v_includeSeps_1101_){
_start:
{
uint8_t v___x_1102_; lean_object* v_elems_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1102_ = 1;
lean_inc_ref(v_sep_1099_);
v_elems_1103_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_1099_, v_elems_1100_, v___x_1102_);
v___x_1104_ = lean_array_get_size(v_elems_1103_);
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_dec_eq(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
if (v_includeSeps_1101_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0));
v___x_1108_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1099_, v_elems_1103_, v___x_1107_);
lean_dec_ref(v_elems_1103_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v___x_1110_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1099_, v_elems_1103_, v___x_1109_);
lean_dec_ref(v_elems_1103_);
v___x_1111_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_1110_);
return v___x_1111_;
}
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v_sep_1099_);
v___x_1112_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_array_get(v___x_1112_, v_elems_1103_, v___x_1113_);
lean_dec_ref(v_elems_1103_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___boxed(lean_object* v_sep_1115_, lean_object* v_elems_1116_, lean_object* v_includeSeps_1117_){
_start:
{
uint8_t v_includeSeps_boxed_1118_; lean_object* v_res_1119_; 
v_includeSeps_boxed_1118_ = lean_unbox(v_includeSeps_1117_);
v_res_1119_ = l_Lean_Fmt_Layouts_sepHorizontalOrVertical(v_sep_1115_, v_elems_1116_, v_includeSeps_boxed_1118_);
lean_dec_ref(v_elems_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(lean_object* v___x_1120_, lean_object* v_docsWithIntermediateWhitespace_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_fst_1123_; lean_object* v_snd_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1153_; 
v_fst_1123_ = lean_ctor_get(v_a_1122_, 0);
v_snd_1124_ = lean_ctor_get(v_a_1122_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_a_1122_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1126_ = v_a_1122_;
v_isShared_1127_ = v_isSharedCheck_1153_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_snd_1124_);
lean_inc(v_fst_1123_);
lean_dec(v_a_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1153_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_nat_dec_lt(v_snd_1124_, v___x_1120_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1130_; 
if (v_isShared_1127_ == 0)
{
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_fst_1123_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_snd_1124_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___y_1137_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___f_1132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_1133_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1134_ = lean_unsigned_to_nat(1u);
v___x_1135_ = lean_array_get_borrowed(v___x_1133_, v_docsWithIntermediateWhitespace_1121_, v_snd_1124_);
v___x_1148_ = lean_nat_add(v_snd_1124_, v___x_1134_);
v___x_1149_ = lean_array_get_size(v_docsWithIntermediateWhitespace_1121_);
v___x_1150_ = lean_nat_dec_lt(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
lean_dec(v___x_1148_);
v___x_1151_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1137_ = v___x_1151_;
goto v___jp_1136_;
}
else
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_array_fget_borrowed(v_docsWithIntermediateWhitespace_1121_, v___x_1148_);
lean_dec(v___x_1148_);
lean_inc(v___x_1152_);
v___y_1137_ = v___x_1152_;
goto v___jp_1136_;
}
v___jp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
lean_inc(v___x_1135_);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1135_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1137_);
lean_ctor_set(v___x_1139_, 1, v___f_1132_);
v___x_1140_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1138_, v___x_1139_);
v___x_1141_ = lean_array_push(v_fst_1123_, v___x_1140_);
v___x_1142_ = lean_unsigned_to_nat(2u);
v___x_1143_ = lean_nat_add(v_snd_1124_, v___x_1142_);
lean_dec(v_snd_1124_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 1, v___x_1143_);
lean_ctor_set(v___x_1126_, 0, v___x_1141_);
v___x_1145_ = v___x_1126_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
v_a_1122_ = v___x_1145_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg___boxed(lean_object* v___x_1154_, lean_object* v_docsWithIntermediateWhitespace_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1154_, v_docsWithIntermediateWhitespace_1155_, v_a_1156_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1155_);
lean_dec(v___x_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace(lean_object* v_docsWithIntermediateWhitespace_1163_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_array_get_size(v_docsWithIntermediateWhitespace_1163_);
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = lean_nat_dec_eq(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
v___x_1168_ = lean_nat_dec_eq(v___x_1164_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_fst_1171_; lean_object* v___x_1172_; 
v___x_1169_ = ((lean_object*)(l_Lean_Fmt_Layouts_retainedWhitespace___closed__1));
v___x_1170_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1164_, v_docsWithIntermediateWhitespace_1163_, v___x_1169_);
v_fst_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_fst_1171_);
lean_dec_ref(v___x_1170_);
v___x_1172_ = l_Lean_Fmt_TaggedDoc_combine(v_fst_1171_);
lean_dec(v_fst_1171_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1174_ = lean_array_get_borrowed(v___x_1173_, v_docsWithIntermediateWhitespace_1163_, v___x_1165_);
lean_inc(v___x_1174_);
return v___x_1174_;
}
}
else
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___boxed(lean_object* v_docsWithIntermediateWhitespace_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Fmt_Layouts_retainedWhitespace(v_docsWithIntermediateWhitespace_1176_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1176_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(lean_object* v___x_1178_, lean_object* v_docsWithIntermediateWhitespace_1179_, lean_object* v_inst_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1178_, v_docsWithIntermediateWhitespace_1179_, v_a_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___boxed(lean_object* v___x_1183_, lean_object* v_docsWithIntermediateWhitespace_1184_, lean_object* v_inst_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(v___x_1183_, v_docsWithIntermediateWhitespace_1184_, v_inst_1185_, v_a_1186_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1184_);
lean_dec(v___x_1183_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1___redArg(lean_object* v_v_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1(lean_object* v_00_u03c4_1190_, lean_object* v_v_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(lean_object* v_a_1193_, lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1194_) == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_box(0);
return v___x_1195_;
}
else
{
lean_object* v_key_1196_; lean_object* v_value_1197_; lean_object* v_tail_1198_; size_t v_ptr_1199_; size_t v_ptr_1200_; uint8_t v___x_1201_; 
v_key_1196_ = lean_ctor_get(v_x_1194_, 0);
v_value_1197_ = lean_ctor_get(v_x_1194_, 1);
v_tail_1198_ = lean_ctor_get(v_x_1194_, 2);
v_ptr_1199_ = lean_ctor_get_usize(v_key_1196_, 1);
v_ptr_1200_ = lean_ctor_get_usize(v_a_1193_, 1);
v___x_1201_ = lean_usize_dec_eq(v_ptr_1199_, v_ptr_1200_);
if (v___x_1201_ == 0)
{
v_x_1194_ = v_tail_1198_;
goto _start;
}
else
{
lean_object* v___x_1203_; 
lean_inc(v_value_1197_);
v___x_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1203_, 0, v_value_1197_);
return v___x_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg___boxed(lean_object* v_a_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1204_, v_x_1205_);
lean_dec(v_x_1205_);
lean_dec_ref(v_a_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(lean_object* v_m_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_buckets_1209_; size_t v_ptr_1210_; lean_object* v___x_1211_; uint64_t v___x_1212_; uint64_t v___x_1213_; uint64_t v___x_1214_; uint64_t v_fold_1215_; uint64_t v___x_1216_; uint64_t v___x_1217_; uint64_t v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_buckets_1209_ = lean_ctor_get(v_m_1207_, 1);
v_ptr_1210_ = lean_ctor_get_usize(v_a_1208_, 1);
v___x_1211_ = lean_array_get_size(v_buckets_1209_);
v___x_1212_ = lean_usize_to_uint64(v_ptr_1210_);
v___x_1213_ = 32ULL;
v___x_1214_ = lean_uint64_shift_right(v___x_1212_, v___x_1213_);
v_fold_1215_ = lean_uint64_xor(v___x_1212_, v___x_1214_);
v___x_1216_ = 16ULL;
v___x_1217_ = lean_uint64_shift_right(v_fold_1215_, v___x_1216_);
v___x_1218_ = lean_uint64_xor(v_fold_1215_, v___x_1217_);
v___x_1219_ = lean_uint64_to_usize(v___x_1218_);
v___x_1220_ = lean_usize_of_nat(v___x_1211_);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_sub(v___x_1220_, v___x_1221_);
v___x_1223_ = lean_usize_land(v___x_1219_, v___x_1222_);
v___x_1224_ = lean_array_uget_borrowed(v_buckets_1209_, v___x_1223_);
v___x_1225_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1208_, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg___boxed(lean_object* v_m_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1226_, v_a_1227_);
lean_dec_ref(v_a_1227_);
lean_dec_ref(v_m_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(lean_object* v_a_1229_, lean_object* v_b_1230_, lean_object* v_x_1231_){
_start:
{
if (lean_obj_tag(v_x_1231_) == 0)
{
lean_dec(v_b_1230_);
lean_dec_ref(v_a_1229_);
return v_x_1231_;
}
else
{
lean_object* v_key_1232_; lean_object* v_value_1233_; lean_object* v_tail_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1248_; 
v_key_1232_ = lean_ctor_get(v_x_1231_, 0);
v_value_1233_ = lean_ctor_get(v_x_1231_, 1);
v_tail_1234_ = lean_ctor_get(v_x_1231_, 2);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1231_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1236_ = v_x_1231_;
v_isShared_1237_ = v_isSharedCheck_1248_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_tail_1234_);
lean_inc(v_value_1233_);
lean_inc(v_key_1232_);
lean_dec(v_x_1231_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1248_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
size_t v_ptr_1238_; size_t v_ptr_1239_; uint8_t v___x_1240_; 
v_ptr_1238_ = lean_ctor_get_usize(v_key_1232_, 1);
v_ptr_1239_ = lean_ctor_get_usize(v_a_1229_, 1);
v___x_1240_ = lean_usize_dec_eq(v_ptr_1238_, v_ptr_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1229_, v_b_1230_, v_tail_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 2, v___x_1241_);
v___x_1243_ = v___x_1236_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_key_1232_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_value_1233_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
else
{
lean_object* v___x_1246_; 
lean_dec(v_value_1233_);
lean_dec(v_key_1232_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v_b_1230_);
lean_ctor_set(v___x_1236_, 0, v_a_1229_);
v___x_1246_ = v___x_1236_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1229_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_b_1230_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_tail_1234_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
return v_x_1249_;
}
else
{
lean_object* v_key_1251_; lean_object* v_value_1252_; lean_object* v_tail_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1277_; 
v_key_1251_ = lean_ctor_get(v_x_1250_, 0);
v_value_1252_ = lean_ctor_get(v_x_1250_, 1);
v_tail_1253_ = lean_ctor_get(v_x_1250_, 2);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_x_1250_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1255_ = v_x_1250_;
v_isShared_1256_ = v_isSharedCheck_1277_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_tail_1253_);
lean_inc(v_value_1252_);
lean_inc(v_key_1251_);
lean_dec(v_x_1250_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1277_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
size_t v_ptr_1257_; lean_object* v___x_1258_; uint64_t v___x_1259_; uint64_t v___x_1260_; uint64_t v___x_1261_; uint64_t v_fold_1262_; uint64_t v___x_1263_; uint64_t v___x_1264_; uint64_t v___x_1265_; size_t v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v_ptr_1257_ = lean_ctor_get_usize(v_key_1251_, 1);
v___x_1258_ = lean_array_get_size(v_x_1249_);
v___x_1259_ = lean_usize_to_uint64(v_ptr_1257_);
v___x_1260_ = 32ULL;
v___x_1261_ = lean_uint64_shift_right(v___x_1259_, v___x_1260_);
v_fold_1262_ = lean_uint64_xor(v___x_1259_, v___x_1261_);
v___x_1263_ = 16ULL;
v___x_1264_ = lean_uint64_shift_right(v_fold_1262_, v___x_1263_);
v___x_1265_ = lean_uint64_xor(v_fold_1262_, v___x_1264_);
v___x_1266_ = lean_uint64_to_usize(v___x_1265_);
v___x_1267_ = lean_usize_of_nat(v___x_1258_);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_sub(v___x_1267_, v___x_1268_);
v___x_1270_ = lean_usize_land(v___x_1266_, v___x_1269_);
v___x_1271_ = lean_array_uget_borrowed(v_x_1249_, v___x_1270_);
lean_inc(v___x_1271_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 2, v___x_1271_);
v___x_1273_ = v___x_1255_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_key_1251_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_value_1252_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_array_uset(v_x_1249_, v___x_1270_, v___x_1273_);
v_x_1249_ = v___x_1274_;
v_x_1250_ = v_tail_1253_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(lean_object* v_i_1278_, lean_object* v_source_1279_, lean_object* v_target_1280_){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_array_get_size(v_source_1279_);
v___x_1282_ = lean_nat_dec_lt(v_i_1278_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec_ref(v_source_1279_);
lean_dec(v_i_1278_);
return v_target_1280_;
}
else
{
lean_object* v_es_1283_; lean_object* v___x_1284_; lean_object* v_source_1285_; lean_object* v_target_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_es_1283_ = lean_array_fget(v_source_1279_, v_i_1278_);
v___x_1284_ = lean_box(0);
v_source_1285_ = lean_array_fset(v_source_1279_, v_i_1278_, v___x_1284_);
v_target_1286_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_target_1280_, v_es_1283_);
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_add(v_i_1278_, v___x_1287_);
lean_dec(v_i_1278_);
v_i_1278_ = v___x_1288_;
v_source_1279_ = v_source_1285_;
v_target_1280_ = v_target_1286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(lean_object* v_data_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_nbuckets_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1291_ = lean_array_get_size(v_data_1290_);
v___x_1292_ = lean_unsigned_to_nat(2u);
v_nbuckets_1293_ = lean_nat_mul(v___x_1291_, v___x_1292_);
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_mk_array(v_nbuckets_1293_, v___x_1295_);
v___x_1297_ = lean_array_propagate_mark(v_data_1290_, v___x_1296_);
v___x_1298_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v___x_1294_, v_data_1290_, v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(lean_object* v_a_1299_, lean_object* v_x_1300_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 0)
{
uint8_t v___x_1301_; 
v___x_1301_ = 0;
return v___x_1301_;
}
else
{
lean_object* v_key_1302_; lean_object* v_tail_1303_; size_t v_ptr_1304_; size_t v_ptr_1305_; uint8_t v___x_1306_; 
v_key_1302_ = lean_ctor_get(v_x_1300_, 0);
v_tail_1303_ = lean_ctor_get(v_x_1300_, 2);
v_ptr_1304_ = lean_ctor_get_usize(v_key_1302_, 1);
v_ptr_1305_ = lean_ctor_get_usize(v_a_1299_, 1);
v___x_1306_ = lean_usize_dec_eq(v_ptr_1304_, v_ptr_1305_);
if (v___x_1306_ == 0)
{
v_x_1300_ = v_tail_1303_;
goto _start;
}
else
{
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg___boxed(lean_object* v_a_1308_, lean_object* v_x_1309_){
_start:
{
uint8_t v_res_1310_; lean_object* v_r_1311_; 
v_res_1310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1308_, v_x_1309_);
lean_dec(v_x_1309_);
lean_dec_ref(v_a_1308_);
v_r_1311_ = lean_box(v_res_1310_);
return v_r_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(lean_object* v_m_1312_, lean_object* v_a_1313_, lean_object* v_b_1314_){
_start:
{
lean_object* v_size_1315_; lean_object* v_buckets_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1360_; 
v_size_1315_ = lean_ctor_get(v_m_1312_, 0);
v_buckets_1316_ = lean_ctor_get(v_m_1312_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_m_1312_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1318_ = v_m_1312_;
v_isShared_1319_ = v_isSharedCheck_1360_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_buckets_1316_);
lean_inc(v_size_1315_);
lean_dec(v_m_1312_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1360_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
size_t v_ptr_1320_; lean_object* v___x_1321_; uint64_t v___x_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v_fold_1325_; uint64_t v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; lean_object* v_bkt_1334_; uint8_t v___x_1335_; 
v_ptr_1320_ = lean_ctor_get_usize(v_a_1313_, 1);
v___x_1321_ = lean_array_get_size(v_buckets_1316_);
v___x_1322_ = lean_usize_to_uint64(v_ptr_1320_);
v___x_1323_ = 32ULL;
v___x_1324_ = lean_uint64_shift_right(v___x_1322_, v___x_1323_);
v_fold_1325_ = lean_uint64_xor(v___x_1322_, v___x_1324_);
v___x_1326_ = 16ULL;
v___x_1327_ = lean_uint64_shift_right(v_fold_1325_, v___x_1326_);
v___x_1328_ = lean_uint64_xor(v_fold_1325_, v___x_1327_);
v___x_1329_ = lean_uint64_to_usize(v___x_1328_);
v___x_1330_ = lean_usize_of_nat(v___x_1321_);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_sub(v___x_1330_, v___x_1331_);
v___x_1333_ = lean_usize_land(v___x_1329_, v___x_1332_);
v_bkt_1334_ = lean_array_uget_borrowed(v_buckets_1316_, v___x_1333_);
v___x_1335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1313_, v_bkt_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v_size_x27_1337_; lean_object* v___x_1338_; lean_object* v_buckets_x27_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1336_ = lean_unsigned_to_nat(1u);
v_size_x27_1337_ = lean_nat_add(v_size_1315_, v___x_1336_);
lean_dec(v_size_1315_);
lean_inc(v_bkt_1334_);
v___x_1338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1338_, 0, v_a_1313_);
lean_ctor_set(v___x_1338_, 1, v_b_1314_);
lean_ctor_set(v___x_1338_, 2, v_bkt_1334_);
v_buckets_x27_1339_ = lean_array_uset(v_buckets_1316_, v___x_1333_, v___x_1338_);
v___x_1340_ = lean_unsigned_to_nat(4u);
v___x_1341_ = lean_nat_mul(v_size_x27_1337_, v___x_1340_);
v___x_1342_ = lean_unsigned_to_nat(3u);
v___x_1343_ = lean_nat_div(v___x_1341_, v___x_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_array_get_size(v_buckets_x27_1339_);
v___x_1345_ = lean_nat_dec_le(v___x_1343_, v___x_1344_);
lean_dec(v___x_1343_);
if (v___x_1345_ == 0)
{
lean_object* v_val_1346_; lean_object* v___x_1348_; 
v_val_1346_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_buckets_x27_1339_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v_val_1346_);
lean_ctor_set(v___x_1318_, 0, v_size_x27_1337_);
v___x_1348_ = v___x_1318_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_size_x27_1337_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_val_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
else
{
lean_object* v___x_1351_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v_buckets_x27_1339_);
lean_ctor_set(v___x_1318_, 0, v_size_x27_1337_);
v___x_1351_ = v___x_1318_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_size_x27_1337_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_buckets_x27_1339_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_object* v___x_1353_; lean_object* v_buckets_x27_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_inc(v_bkt_1334_);
v___x_1353_ = lean_box(0);
v_buckets_x27_1354_ = lean_array_uset(v_buckets_1316_, v___x_1333_, v___x_1353_);
v___x_1355_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1313_, v_b_1314_, v_bkt_1334_);
v___x_1356_ = lean_array_uset(v_buckets_x27_1354_, v___x_1333_, v___x_1355_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v___x_1356_);
v___x_1358_ = v___x_1318_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_size_1315_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___y_1364_; 
switch(lean_obj_tag(v_a_1361_))
{
case 1:
{
lean_dec_ref_known(v_a_1361_, 2);
v___y_1364_ = v_a_1362_;
goto v___jp_1363_;
}
case 2:
{
lean_dec_ref_known(v_a_1361_, 2);
v___y_1364_ = v_a_1362_;
goto v___jp_1363_;
}
case 3:
{
lean_object* v_id_1368_; lean_object* v_d_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_id_1368_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_id_1368_);
v_d_1369_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_d_1369_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1370_ = l_Lean_Fmt_multiLineRawTagId;
v___x_1371_ = lean_nat_dec_eq(v_id_1368_, v___x_1370_);
lean_dec(v_id_1368_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
v___x_1372_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1369_, v_a_1362_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec(v_d_1369_);
v___x_1373_ = lean_box(v___x_1371_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
lean_ctor_set(v___x_1374_, 1, v_a_1362_);
return v___x_1374_;
}
}
case 4:
{
lean_object* v_d_1375_; lean_object* v___x_1376_; 
v_d_1375_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1375_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1376_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1375_, v_a_1362_);
return v___x_1376_;
}
case 5:
{
lean_object* v_d_1377_; lean_object* v___x_1378_; 
v_d_1377_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1377_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1378_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1377_, v_a_1362_);
return v___x_1378_;
}
case 6:
{
lean_object* v_d_1379_; lean_object* v___x_1380_; 
v_d_1379_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_d_1379_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1380_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1379_, v_a_1362_);
return v___x_1380_;
}
case 7:
{
uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref_known(v_a_1361_, 2);
v___x_1381_ = 1;
v___x_1382_ = lean_box(v___x_1381_);
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v_a_1362_);
return v___x_1383_;
}
case 8:
{
lean_object* v_d_1384_; lean_object* v___x_1385_; 
v_d_1384_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1384_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1385_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1384_, v_a_1362_);
return v___x_1385_;
}
case 9:
{
lean_object* v_d_1386_; lean_object* v___x_1387_; 
v_d_1386_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1386_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1387_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1386_, v_a_1362_);
return v___x_1387_;
}
case 10:
{
lean_object* v_d_1388_; lean_object* v___x_1389_; 
v_d_1388_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1388_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1389_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1388_, v_a_1362_);
return v___x_1389_;
}
case 11:
{
lean_object* v_d_1390_; lean_object* v___x_1391_; 
v_d_1390_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1390_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1391_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1390_, v_a_1362_);
return v___x_1391_;
}
case 12:
{
lean_object* v_d_1392_; lean_object* v___x_1393_; 
v_d_1392_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_d_1392_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1393_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1392_, v_a_1362_);
return v___x_1393_;
}
case 13:
{
lean_object* v_d_1394_; lean_object* v___x_1395_; 
v_d_1394_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_d_1394_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1395_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1394_, v_a_1362_);
return v___x_1395_;
}
case 14:
{
lean_object* v_a_1396_; lean_object* v_b_1397_; lean_object* v___x_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_a_1396_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_a_1396_);
v_b_1397_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_b_1397_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1398_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_a_1396_, v_a_1362_);
v_fst_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_fst_1399_);
v_snd_1400_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_snd_1400_);
lean_dec_ref(v___x_1398_);
v___x_1401_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_b_1397_, v_snd_1400_);
v___x_1402_ = lean_unbox(v_fst_1399_);
if (v___x_1402_ == 0)
{
lean_object* v_snd_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_snd_1403_ = lean_ctor_get(v___x_1401_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; 
v_unused_1411_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1411_);
v___x_1405_ = v___x_1401_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_snd_1403_);
lean_dec(v___x_1401_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v_fst_1399_);
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_fst_1399_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_snd_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_dec(v_fst_1399_);
return v___x_1401_;
}
}
default: 
{
uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec(v_a_1361_);
v___x_1412_ = 0;
v___x_1413_ = lean_box(v___x_1412_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v_a_1362_);
return v___x_1414_;
}
}
v___jp_1363_:
{
uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = 0;
v___x_1366_ = lean_box(v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v___y_1364_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(lean_object* v_v_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_cacheKey_1417_; lean_object* v___x_1418_; 
lean_inc(v_v_1415_);
v_cacheKey_1417_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1415_);
v___x_1418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_a_1416_, v_cacheKey_1417_);
if (lean_obj_tag(v___x_1418_) == 1)
{
lean_object* v_val_1419_; lean_object* v___x_1420_; 
lean_dec_ref(v_cacheKey_1417_);
lean_dec(v_v_1415_);
v_val_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v_val_1419_);
lean_ctor_set(v___x_1420_, 1, v_a_1416_);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; lean_object* v_fst_1422_; lean_object* v_snd_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v___x_1418_);
v___x_1421_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_v_1415_, v_a_1416_);
v_fst_1422_ = lean_ctor_get(v___x_1421_, 0);
v_snd_1423_ = lean_ctor_get(v___x_1421_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1425_ = v___x_1421_;
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_snd_1423_);
lean_inc(v_fst_1422_);
lean_dec(v___x_1421_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_inc(v_fst_1422_);
v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_snd_1423_, v_cacheKey_1417_, v_fst_1422_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 1, v___x_1427_);
v___x_1429_ = v___x_1425_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_fst_1422_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go(lean_object* v_00_u03c4_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_a_1433_, v_a_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized(lean_object* v_00_u03c4_1436_, lean_object* v_v_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1437_, v_a_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(lean_object* v_00_u03c4_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_m_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1442_, v_a_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___boxed(lean_object* v_00_u03c4_1445_, lean_object* v_00_u03b2_1446_, lean_object* v_m_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(v_00_u03c4_1445_, v_00_u03b2_1446_, v_m_1447_, v_a_1448_);
lean_dec_ref(v_a_1448_);
lean_dec_ref(v_m_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1(lean_object* v_00_u03c4_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_m_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_m_1452_, v_a_1453_, v_b_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(lean_object* v_00_u03c4_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_a_1458_, lean_object* v_x_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1458_, v_x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___boxed(lean_object* v_00_u03c4_1461_, lean_object* v_00_u03b2_1462_, lean_object* v_a_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(v_00_u03c4_1461_, v_00_u03b2_1462_, v_a_1463_, v_x_1464_);
lean_dec(v_x_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(lean_object* v_00_u03c4_1466_, lean_object* v_00_u03b2_1467_, lean_object* v_a_1468_, lean_object* v_x_1469_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1468_, v_x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___boxed(lean_object* v_00_u03c4_1471_, lean_object* v_00_u03b2_1472_, lean_object* v_a_1473_, lean_object* v_x_1474_){
_start:
{
uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(v_00_u03c4_1471_, v_00_u03b2_1472_, v_a_1473_, v_x_1474_);
lean_dec(v_x_1474_);
lean_dec_ref(v_a_1473_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4(lean_object* v_00_u03c4_1477_, lean_object* v_00_u03b2_1478_, lean_object* v_data_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_data_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5(lean_object* v_00_u03c4_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_a_1483_, lean_object* v_b_1484_, lean_object* v_x_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1483_, v_b_1484_, v_x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5(lean_object* v_00_u03c4_1487_, lean_object* v_00_u03b2_1488_, lean_object* v_i_1489_, lean_object* v_source_1490_, lean_object* v_target_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v_i_1489_, v_source_1490_, v_target_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03c4_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_x_1495_, v_x_1496_);
return v___x_1497_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_isAligned___redArg___closed__0(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_unsigned_to_nat(16u);
v___x_1500_ = lean_mk_array(v___x_1499_, v___x_1498_);
return v___x_1500_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_isAligned___redArg___closed__1(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = lean_obj_once(&l_Lean_Fmt_Layouts_isAligned___redArg___closed__0, &l_Lean_Fmt_Layouts_isAligned___redArg___closed__0_once, _init_l_Lean_Fmt_Layouts_isAligned___redArg___closed__0);
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
lean_ctor_set(v___x_1503_, 1, v___x_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_isAligned___redArg(lean_object* v_v_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_fst_1507_; 
v___x_1505_ = lean_obj_once(&l_Lean_Fmt_Layouts_isAligned___redArg___closed__1, &l_Lean_Fmt_Layouts_isAligned___redArg___closed__1_once, _init_l_Lean_Fmt_Layouts_isAligned___redArg___closed__1);
v___x_1506_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1504_, v___x_1505_);
v_fst_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_fst_1507_);
lean_dec_ref(v___x_1506_);
return v_fst_1507_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_isAligned(lean_object* v_00_u03c4_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_v_1511_){
_start:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = l_Lean_Fmt_Layouts_isAligned___redArg(v_v_1511_);
v___x_1513_ = lean_unbox(v___x_1512_);
lean_dec(v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_isAligned___boxed(lean_object* v_00_u03c4_1514_, lean_object* v_inst_1515_, lean_object* v_inst_1516_, lean_object* v_v_1517_){
_start:
{
uint8_t v_res_1518_; lean_object* v_r_1519_; 
v_res_1518_ = l_Lean_Fmt_Layouts_isAligned(v_00_u03c4_1514_, v_inst_1515_, v_inst_1516_, v_v_1517_);
lean_dec_ref(v_inst_1516_);
lean_dec_ref(v_inst_1515_);
v_r_1519_ = lean_box(v_res_1518_);
return v_r_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___impl(uint8_t v_x_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_box(v_x_1520_);
v___x_1522_ = lean_obj_tag_nat(v___x_1521_);
lean_dec(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___impl___boxed(lean_object* v_x_1523_){
_start:
{
uint8_t v_x_4__boxed_1524_; lean_object* v_res_1525_; 
v_x_4__boxed_1524_ = lean_unbox(v_x_1523_);
v_res_1525_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___impl(v_x_4__boxed_1524_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(lean_object* v_k_1526_){
_start:
{
lean_inc(v_k_1526_);
return v_k_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(v_k_1527_);
lean_dec(v_k_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(lean_object* v_motive_1529_, lean_object* v_ctorIdx_1530_, uint8_t v_t_1531_, lean_object* v_h_1532_, lean_object* v_k_1533_){
_start:
{
lean_inc(v_k_1533_);
return v_k_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1534_, lean_object* v_ctorIdx_1535_, lean_object* v_t_1536_, lean_object* v_h_1537_, lean_object* v_k_1538_){
_start:
{
uint8_t v_t_boxed_1539_; lean_object* v_res_1540_; 
v_t_boxed_1539_ = lean_unbox(v_t_1536_);
v_res_1540_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(v_motive_1534_, v_ctorIdx_1535_, v_t_boxed_1539_, v_h_1537_, v_k_1538_);
lean_dec(v_k_1538_);
lean_dec(v_ctorIdx_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1541_){
_start:
{
lean_inc(v_withoutSpacing_1541_);
return v_withoutSpacing_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1542_);
lean_dec(v_withoutSpacing_1542_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1544_, uint8_t v_t_1545_, lean_object* v_h_1546_, lean_object* v_withoutSpacing_1547_){
_start:
{
lean_inc(v_withoutSpacing_1547_);
return v_withoutSpacing_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1548_, lean_object* v_t_1549_, lean_object* v_h_1550_, lean_object* v_withoutSpacing_1551_){
_start:
{
uint8_t v_t_boxed_1552_; lean_object* v_res_1553_; 
v_t_boxed_1552_ = lean_unbox(v_t_1549_);
v_res_1553_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(v_motive_1548_, v_t_boxed_1552_, v_h_1550_, v_withoutSpacing_1551_);
lean_dec(v_withoutSpacing_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(lean_object* v_withoutSpacingIfAtomic_1554_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1554_);
return v_withoutSpacingIfAtomic_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg___boxed(lean_object* v_withoutSpacingIfAtomic_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(v_withoutSpacingIfAtomic_1555_);
lean_dec(v_withoutSpacingIfAtomic_1555_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(lean_object* v_motive_1557_, uint8_t v_t_1558_, lean_object* v_h_1559_, lean_object* v_withoutSpacingIfAtomic_1560_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1560_);
return v_withoutSpacingIfAtomic_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___boxed(lean_object* v_motive_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_withoutSpacingIfAtomic_1564_){
_start:
{
uint8_t v_t_boxed_1565_; lean_object* v_res_1566_; 
v_t_boxed_1565_ = lean_unbox(v_t_1562_);
v_res_1566_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(v_motive_1561_, v_t_boxed_1565_, v_h_1563_, v_withoutSpacingIfAtomic_1564_);
lean_dec(v_withoutSpacingIfAtomic_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1567_){
_start:
{
lean_inc(v_withSpacing_1567_);
return v_withSpacing_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1568_);
lean_dec(v_withSpacing_1568_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(lean_object* v_motive_1570_, uint8_t v_t_1571_, lean_object* v_h_1572_, lean_object* v_withSpacing_1573_){
_start:
{
lean_inc(v_withSpacing_1573_);
return v_withSpacing_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_withSpacing_1577_){
_start:
{
uint8_t v_t_boxed_1578_; lean_object* v_res_1579_; 
v_t_boxed_1578_ = lean_unbox(v_t_1575_);
v_res_1579_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(v_motive_1574_, v_t_boxed_1578_, v_h_1576_, v_withSpacing_1577_);
lean_dec(v_withSpacing_1577_);
return v_res_1579_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_unsigned_to_nat(16u);
v___x_1582_ = lean_mk_array(v___x_1581_, v___x_1580_);
return v___x_1582_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = lean_obj_once(&l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0, &l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once, _init_l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0);
v___x_1584_ = lean_unsigned_to_nat(0u);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object* v_v_1586_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_fst_1589_; uint8_t v___x_1590_; 
v___x_1587_ = lean_obj_once(&l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1, &l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once, _init_l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1);
v___x_1588_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1586_, v___x_1587_);
v_fst_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_fst_1589_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = lean_unbox(v_fst_1589_);
lean_dec(v_fst_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object* v_v_1591_){
_start:
{
uint8_t v_res_1592_; lean_object* v_r_1593_; 
v_res_1592_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_v_1591_);
v_r_1593_ = lean_box(v_res_1592_);
return v_r_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object* v_prefixOperatorTk_1594_, lean_object* v_operand_1595_, uint8_t v_format_1596_){
_start:
{
uint8_t v___x_1597_; lean_object* v___y_1599_; 
v___x_1597_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_prefixOperatorTk_1594_);
if (v___x_1597_ == 0)
{
if (v_format_1596_ == 0)
{
goto v___jp_1603_;
}
else
{
if (v_format_1596_ == 1)
{
uint8_t v___x_1619_; 
v___x_1619_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_operand_1595_);
if (v___x_1619_ == 0)
{
uint8_t v___x_1620_; 
lean_inc_ref(v_operand_1595_);
v___x_1620_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_operand_1595_);
if (v___x_1620_ == 0)
{
goto v___jp_1610_;
}
else
{
goto v___jp_1617_;
}
}
else
{
goto v___jp_1617_;
}
}
else
{
goto v___jp_1610_;
}
}
}
else
{
lean_dec_ref(v_prefixOperatorTk_1594_);
return v_operand_1595_;
}
v___jp_1598_:
{
lean_object* v_doc_1600_; uint8_t v___x_1601_; 
v_doc_1600_ = lean_ctor_get(v_operand_1595_, 0);
lean_inc(v_doc_1600_);
lean_dec_ref(v_operand_1595_);
v___x_1601_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1600_);
if (v___x_1601_ == 0)
{
return v___y_1599_;
}
else
{
lean_object* v_doc_1602_; 
v_doc_1602_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___y_1599_, v___x_1597_);
return v_doc_1602_;
}
}
v___jp_1603_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1604_ = lean_unsigned_to_nat(2u);
v___x_1605_ = lean_mk_empty_array_with_capacity(v___x_1604_);
v___x_1606_ = lean_array_push(v___x_1605_, v_prefixOperatorTk_1594_);
lean_inc_ref(v_operand_1595_);
v___x_1607_ = lean_array_push(v___x_1606_, v_operand_1595_);
v___x_1608_ = l_Lean_Fmt_Layouts_atomic(v___x_1607_);
lean_dec_ref(v___x_1607_);
v___x_1609_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1608_);
v___y_1599_ = v___x_1609_;
goto v___jp_1598_;
}
v___jp_1610_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1611_ = lean_unsigned_to_nat(2u);
v___x_1612_ = lean_mk_empty_array_with_capacity(v___x_1611_);
v___x_1613_ = lean_array_push(v___x_1612_, v_prefixOperatorTk_1594_);
lean_inc_ref(v_operand_1595_);
v___x_1614_ = lean_array_push(v___x_1613_, v_operand_1595_);
v___x_1615_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1614_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1615_);
v___y_1599_ = v___x_1616_;
goto v___jp_1598_;
}
v___jp_1617_:
{
uint8_t v___x_1618_; 
lean_inc_ref(v_operand_1595_);
v___x_1618_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_operand_1595_);
if (v___x_1618_ == 0)
{
goto v___jp_1603_;
}
else
{
goto v___jp_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator___boxed(lean_object* v_prefixOperatorTk_1621_, lean_object* v_operand_1622_, lean_object* v_format_1623_){
_start:
{
uint8_t v_format_boxed_1624_; lean_object* v_res_1625_; 
v_format_boxed_1624_ = lean_unbox(v_format_1623_);
v_res_1625_ = l_Lean_Fmt_Layouts_prefixOperator(v_prefixOperatorTk_1621_, v_operand_1622_, v_format_boxed_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___impl(uint8_t v_x_1626_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_box(v_x_1626_);
v___x_1628_ = lean_obj_tag_nat(v___x_1627_);
lean_dec(v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___impl___boxed(lean_object* v_x_1629_){
_start:
{
uint8_t v_x_4__boxed_1630_; lean_object* v_res_1631_; 
v_x_4__boxed_1630_ = lean_unbox(v_x_1629_);
v_res_1631_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___impl(v_x_4__boxed_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(lean_object* v_k_1632_){
_start:
{
lean_inc(v_k_1632_);
return v_k_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(v_k_1633_);
lean_dec(v_k_1633_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(lean_object* v_motive_1635_, lean_object* v_ctorIdx_1636_, uint8_t v_t_1637_, lean_object* v_h_1638_, lean_object* v_k_1639_){
_start:
{
lean_inc(v_k_1639_);
return v_k_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1640_, lean_object* v_ctorIdx_1641_, lean_object* v_t_1642_, lean_object* v_h_1643_, lean_object* v_k_1644_){
_start:
{
uint8_t v_t_boxed_1645_; lean_object* v_res_1646_; 
v_t_boxed_1645_ = lean_unbox(v_t_1642_);
v_res_1646_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(v_motive_1640_, v_ctorIdx_1641_, v_t_boxed_1645_, v_h_1643_, v_k_1644_);
lean_dec(v_k_1644_);
lean_dec(v_ctorIdx_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1647_){
_start:
{
lean_inc(v_withoutSpacing_1647_);
return v_withoutSpacing_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1648_);
lean_dec(v_withoutSpacing_1648_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1650_, uint8_t v_t_1651_, lean_object* v_h_1652_, lean_object* v_withoutSpacing_1653_){
_start:
{
lean_inc(v_withoutSpacing_1653_);
return v_withoutSpacing_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1654_, lean_object* v_t_1655_, lean_object* v_h_1656_, lean_object* v_withoutSpacing_1657_){
_start:
{
uint8_t v_t_boxed_1658_; lean_object* v_res_1659_; 
v_t_boxed_1658_ = lean_unbox(v_t_1655_);
v_res_1659_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(v_motive_1654_, v_t_boxed_1658_, v_h_1656_, v_withoutSpacing_1657_);
lean_dec(v_withoutSpacing_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1660_){
_start:
{
lean_inc(v_withSpacing_1660_);
return v_withSpacing_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1661_);
lean_dec(v_withSpacing_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(lean_object* v_motive_1663_, uint8_t v_t_1664_, lean_object* v_h_1665_, lean_object* v_withSpacing_1666_){
_start:
{
lean_inc(v_withSpacing_1666_);
return v_withSpacing_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1667_, lean_object* v_t_1668_, lean_object* v_h_1669_, lean_object* v_withSpacing_1670_){
_start:
{
uint8_t v_t_boxed_1671_; lean_object* v_res_1672_; 
v_t_boxed_1671_ = lean_unbox(v_t_1668_);
v_res_1672_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(v_motive_1667_, v_t_boxed_1671_, v_h_1669_, v_withSpacing_1670_);
lean_dec(v_withSpacing_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object* v_operand_1673_, lean_object* v_postfixOperatorTk_1674_, uint8_t v_format_1675_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_postfixOperatorTk_1674_);
if (v___x_1676_ == 0)
{
if (v_format_1675_ == 1)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1677_ = lean_unsigned_to_nat(2u);
v___x_1678_ = lean_mk_empty_array_with_capacity(v___x_1677_);
v___x_1679_ = lean_array_push(v___x_1678_, v_operand_1673_);
v___x_1680_ = lean_array_push(v___x_1679_, v_postfixOperatorTk_1674_);
v___x_1681_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1680_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1681_);
return v___x_1682_;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1683_ = lean_unsigned_to_nat(2u);
v___x_1684_ = lean_mk_empty_array_with_capacity(v___x_1683_);
v___x_1685_ = lean_array_push(v___x_1684_, v_operand_1673_);
v___x_1686_ = lean_array_push(v___x_1685_, v_postfixOperatorTk_1674_);
v___x_1687_ = l_Lean_Fmt_Layouts_atomic(v___x_1686_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1687_);
return v___x_1688_;
}
}
else
{
lean_dec_ref(v_postfixOperatorTk_1674_);
return v_operand_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator___boxed(lean_object* v_operand_1689_, lean_object* v_postfixOperatorTk_1690_, lean_object* v_format_1691_){
_start:
{
uint8_t v_format_boxed_1692_; lean_object* v_res_1693_; 
v_format_boxed_1692_ = lean_unbox(v_format_1691_);
v_res_1693_ = l_Lean_Fmt_Layouts_postfixOperator(v_operand_1689_, v_postfixOperatorTk_1690_, v_format_boxed_1692_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___impl(lean_object* v_x_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_obj_tag_nat(v_x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___impl___boxed(lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___impl(v_x_1696_);
lean_dec_ref(v_x_1696_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(lean_object* v_t_1698_, lean_object* v_k_1699_){
_start:
{
if (lean_obj_tag(v_t_1698_) == 0)
{
uint8_t v_hardNestedFirstOperand_1700_; uint8_t v_trailingOperator_1701_; uint8_t v_spacing_1702_; uint8_t v_respectPseudoAlignment_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_hardNestedFirstOperand_1700_ = lean_ctor_get_uint8(v_t_1698_, 0);
v_trailingOperator_1701_ = lean_ctor_get_uint8(v_t_1698_, 1);
v_spacing_1702_ = lean_ctor_get_uint8(v_t_1698_, 2);
v_respectPseudoAlignment_1703_ = lean_ctor_get_uint8(v_t_1698_, 3);
v___x_1704_ = lean_box(v_hardNestedFirstOperand_1700_);
v___x_1705_ = lean_box(v_trailingOperator_1701_);
v___x_1706_ = lean_box(v_spacing_1702_);
v___x_1707_ = lean_box(v_respectPseudoAlignment_1703_);
v___x_1708_ = lean_apply_4(v_k_1699_, v___x_1704_, v___x_1705_, v___x_1706_, v___x_1707_);
return v___x_1708_;
}
else
{
uint8_t v_hardNestedFirstOperand_1709_; uint8_t v_trailingOperator_1710_; uint8_t v_spacing_1711_; uint8_t v_alignedOperators_1712_; uint8_t v_separateFinalOperand_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_hardNestedFirstOperand_1709_ = lean_ctor_get_uint8(v_t_1698_, 0);
v_trailingOperator_1710_ = lean_ctor_get_uint8(v_t_1698_, 1);
v_spacing_1711_ = lean_ctor_get_uint8(v_t_1698_, 2);
v_alignedOperators_1712_ = lean_ctor_get_uint8(v_t_1698_, 3);
v_separateFinalOperand_1713_ = lean_ctor_get_uint8(v_t_1698_, 4);
v___x_1714_ = lean_box(v_hardNestedFirstOperand_1709_);
v___x_1715_ = lean_box(v_trailingOperator_1710_);
v___x_1716_ = lean_box(v_spacing_1711_);
v___x_1717_ = lean_box(v_alignedOperators_1712_);
v___x_1718_ = lean_box(v_separateFinalOperand_1713_);
v___x_1719_ = lean_apply_5(v_k_1699_, v___x_1714_, v___x_1715_, v___x_1716_, v___x_1717_, v___x_1718_);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_t_1720_, lean_object* v_k_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1720_, v_k_1721_);
lean_dec_ref(v_t_1720_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(lean_object* v_motive_1723_, lean_object* v_ctorIdx_1724_, lean_object* v_t_1725_, lean_object* v_h_1726_, lean_object* v_k_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1725_, v_k_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1729_, lean_object* v_ctorIdx_1730_, lean_object* v_t_1731_, lean_object* v_h_1732_, lean_object* v_k_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(v_motive_1729_, v_ctorIdx_1730_, v_t_1731_, v_h_1732_, v_k_1733_);
lean_dec_ref(v_t_1731_);
lean_dec(v_ctorIdx_1730_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(lean_object* v_t_1735_, lean_object* v_dense_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1735_, v_dense_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg___boxed(lean_object* v_t_1738_, lean_object* v_dense_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(v_t_1738_, v_dense_1739_);
lean_dec_ref(v_t_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(lean_object* v_motive_1741_, lean_object* v_t_1742_, lean_object* v_h_1743_, lean_object* v_dense_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1742_, v_dense_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___boxed(lean_object* v_motive_1746_, lean_object* v_t_1747_, lean_object* v_h_1748_, lean_object* v_dense_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(v_motive_1746_, v_t_1747_, v_h_1748_, v_dense_1749_);
lean_dec_ref(v_t_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(lean_object* v_t_1751_, lean_object* v_sparse_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1751_, v_sparse_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg___boxed(lean_object* v_t_1754_, lean_object* v_sparse_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(v_t_1754_, v_sparse_1755_);
lean_dec_ref(v_t_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(lean_object* v_motive_1757_, lean_object* v_t_1758_, lean_object* v_h_1759_, lean_object* v_sparse_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1758_, v_sparse_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___boxed(lean_object* v_motive_1762_, lean_object* v_t_1763_, lean_object* v_h_1764_, lean_object* v_sparse_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(v_motive_1762_, v_t_1763_, v_h_1764_, v_sparse_1765_);
lean_dec_ref(v_t_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(lean_object* v_x_1767_){
_start:
{
uint8_t v_hardNestedFirstOperand_1768_; 
v_hardNestedFirstOperand_1768_ = lean_ctor_get_uint8(v_x_1767_, 0);
return v_hardNestedFirstOperand_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand___boxed(lean_object* v_x_1769_){
_start:
{
uint8_t v_res_1770_; lean_object* v_r_1771_; 
v_res_1770_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(v_x_1769_);
lean_dec_ref(v_x_1769_);
v_r_1771_ = lean_box(v_res_1770_);
return v_r_1771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(lean_object* v_x_1772_){
_start:
{
uint8_t v_trailingOperator_1773_; 
v_trailingOperator_1773_ = lean_ctor_get_uint8(v_x_1772_, 1);
return v_trailingOperator_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator___boxed(lean_object* v_x_1774_){
_start:
{
uint8_t v_res_1775_; lean_object* v_r_1776_; 
v_res_1775_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(v_x_1774_);
lean_dec_ref(v_x_1774_);
v_r_1776_ = lean_box(v_res_1775_);
return v_r_1776_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(lean_object* v_x_1777_){
_start:
{
uint8_t v_spacing_1778_; 
v_spacing_1778_ = lean_ctor_get_uint8(v_x_1777_, 2);
return v_spacing_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing___boxed(lean_object* v_x_1779_){
_start:
{
uint8_t v_res_1780_; lean_object* v_r_1781_; 
v_res_1780_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(v_x_1779_);
lean_dec_ref(v_x_1779_);
v_r_1781_ = lean_box(v_res_1780_);
return v_r_1781_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(lean_object* v_x_1782_){
_start:
{
if (lean_obj_tag(v_x_1782_) == 0)
{
uint8_t v___x_1783_; 
v___x_1783_ = 0;
return v___x_1783_;
}
else
{
uint8_t v_trailingOperator_1784_; 
v_trailingOperator_1784_ = lean_ctor_get_uint8(v_x_1782_, 1);
if (v_trailingOperator_1784_ == 0)
{
uint8_t v_alignedOperators_1785_; 
v_alignedOperators_1785_ = lean_ctor_get_uint8(v_x_1782_, 3);
return v_alignedOperators_1785_;
}
else
{
uint8_t v___x_1786_; 
v___x_1786_ = 0;
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators___boxed(lean_object* v_x_1787_){
_start:
{
uint8_t v_res_1788_; lean_object* v_r_1789_; 
v_res_1788_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_x_1787_);
lean_dec_ref(v_x_1787_);
v_r_1789_ = lean_box(v_res_1788_);
return v_r_1789_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
uint8_t v___x_1791_; 
v___x_1791_ = 0;
return v___x_1791_;
}
else
{
uint8_t v_trailingOperator_1792_; 
v_trailingOperator_1792_ = lean_ctor_get_uint8(v_x_1790_, 1);
if (v_trailingOperator_1792_ == 0)
{
uint8_t v_separateFinalOperand_1793_; 
v_separateFinalOperand_1793_ = lean_ctor_get_uint8(v_x_1790_, 4);
return v_separateFinalOperand_1793_;
}
else
{
uint8_t v___x_1794_; 
v___x_1794_ = 0;
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand___boxed(lean_object* v_x_1795_){
_start:
{
uint8_t v_res_1796_; lean_object* v_r_1797_; 
v_res_1796_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_x_1795_);
lean_dec_ref(v_x_1795_);
v_r_1797_ = lean_box(v_res_1796_);
return v_r_1797_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(lean_object* v_x_1798_){
_start:
{
if (lean_obj_tag(v_x_1798_) == 0)
{
uint8_t v_respectPseudoAlignment_1799_; 
v_respectPseudoAlignment_1799_ = lean_ctor_get_uint8(v_x_1798_, 3);
return v_respectPseudoAlignment_1799_;
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = 1;
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment___boxed(lean_object* v_x_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(v_x_1801_);
lean_dec_ref(v_x_1801_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_permitDenseLayout(lean_object* v_doc_1804_, uint8_t v_respectPseudoAlignment_1805_){
_start:
{
lean_object* v_pseudoAligned_x3f_1810_; 
lean_inc_ref(v_doc_1804_);
v_pseudoAligned_x3f_1810_ = l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(v_doc_1804_);
if (v_respectPseudoAlignment_1805_ == 0)
{
if (lean_obj_tag(v_pseudoAligned_x3f_1810_) == 0)
{
goto v___jp_1806_;
}
else
{
lean_object* v_val_1811_; uint8_t v___x_1812_; 
v_val_1811_ = lean_ctor_get(v_pseudoAligned_x3f_1810_, 0);
lean_inc(v_val_1811_);
lean_dec_ref_known(v_pseudoAligned_x3f_1810_, 1);
v___x_1812_ = lean_unbox(v_val_1811_);
lean_dec(v_val_1811_);
if (v___x_1812_ == 0)
{
goto v___jp_1806_;
}
else
{
lean_dec_ref(v_doc_1804_);
return v_respectPseudoAlignment_1805_;
}
}
}
else
{
if (lean_obj_tag(v_pseudoAligned_x3f_1810_) == 0)
{
lean_object* v_doc_1813_; uint8_t v___x_1814_; 
v_doc_1813_ = lean_ctor_get(v_doc_1804_, 0);
lean_inc(v_doc_1813_);
lean_dec_ref(v_doc_1804_);
v___x_1814_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1813_);
if (v___x_1814_ == 0)
{
return v_respectPseudoAlignment_1805_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = 0;
return v___x_1815_;
}
}
else
{
uint8_t v___x_1816_; 
lean_dec_ref_known(v_pseudoAligned_x3f_1810_, 1);
lean_dec_ref(v_doc_1804_);
v___x_1816_ = 0;
return v___x_1816_;
}
}
v___jp_1806_:
{
lean_object* v_doc_1807_; uint8_t v___x_1808_; 
v_doc_1807_ = lean_ctor_get(v_doc_1804_, 0);
lean_inc(v_doc_1807_);
lean_dec_ref(v_doc_1804_);
v___x_1808_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1807_);
if (v___x_1808_ == 0)
{
uint8_t v___x_1809_; 
v___x_1809_ = 1;
return v___x_1809_;
}
else
{
return v_respectPseudoAlignment_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_permitDenseLayout___boxed(lean_object* v_doc_1817_, lean_object* v_respectPseudoAlignment_1818_){
_start:
{
uint8_t v_respectPseudoAlignment_boxed_1819_; uint8_t v_res_1820_; lean_object* v_r_1821_; 
v_respectPseudoAlignment_boxed_1819_ = lean_unbox(v_respectPseudoAlignment_1818_);
v_res_1820_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_doc_1817_, v_respectPseudoAlignment_boxed_1819_);
v_r_1821_ = lean_box(v_res_1820_);
return v_r_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___lam__0(lean_object* v_wrap_1822_, lean_object* v_d_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_doc_1826_; 
v___x_1824_ = l_Lean_Fmt_TaggedDoc_untagged(v_d_1823_);
v___x_1825_ = lean_apply_1(v_wrap_1822_, v___x_1824_);
v_doc_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_doc_1826_);
lean_dec_ref(v___x_1825_);
return v_doc_1826_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_1827_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1828_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__0);
v___x_1829_ = lean_unsigned_to_nat(2u);
v___x_1830_ = lean_mk_empty_array_with_capacity(v___x_1829_);
v___x_1831_ = lean_array_push(v___x_1830_, v___x_1828_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0(lean_object* v_wrap_1832_, lean_object* v___y_1833_, lean_object* v_as_1834_, size_t v_sz_1835_, size_t v_i_1836_, lean_object* v_b_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_usize_dec_lt(v_i_1836_, v_sz_1835_);
if (v___x_1838_ == 0)
{
lean_dec(v___y_1833_);
lean_dec_ref(v_wrap_1832_);
return v_b_1837_;
}
else
{
lean_object* v_fst_1839_; lean_object* v_snd_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1877_; 
v_fst_1839_ = lean_ctor_get(v_b_1837_, 0);
v_snd_1840_ = lean_ctor_get(v_b_1837_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_b_1837_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1842_ = v_b_1837_;
v_isShared_1843_ = v_isSharedCheck_1877_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_snd_1840_);
lean_inc(v_fst_1839_);
lean_dec(v_b_1837_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1877_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v_a_1844_; lean_object* v_doc_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v_a_1844_ = lean_array_uget_borrowed(v_as_1834_, v_i_1836_);
v_doc_1845_ = lean_ctor_get(v_a_1844_, 0);
v___x_1846_ = lean_unsigned_to_nat(2u);
v___x_1847_ = lean_mk_empty_array_with_capacity(v___x_1846_);
v___x_1848_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___closed__1);
v___x_1849_ = lean_array_push(v___x_1848_, v_snd_1840_);
v___x_1850_ = l_Lean_Fmt_Doc_join___redArg(v___x_1849_);
lean_inc_ref_n(v_wrap_1832_, 2);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___lam__0(v_wrap_1832_, v___x_1850_);
lean_inc_n(v_doc_1845_, 2);
v___x_1852_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_doc_1845_);
lean_inc(v___y_1833_);
lean_inc_ref_n(v___x_1847_, 4);
v___x_1853_ = lean_array_push(v___x_1847_, v___y_1833_);
v___x_1854_ = lean_array_push(v___x_1853_, v_fst_1839_);
v___x_1855_ = l_Lean_Fmt_Doc_join___redArg(v___x_1854_);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___lam__0(v_wrap_1832_, v___x_1855_);
v___x_1857_ = lean_array_push(v___x_1847_, v___x_1852_);
lean_inc_ref(v___x_1857_);
v___x_1858_ = lean_array_push(v___x_1857_, v___x_1856_);
v___x_1859_ = l_Lean_Fmt_Doc_join___redArg(v___x_1858_);
lean_inc(v___x_1851_);
v___x_1860_ = lean_array_push(v___x_1857_, v___x_1851_);
v___x_1861_ = l_Lean_Fmt_Doc_join___redArg(v___x_1860_);
v___x_1862_ = lean_array_push(v___x_1847_, v___x_1859_);
v___x_1863_ = lean_array_push(v___x_1862_, v___x_1861_);
v___x_1864_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_1863_);
v___x_1865_ = lean_array_push(v___x_1847_, v_doc_1845_);
v___x_1866_ = lean_array_push(v___x_1865_, v___x_1851_);
v___x_1867_ = l_Lean_Fmt_Doc_join___redArg(v___x_1866_);
lean_inc(v___x_1864_);
v___x_1868_ = lean_array_push(v___x_1847_, v___x_1864_);
v___x_1869_ = lean_array_push(v___x_1868_, v___x_1867_);
v___x_1870_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_1869_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 1, v___x_1870_);
lean_ctor_set(v___x_1842_, 0, v___x_1864_);
v___x_1872_ = v___x_1842_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
size_t v___x_1873_; size_t v___x_1874_; 
v___x_1873_ = ((size_t)1ULL);
v___x_1874_ = lean_usize_add(v_i_1836_, v___x_1873_);
v_i_1836_ = v___x_1874_;
v_b_1837_ = v___x_1872_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0___boxed(lean_object* v_wrap_1878_, lean_object* v___y_1879_, lean_object* v_as_1880_, lean_object* v_sz_1881_, lean_object* v_i_1882_, lean_object* v_b_1883_){
_start:
{
size_t v_sz_boxed_1884_; size_t v_i_boxed_1885_; lean_object* v_res_1886_; 
v_sz_boxed_1884_ = lean_unbox_usize(v_sz_1881_);
lean_dec(v_sz_1881_);
v_i_boxed_1885_ = lean_unbox_usize(v_i_1882_);
lean_dec(v_i_1882_);
v_res_1886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0(v_wrap_1878_, v___y_1879_, v_as_1880_, v_sz_boxed_1884_, v_i_boxed_1885_, v_b_1883_);
lean_dec_ref(v_as_1880_);
return v_res_1886_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__0(void){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_Fmt_Doc_empty___redArg();
return v___x_1887_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__2(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__1));
v___x_1890_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline(lean_object* v_format_1891_, lean_object* v_docs_1892_, lean_object* v_wrap_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v___y_1896_; uint8_t v___y_1918_; lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1894_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1921_ = lean_array_get_size(v_docs_1892_);
v___x_1922_ = lean_unsigned_to_nat(1u);
v___x_1923_ = lean_nat_dec_eq(v___x_1921_, v___x_1922_);
if (v___x_1923_ == 0)
{
uint8_t v_spacing_1924_; 
v_spacing_1924_ = lean_ctor_get_uint8(v_format_1891_, 2);
v___y_1918_ = v_spacing_1924_;
goto v___jp_1917_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref(v_wrap_1893_);
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = lean_array_get(v___x_1894_, v_docs_1892_, v___x_1925_);
lean_dec_ref(v_docs_1892_);
return v___x_1926_;
}
v___jp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_doc_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1915_; 
v___x_1897_ = lean_array_get_size(v_docs_1892_);
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = lean_nat_sub(v___x_1897_, v___x_1898_);
v___x_1900_ = lean_array_get(v___x_1894_, v_docs_1892_, v___x_1899_);
lean_dec(v___x_1899_);
v_doc_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v___x_1900_, 1);
lean_dec(v_unused_1916_);
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_doc_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1905_ = lean_array_pop(v_docs_1892_);
v___x_1906_ = l_Array_reverse___redArg(v___x_1905_);
lean_inc(v_doc_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 1, v_doc_1901_);
v___x_1908_ = v___x_1903_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_doc_1901_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_doc_1901_);
v___x_1908_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
size_t v_sz_1909_; size_t v___x_1910_; lean_object* v___x_1911_; lean_object* v_snd_1912_; lean_object* v___x_1913_; 
v_sz_1909_ = lean_array_size(v___x_1906_);
v___x_1910_ = ((size_t)0ULL);
lean_inc(v___y_1896_);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline_spec__0(v_wrap_1893_, v___y_1896_, v___x_1906_, v_sz_1909_, v___x_1910_, v___x_1908_);
lean_dec_ref(v___x_1906_);
v_snd_1912_ = lean_ctor_get(v___x_1911_, 1);
lean_inc(v_snd_1912_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = l_Lean_Fmt_TaggedDoc_untagged(v_snd_1912_);
return v___x_1913_;
}
}
}
v___jp_1917_:
{
if (v___y_1918_ == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__0);
v___y_1896_ = v___x_1919_;
goto v___jp_1895_;
}
else
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__2, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___closed__2);
v___y_1896_ = v___x_1920_;
goto v___jp_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline___boxed(lean_object* v_format_1927_, lean_object* v_docs_1928_, lean_object* v_wrap_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline(v_format_1927_, v_docs_1928_, v_wrap_1929_);
lean_dec_ref(v_format_1927_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object* v_format_1931_, lean_object* v_docs_1932_){
_start:
{
uint8_t v___y_1934_; uint8_t v_spacing_1937_; 
v_spacing_1937_ = lean_ctor_get_uint8(v_format_1931_, 2);
v___y_1934_ = v_spacing_1937_;
goto v___jp_1933_;
v___jp_1933_:
{
if (v___y_1934_ == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_Fmt_Layouts_atomic(v_docs_1932_);
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_Fmt_Layouts_spacedAtomic(v_docs_1932_);
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object* v_format_1938_, lean_object* v_docs_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1938_, v_docs_1939_);
lean_dec_ref(v_docs_1939_);
lean_dec_ref(v_format_1938_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object* v_msg_1941_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_1943_ = lean_panic_fn_borrowed(v___x_1942_, v_msg_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t v_a_1944_, lean_object* v_as_1945_, size_t v_i_1946_, size_t v_stop_1947_){
_start:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_usize_dec_eq(v_i_1946_, v_stop_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; uint8_t v___x_1950_; uint8_t v___x_1951_; 
v___x_1949_ = lean_array_uget_borrowed(v_as_1945_, v_i_1946_);
v___x_1950_ = lean_unbox(v___x_1949_);
v___x_1951_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_a_1944_, v___x_1950_);
if (v___x_1951_ == 0)
{
size_t v___x_1952_; size_t v___x_1953_; 
v___x_1952_ = ((size_t)1ULL);
v___x_1953_ = lean_usize_add(v_i_1946_, v___x_1952_);
v_i_1946_ = v___x_1953_;
goto _start;
}
else
{
return v___x_1951_;
}
}
else
{
uint8_t v___x_1955_; 
v___x_1955_ = 0;
return v___x_1955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object* v_a_1956_, lean_object* v_as_1957_, lean_object* v_i_1958_, lean_object* v_stop_1959_){
_start:
{
uint8_t v_a_boxed_1960_; size_t v_i_boxed_1961_; size_t v_stop_boxed_1962_; uint8_t v_res_1963_; lean_object* v_r_1964_; 
v_a_boxed_1960_ = lean_unbox(v_a_1956_);
v_i_boxed_1961_ = lean_unbox_usize(v_i_1958_);
lean_dec(v_i_1958_);
v_stop_boxed_1962_ = lean_unbox_usize(v_stop_1959_);
lean_dec(v_stop_1959_);
v_res_1963_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_boxed_1960_, v_as_1957_, v_i_boxed_1961_, v_stop_boxed_1962_);
lean_dec_ref(v_as_1957_);
v_r_1964_ = lean_box(v_res_1963_);
return v_r_1964_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object* v_as_1965_, uint8_t v_a_1966_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_array_get_size(v_as_1965_);
v___x_1969_ = lean_nat_dec_lt(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
return v___x_1969_;
}
else
{
size_t v___x_1970_; size_t v___x_1971_; uint8_t v___x_1972_; 
v___x_1970_ = ((size_t)0ULL);
v___x_1971_ = lean_usize_of_nat(v___x_1968_);
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_1966_, v_as_1965_, v___x_1970_, v___x_1971_);
return v___x_1972_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object* v_as_1973_, lean_object* v_a_1974_){
_start:
{
uint8_t v_a_boxed_1975_; uint8_t v_res_1976_; lean_object* v_r_1977_; 
v_a_boxed_1975_ = lean_unbox(v_a_1974_);
v_res_1976_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_as_1973_, v_a_boxed_1975_);
lean_dec_ref(v_as_1973_);
v_r_1977_ = lean_box(v_res_1976_);
return v_r_1977_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__4(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1982_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3));
v___x_1983_ = lean_unsigned_to_nat(14u);
v___x_1984_ = lean_unsigned_to_nat(22u);
v___x_1985_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2));
v___x_1986_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1));
v___x_1987_ = l_mkPanicMessageWithDecl(v___x_1986_, v___x_1985_, v___x_1984_, v___x_1983_, v___x_1982_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(lean_object* v_format_1988_, lean_object* v_doc_1989_, lean_object* v_lastOperand_1990_, uint8_t v_isTailless_1991_, lean_object* v_combinedChain_1992_, lean_object* v_eligibleKinds_1993_){
_start:
{
uint8_t v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; uint8_t v___y_2004_; lean_object* v___y_2005_; uint8_t v___y_2023_; uint8_t v_trailingOperator_2036_; 
v_trailingOperator_2036_ = lean_ctor_get_uint8(v_format_1988_, 1);
v___y_2023_ = v_trailingOperator_2036_;
goto v___jp_2022_;
v___jp_1994_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1998_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_1999_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrappingLastInline(v_format_1988_, v___y_1997_, v___x_1998_);
v___x_2000_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_1996_, v___y_1995_);
lean_dec_ref(v___y_1996_);
v___x_2001_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1989_, v___x_1999_, v___x_2000_);
lean_dec(v___x_2000_);
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
v___jp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
lean_inc_ref(v_combinedChain_1992_);
v___x_2006_ = lean_array_pop(v_combinedChain_1992_);
v___x_2007_ = lean_array_get_size(v_combinedChain_1992_);
lean_dec_ref(v_combinedChain_1992_);
v___x_2008_ = lean_unsigned_to_nat(2u);
v___x_2009_ = lean_nat_sub(v___x_2007_, v___x_2008_);
v___x_2010_ = lean_array_get_size(v___x_2006_);
v___x_2011_ = lean_nat_dec_lt(v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_dec(v___x_2009_);
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___y_2005_;
v___y_1997_ = v___x_2006_;
goto v___jp_1994_;
}
else
{
lean_object* v_stickyVariant_2012_; lean_object* v_v_2013_; lean_object* v___x_2014_; lean_object* v_xs_x27_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_stickyVariant_2012_ = lean_ctor_get(v___y_2005_, 0);
v_v_2013_ = lean_array_fget(v___x_2006_, v___x_2009_);
v___x_2014_ = lean_box(0);
v_xs_x27_2015_ = lean_array_fset(v___x_2006_, v___x_2009_, v___x_2014_);
v___x_2016_ = l_Lean_Fmt_TaggedDoc_flattened(v_v_2013_);
v___x_2017_ = lean_mk_empty_array_with_capacity(v___x_2008_);
v___x_2018_ = lean_array_push(v___x_2017_, v___x_2016_);
lean_inc_ref(v_stickyVariant_2012_);
v___x_2019_ = lean_array_push(v___x_2018_, v_stickyVariant_2012_);
v___x_2020_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1988_, v___x_2019_);
lean_dec_ref(v___x_2019_);
v___x_2021_ = lean_array_fset(v_xs_x27_2015_, v___x_2009_, v___x_2020_);
lean_dec(v___x_2009_);
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___y_2005_;
v___y_1997_ = v___x_2021_;
goto v___jp_1994_;
}
}
v___jp_2022_:
{
if (v___y_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_dec_ref(v_combinedChain_1992_);
lean_dec_ref(v_lastOperand_1990_);
lean_dec_ref(v_doc_1989_);
v___x_2024_ = lean_box(0);
return v___x_2024_;
}
else
{
if (v_isTailless_1991_ == 0)
{
lean_object* v___x_2025_; 
lean_inc_ref(v_lastOperand_1990_);
v___x_2025_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v_lastOperand_1990_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v___x_2026_; 
lean_dec_ref(v_combinedChain_1992_);
lean_dec_ref(v_lastOperand_1990_);
lean_dec_ref(v_doc_1989_);
v___x_2026_ = lean_box(0);
return v___x_2026_;
}
else
{
lean_object* v_val_2027_; uint8_t v___x_2028_; uint8_t v___x_2029_; 
v_val_2027_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_val_2027_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2028_ = lean_unbox(v_val_2027_);
lean_dec(v_val_2027_);
v___x_2029_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_1993_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_dec_ref(v_combinedChain_1992_);
lean_dec_ref(v_lastOperand_1990_);
lean_dec_ref(v_doc_1989_);
v___x_2030_ = lean_box(0);
return v___x_2030_;
}
else
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_lastOperand_1990_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__4, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__4);
v___x_2033_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_2032_);
v___y_2004_ = v___x_2029_;
v___y_2005_ = v___x_2033_;
goto v___jp_2003_;
}
else
{
lean_object* v_val_2034_; 
v_val_2034_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v___x_2031_, 1);
v___y_2004_ = v___x_2029_;
v___y_2005_ = v_val_2034_;
goto v___jp_2003_;
}
}
}
}
else
{
lean_object* v___x_2035_; 
lean_dec_ref(v_combinedChain_1992_);
lean_dec_ref(v_lastOperand_1990_);
lean_dec_ref(v_doc_1989_);
v___x_2035_ = lean_box(0);
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___boxed(lean_object* v_format_2037_, lean_object* v_doc_2038_, lean_object* v_lastOperand_2039_, lean_object* v_isTailless_2040_, lean_object* v_combinedChain_2041_, lean_object* v_eligibleKinds_2042_){
_start:
{
uint8_t v_isTailless_boxed_2043_; lean_object* v_res_2044_; 
v_isTailless_boxed_2043_ = lean_unbox(v_isTailless_2040_);
v_res_2044_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2037_, v_doc_2038_, v_lastOperand_2039_, v_isTailless_boxed_2043_, v_combinedChain_2041_, v_eligibleKinds_2042_);
lean_dec_ref(v_eligibleKinds_2042_);
lean_dec_ref(v_format_2037_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(lean_object* v_format_2045_, lean_object* v_doc_2046_, lean_object* v_lastOperand_2047_, uint8_t v_isTailless_2048_, lean_object* v_combinedChain_2049_){
_start:
{
if (lean_obj_tag(v_format_2045_) == 0)
{
if (v_isTailless_2048_ == 0)
{
uint8_t v_trailingOperator_2050_; lean_object* v___x_2051_; 
v_trailingOperator_2050_ = lean_ctor_get_uint8(v_format_2045_, 1);
v___x_2051_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (v_trailingOperator_2050_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2070_ = lean_array_get_size(v_combinedChain_2049_);
v___x_2071_ = lean_unsigned_to_nat(2u);
v___x_2072_ = lean_nat_dec_eq(v___x_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec_ref(v_combinedChain_2049_);
lean_dec_ref(v_lastOperand_2047_);
lean_dec_ref(v_doc_2046_);
v___x_2073_ = lean_box(0);
return v___x_2073_;
}
else
{
goto v___jp_2052_;
}
}
else
{
goto v___jp_2052_;
}
v___jp_2052_:
{
uint8_t v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(v_format_2045_);
v___x_2054_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_lastOperand_2047_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec_ref(v_combinedChain_2049_);
lean_dec_ref(v_doc_2046_);
v___x_2055_ = lean_box(0);
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_inc_ref(v_combinedChain_2049_);
v___x_2056_ = lean_array_pop(v_combinedChain_2049_);
v___x_2057_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2045_, v___x_2056_);
lean_dec_ref(v___x_2056_);
v___x_2058_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_2057_);
v___x_2059_ = lean_array_get_size(v_combinedChain_2049_);
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = lean_nat_sub(v___x_2059_, v___x_2060_);
v___x_2062_ = lean_array_get(v___x_2051_, v_combinedChain_2049_, v___x_2061_);
lean_dec(v___x_2061_);
lean_dec_ref(v_combinedChain_2049_);
v___x_2063_ = lean_unsigned_to_nat(2u);
v___x_2064_ = lean_mk_empty_array_with_capacity(v___x_2063_);
v___x_2065_ = lean_array_push(v___x_2064_, v___x_2058_);
v___x_2066_ = lean_array_push(v___x_2065_, v___x_2062_);
v___x_2067_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2045_, v___x_2066_);
lean_dec_ref(v___x_2066_);
v___x_2068_ = l_Lean_Fmt_TaggedDoc_fallbackOnHeight(v_doc_2046_, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
}
else
{
lean_object* v___x_2074_; 
lean_dec_ref(v_combinedChain_2049_);
lean_dec_ref(v_lastOperand_2047_);
lean_dec_ref(v_doc_2046_);
v___x_2074_ = lean_box(0);
return v___x_2074_;
}
}
else
{
lean_object* v___x_2075_; 
lean_dec_ref(v_combinedChain_2049_);
lean_dec_ref(v_lastOperand_2047_);
lean_dec_ref(v_doc_2046_);
v___x_2075_ = lean_box(0);
return v___x_2075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f___boxed(lean_object* v_format_2076_, lean_object* v_doc_2077_, lean_object* v_lastOperand_2078_, lean_object* v_isTailless_2079_, lean_object* v_combinedChain_2080_){
_start:
{
uint8_t v_isTailless_boxed_2081_; lean_object* v_res_2082_; 
v_isTailless_boxed_2081_ = lean_unbox(v_isTailless_2079_);
v_res_2082_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2076_, v_doc_2077_, v_lastOperand_2078_, v_isTailless_boxed_2081_, v_combinedChain_2080_);
lean_dec_ref(v_format_2076_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(lean_object* v_snd_2083_, lean_object* v___x_2084_, lean_object* v_____r_2085_, lean_object* v_normalized_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = lean_nat_add(v_snd_2083_, v___x_2084_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_normalized_2086_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0___boxed(lean_object* v_snd_2090_, lean_object* v___x_2091_, lean_object* v_____r_2092_, lean_object* v_normalized_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2090_, v___x_2091_, v_____r_2092_, v_normalized_2093_);
lean_dec(v___x_2091_);
lean_dec(v_snd_2090_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object* v___x_2095_, lean_object* v_chain_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___y_2099_; lean_object* v_fst_2103_; lean_object* v_snd_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2131_; 
v_fst_2103_ = lean_ctor_get(v_a_2097_, 0);
v_snd_2104_ = lean_ctor_get(v_a_2097_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_a_2097_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2106_ = v_a_2097_;
v_isShared_2107_ = v_isSharedCheck_2131_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_snd_2104_);
lean_inc(v_fst_2103_);
lean_dec(v_a_2097_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2131_;
goto v_resetjp_2105_;
}
v___jp_2098_:
{
if (lean_obj_tag(v___y_2099_) == 0)
{
lean_object* v_a_2100_; 
v_a_2100_ = lean_ctor_get(v___y_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___y_2099_, 1);
return v_a_2100_;
}
else
{
lean_object* v_a_2101_; 
v_a_2101_ = lean_ctor_get(v___y_2099_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___y_2099_, 1);
v_a_2097_ = v_a_2101_;
goto _start;
}
}
v_resetjp_2105_:
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_nat_dec_lt(v_snd_2104_, v___x_2095_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2110_; 
if (v_isShared_2107_ == 0)
{
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_fst_2103_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_snd_2104_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2112_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2113_ = lean_array_get_borrowed(v___x_2112_, v_chain_2096_, v_snd_2104_);
v___x_2114_ = lean_unsigned_to_nat(1u);
v___x_2115_ = lean_nat_add(v_snd_2104_, v___x_2114_);
v___x_2116_ = lean_array_get_size(v_chain_2096_);
v___x_2117_ = lean_nat_dec_lt(v___x_2115_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
lean_dec(v___x_2115_);
lean_inc(v___x_2113_);
v___x_2118_ = lean_array_push(v_fst_2103_, v___x_2113_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2118_);
v___x_2120_ = v___x_2106_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_snd_2104_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
lean_del_object(v___x_2106_);
v___x_2122_ = lean_unsigned_to_nat(2u);
v___x_2123_ = lean_array_fget_borrowed(v_chain_2096_, v___x_2115_);
lean_dec(v___x_2115_);
v___x_2124_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_inc(v___x_2113_);
v___x_2125_ = lean_array_push(v_fst_2103_, v___x_2113_);
lean_inc(v___x_2123_);
v___x_2126_ = lean_array_push(v___x_2125_, v___x_2123_);
v___x_2127_ = lean_box(0);
v___x_2128_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2104_, v___x_2122_, v___x_2127_, v___x_2126_);
lean_dec(v_snd_2104_);
v___y_2099_ = v___x_2128_;
goto v___jp_2098_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_box(0);
v___x_2130_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2104_, v___x_2122_, v___x_2129_, v_fst_2103_);
lean_dec(v_snd_2104_);
v___y_2099_ = v___x_2130_;
goto v___jp_2098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object* v___x_2132_, lean_object* v_chain_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2132_, v_chain_2133_, v_a_2134_);
lean_dec_ref(v_chain_2133_);
lean_dec(v___x_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(lean_object* v___x_2136_, lean_object* v_chain_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v___y_2140_; lean_object* v_fst_2144_; lean_object* v_snd_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2172_; 
v_fst_2144_ = lean_ctor_get(v_a_2138_, 0);
v_snd_2145_ = lean_ctor_get(v_a_2138_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_a_2138_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2147_ = v_a_2138_;
v_isShared_2148_ = v_isSharedCheck_2172_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_snd_2145_);
lean_inc(v_fst_2144_);
lean_dec(v_a_2138_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2172_;
goto v_resetjp_2146_;
}
v___jp_2139_:
{
if (lean_obj_tag(v___y_2140_) == 0)
{
lean_object* v_a_2141_; 
v_a_2141_ = lean_ctor_get(v___y_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___y_2140_, 1);
return v_a_2141_;
}
else
{
lean_object* v_a_2142_; 
v_a_2142_ = lean_ctor_get(v___y_2140_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___y_2140_, 1);
v_a_2138_ = v_a_2142_;
goto _start;
}
}
v_resetjp_2146_:
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_nat_dec_lt(v_snd_2145_, v___x_2136_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2151_; 
if (v_isShared_2148_ == 0)
{
v___x_2151_ = v___x_2147_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_fst_2144_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_snd_2145_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2153_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2154_ = lean_array_get_borrowed(v___x_2153_, v_chain_2137_, v_snd_2145_);
v___x_2155_ = lean_unsigned_to_nat(1u);
v___x_2156_ = lean_nat_add(v_snd_2145_, v___x_2155_);
v___x_2157_ = lean_array_get_size(v_chain_2137_);
v___x_2158_ = lean_nat_dec_lt(v___x_2156_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v___x_2156_);
lean_inc(v___x_2154_);
v___x_2159_ = lean_array_push(v_fst_2144_, v___x_2154_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2159_);
v___x_2161_ = v___x_2147_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_snd_2145_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
else
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
lean_del_object(v___x_2147_);
v___x_2163_ = lean_unsigned_to_nat(2u);
v___x_2164_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2154_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2165_ = lean_array_fget_borrowed(v_chain_2137_, v___x_2156_);
lean_dec(v___x_2156_);
lean_inc(v___x_2154_);
v___x_2166_ = lean_array_push(v_fst_2144_, v___x_2154_);
lean_inc(v___x_2165_);
v___x_2167_ = lean_array_push(v___x_2166_, v___x_2165_);
v___x_2168_ = lean_box(0);
v___x_2169_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2145_, v___x_2163_, v___x_2168_, v___x_2167_);
lean_dec(v_snd_2145_);
v___y_2140_ = v___x_2169_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec(v___x_2156_);
v___x_2170_ = lean_box(0);
v___x_2171_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2145_, v___x_2163_, v___x_2170_, v_fst_2144_);
lean_dec(v_snd_2145_);
v___y_2140_ = v___x_2171_;
goto v___jp_2139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___boxed(lean_object* v___x_2173_, lean_object* v_chain_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2173_, v_chain_2174_, v_a_2175_);
lean_dec_ref(v_chain_2174_);
lean_dec(v___x_2173_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(lean_object* v_format_2185_, lean_object* v_chain_2186_){
_start:
{
uint8_t v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; uint8_t v___y_2192_; lean_object* v___y_2193_; uint8_t v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; uint8_t v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___f_2229_; lean_object* v___x_2230_; lean_object* v_chainSizeBeforeSuffixTrim_2231_; lean_object* v_chain_2232_; lean_object* v_chainSizeBeforePrefixTrim_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; uint8_t v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; uint8_t v___y_2242_; uint8_t v___y_2243_; lean_object* v___y_2255_; lean_object* v___y_2256_; uint8_t v___y_2257_; uint8_t v___y_2258_; uint8_t v___y_2263_; uint8_t v___x_2273_; 
v___f_2229_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0));
v___x_2230_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_chainSizeBeforeSuffixTrim_2231_ = lean_array_get_size(v_chain_2186_);
v_chain_2232_ = l_Array_popWhile___redArg(v___f_2229_, v_chain_2186_);
v_chainSizeBeforePrefixTrim_2233_ = lean_array_get_size(v_chain_2232_);
v___x_2234_ = lean_nat_sub(v_chainSizeBeforeSuffixTrim_2231_, v_chainSizeBeforePrefixTrim_2233_);
v___x_2235_ = lean_unsigned_to_nat(2u);
v___x_2236_ = lean_nat_mod(v___x_2234_, v___x_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_unsigned_to_nat(0u);
v___x_2273_ = lean_nat_dec_eq(v___x_2236_, v___x_2237_);
lean_dec(v___x_2236_);
if (v___x_2273_ == 0)
{
uint8_t v___x_2274_; 
v___x_2274_ = 1;
v___y_2263_ = v___x_2274_;
goto v___jp_2262_;
}
else
{
uint8_t v___x_2275_; 
v___x_2275_ = 0;
v___y_2263_ = v___x_2275_;
goto v___jp_2262_;
}
v___jp_2187_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v_fst_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2206_; 
v___x_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___y_2191_);
lean_ctor_set(v___x_2194_, 1, v___y_2193_);
v___x_2195_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___y_2189_, v___y_2190_, v___x_2194_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
v_fst_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v___x_2195_, 1);
lean_dec(v_unused_2207_);
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2206_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_fst_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2206_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2200_ = lean_box(v___y_2188_);
v___x_2201_ = lean_box(v___y_2192_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v___x_2201_);
lean_ctor_set(v___x_2198_, 0, v___x_2200_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v_fst_2196_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
return v___x_2204_;
}
}
}
v___jp_2208_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v_fst_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2227_; 
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___y_2213_);
lean_ctor_set(v___x_2215_, 1, v___y_2214_);
v___x_2216_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___y_2210_, v___y_2211_, v___x_2215_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
v_fst_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; 
v_unused_2228_ = lean_ctor_get(v___x_2216_, 1);
lean_dec(v_unused_2228_);
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2227_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_fst_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2227_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2221_ = lean_box(v___y_2209_);
v___x_2222_ = lean_box(v___y_2212_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v___x_2222_);
lean_ctor_set(v___x_2219_, 0, v___x_2221_);
v___x_2224_ = v___x_2219_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2225_, 0, v_fst_2217_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
return v___x_2225_;
}
}
}
v___jp_2238_:
{
if (v___y_2243_ == 0)
{
if (v___y_2239_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2244_ = lean_array_get_borrowed(v___x_2230_, v___y_2241_, v___x_2237_);
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_mk_empty_array_with_capacity(v___x_2245_);
lean_inc(v___x_2244_);
v___x_2247_ = lean_array_push(v___x_2246_, v___x_2244_);
v___y_2209_ = v___y_2239_;
v___y_2210_ = v___y_2240_;
v___y_2211_ = v___y_2241_;
v___y_2212_ = v___y_2242_;
v___y_2213_ = v___x_2247_;
v___y_2214_ = v___x_2245_;
goto v___jp_2208_;
}
else
{
lean_object* v___x_2248_; 
v___x_2248_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2209_ = v___y_2239_;
v___y_2210_ = v___y_2240_;
v___y_2211_ = v___y_2241_;
v___y_2212_ = v___y_2242_;
v___y_2213_ = v___x_2248_;
v___y_2214_ = v___x_2237_;
goto v___jp_2208_;
}
}
else
{
if (v___y_2239_ == 0)
{
lean_object* v___x_2249_; 
v___x_2249_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2188_ = v___y_2239_;
v___y_2189_ = v___y_2240_;
v___y_2190_ = v___y_2241_;
v___y_2191_ = v___x_2249_;
v___y_2192_ = v___y_2242_;
v___y_2193_ = v___x_2237_;
goto v___jp_2187_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2250_ = lean_array_get_borrowed(v___x_2230_, v___y_2241_, v___x_2237_);
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_mk_empty_array_with_capacity(v___x_2251_);
lean_inc(v___x_2250_);
v___x_2253_ = lean_array_push(v___x_2252_, v___x_2250_);
v___y_2188_ = v___y_2239_;
v___y_2189_ = v___y_2240_;
v___y_2190_ = v___y_2241_;
v___y_2191_ = v___x_2253_;
v___y_2192_ = v___y_2242_;
v___y_2193_ = v___x_2251_;
goto v___jp_2187_;
}
}
}
v___jp_2254_:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_nat_dec_eq(v___y_2255_, v___x_2237_);
if (v___x_2259_ == 0)
{
uint8_t v_trailingOperator_2260_; 
v_trailingOperator_2260_ = lean_ctor_get_uint8(v_format_2185_, 1);
v___y_2239_ = v___y_2258_;
v___y_2240_ = v___y_2255_;
v___y_2241_ = v___y_2256_;
v___y_2242_ = v___y_2257_;
v___y_2243_ = v_trailingOperator_2260_;
goto v___jp_2238_;
}
else
{
lean_object* v___x_2261_; 
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
v___x_2261_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2));
return v___x_2261_;
}
}
v___jp_2262_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v_chain_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2264_ = l_Array_reverse___redArg(v_chain_2232_);
v___x_2265_ = l_Array_popWhile___redArg(v___f_2229_, v___x_2264_);
v_chain_2266_ = l_Array_reverse___redArg(v___x_2265_);
v___x_2267_ = lean_array_get_size(v_chain_2266_);
v___x_2268_ = lean_nat_sub(v_chainSizeBeforePrefixTrim_2233_, v___x_2267_);
v___x_2269_ = lean_nat_mod(v___x_2268_, v___x_2235_);
lean_dec(v___x_2268_);
v___x_2270_ = lean_nat_dec_eq(v___x_2269_, v___x_2237_);
lean_dec(v___x_2269_);
if (v___x_2270_ == 0)
{
uint8_t v___x_2271_; 
v___x_2271_ = 1;
v___y_2255_ = v___x_2267_;
v___y_2256_ = v_chain_2266_;
v___y_2257_ = v___y_2263_;
v___y_2258_ = v___x_2271_;
goto v___jp_2254_;
}
else
{
uint8_t v___x_2272_; 
v___x_2272_ = 0;
v___y_2255_ = v___x_2267_;
v___y_2256_ = v_chain_2266_;
v___y_2257_ = v___y_2263_;
v___y_2258_ = v___x_2272_;
goto v___jp_2254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___boxed(lean_object* v_format_2276_, lean_object* v_chain_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2276_, v_chain_2277_);
lean_dec_ref(v_format_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(lean_object* v___x_2279_, lean_object* v_chain_2280_, lean_object* v_inst_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2279_, v_chain_2280_, v_a_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___boxed(lean_object* v___x_2284_, lean_object* v_chain_2285_, lean_object* v_inst_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(v___x_2284_, v_chain_2285_, v_inst_2286_, v_a_2287_);
lean_dec_ref(v_chain_2285_);
lean_dec(v___x_2284_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object* v___x_2289_, lean_object* v_chain_2290_, lean_object* v_inst_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2289_, v_chain_2290_, v_a_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object* v___x_2294_, lean_object* v_chain_2295_, lean_object* v_inst_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(v___x_2294_, v_chain_2295_, v_inst_2296_, v_a_2297_);
lean_dec_ref(v_chain_2295_);
lean_dec(v___x_2294_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(lean_object* v_chain_2299_, lean_object* v_format_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_fst_2302_; lean_object* v_snd_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2333_; 
v_fst_2302_ = lean_ctor_get(v_a_2301_, 0);
v_snd_2303_ = lean_ctor_get(v_a_2301_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_a_2301_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2305_ = v_a_2301_;
v_isShared_2306_ = v_isSharedCheck_2333_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_snd_2303_);
lean_inc(v_fst_2302_);
lean_dec(v_a_2301_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2333_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = lean_array_get_size(v_chain_2299_);
v___x_2308_ = lean_nat_dec_lt(v_snd_2303_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2310_; 
if (v_isShared_2306_ == 0)
{
v___x_2310_ = v___x_2305_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_fst_2302_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_snd_2303_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___y_2315_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2312_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2313_ = lean_array_get_borrowed(v___x_2312_, v_chain_2299_, v_snd_2303_);
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = lean_nat_add(v_snd_2303_, v___x_2328_);
v___x_2330_ = lean_nat_dec_lt(v___x_2329_, v___x_2307_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
lean_dec(v___x_2329_);
v___x_2331_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2315_ = v___x_2331_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_array_fget_borrowed(v_chain_2299_, v___x_2329_);
lean_dec(v___x_2329_);
lean_inc(v___x_2332_);
v___y_2315_ = v___x_2332_;
goto v___jp_2314_;
}
v___jp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2316_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2315_);
v___x_2317_ = lean_unsigned_to_nat(2u);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___x_2317_);
lean_inc(v___x_2313_);
v___x_2319_ = lean_array_push(v___x_2318_, v___x_2313_);
v___x_2320_ = lean_array_push(v___x_2319_, v___x_2316_);
v___x_2321_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2300_, v___x_2320_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = lean_array_push(v_fst_2302_, v___x_2321_);
v___x_2323_ = lean_nat_add(v_snd_2303_, v___x_2317_);
lean_dec(v_snd_2303_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v___x_2323_);
lean_ctor_set(v___x_2305_, 0, v___x_2322_);
v___x_2325_ = v___x_2305_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
v_a_2301_ = v___x_2325_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg___boxed(lean_object* v_chain_2334_, lean_object* v_format_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2334_, v_format_2335_, v_a_2336_);
lean_dec_ref(v_format_2335_);
lean_dec_ref(v_chain_2334_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(lean_object* v_chain_2338_, lean_object* v_format_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_fst_2341_; lean_object* v_snd_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2372_; 
v_fst_2341_ = lean_ctor_get(v_a_2340_, 0);
v_snd_2342_ = lean_ctor_get(v_a_2340_, 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_a_2340_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2344_ = v_a_2340_;
v_isShared_2345_ = v_isSharedCheck_2372_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_snd_2342_);
lean_inc(v_fst_2341_);
lean_dec(v_a_2340_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2372_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_array_get_size(v_chain_2338_);
v___x_2347_ = lean_nat_dec_lt(v_snd_2342_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2349_; 
if (v_isShared_2345_ == 0)
{
v___x_2349_ = v___x_2344_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_fst_2341_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_snd_2342_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___y_2354_; lean_object* v___x_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v___x_2351_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2352_ = lean_array_get_borrowed(v___x_2351_, v_chain_2338_, v_snd_2342_);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_add(v_snd_2342_, v___x_2367_);
v___x_2369_ = lean_nat_dec_lt(v___x_2368_, v___x_2346_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; 
lean_dec(v___x_2368_);
v___x_2370_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2354_ = v___x_2370_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_array_fget_borrowed(v_chain_2338_, v___x_2368_);
lean_dec(v___x_2368_);
lean_inc(v___x_2371_);
v___y_2354_ = v___x_2371_;
goto v___jp_2353_;
}
v___jp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
lean_inc(v___x_2352_);
v___x_2355_ = l_Lean_Fmt_TaggedDoc_nested(v___x_2352_);
v___x_2356_ = lean_unsigned_to_nat(2u);
v___x_2357_ = lean_mk_empty_array_with_capacity(v___x_2356_);
v___x_2358_ = lean_array_push(v___x_2357_, v___x_2355_);
v___x_2359_ = lean_array_push(v___x_2358_, v___y_2354_);
v___x_2360_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2339_, v___x_2359_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = lean_array_push(v_fst_2341_, v___x_2360_);
v___x_2362_ = lean_nat_add(v_snd_2342_, v___x_2356_);
lean_dec(v_snd_2342_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 1, v___x_2362_);
lean_ctor_set(v___x_2344_, 0, v___x_2361_);
v___x_2364_ = v___x_2344_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
v_a_2340_ = v___x_2364_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg___boxed(lean_object* v_chain_2373_, lean_object* v_format_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2373_, v_format_2374_, v_a_2375_);
lean_dec_ref(v_format_2374_);
lean_dec_ref(v_chain_2373_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(lean_object* v_format_2377_, lean_object* v_chain_2378_, uint8_t v_isHeadless_2379_){
_start:
{
lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2387_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2397_; lean_object* v___x_2400_; uint8_t v___y_2402_; uint8_t v_trailingOperator_2415_; 
v___x_2400_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_2415_ = lean_ctor_get_uint8(v_format_2377_, 1);
v___y_2402_ = v_trailingOperator_2415_;
goto v___jp_2401_;
v___jp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_fst_2385_; 
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___y_2381_);
lean_ctor_set(v___x_2383_, 1, v___y_2382_);
v___x_2384_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2378_, v_format_2377_, v___x_2383_);
v_fst_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_fst_2385_);
lean_dec_ref(v___x_2384_);
return v_fst_2385_;
}
v___jp_2386_:
{
if (v_isHeadless_2379_ == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_unsigned_to_nat(0u);
v___y_2381_ = v___y_2387_;
v___y_2382_ = v___x_2388_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_unsigned_to_nat(1u);
v___y_2381_ = v___y_2387_;
v___y_2382_ = v___x_2389_;
goto v___jp_2380_;
}
}
v___jp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_fst_2395_; 
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___y_2391_);
lean_ctor_set(v___x_2393_, 1, v___y_2392_);
v___x_2394_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2378_, v_format_2377_, v___x_2393_);
v_fst_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_fst_2395_);
lean_dec_ref(v___x_2394_);
return v_fst_2395_;
}
v___jp_2396_:
{
if (v_isHeadless_2379_ == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_unsigned_to_nat(1u);
v___y_2391_ = v___y_2397_;
v___y_2392_ = v___x_2398_;
goto v___jp_2390_;
}
else
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_unsigned_to_nat(0u);
v___y_2391_ = v___y_2397_;
v___y_2392_ = v___x_2399_;
goto v___jp_2390_;
}
}
v___jp_2401_:
{
if (v___y_2402_ == 0)
{
if (v_isHeadless_2379_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = lean_array_get_borrowed(v___x_2400_, v_chain_2378_, v___x_2403_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_mk_empty_array_with_capacity(v___x_2405_);
lean_inc(v___x_2404_);
v___x_2407_ = lean_array_push(v___x_2406_, v___x_2404_);
v___y_2397_ = v___x_2407_;
goto v___jp_2396_;
}
else
{
lean_object* v___x_2408_; 
v___x_2408_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2397_ = v___x_2408_;
goto v___jp_2396_;
}
}
else
{
if (v_isHeadless_2379_ == 0)
{
lean_object* v___x_2409_; 
v___x_2409_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2387_ = v___x_2409_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2410_ = lean_unsigned_to_nat(0u);
v___x_2411_ = lean_array_get_borrowed(v___x_2400_, v_chain_2378_, v___x_2410_);
v___x_2412_ = lean_unsigned_to_nat(1u);
v___x_2413_ = lean_mk_empty_array_with_capacity(v___x_2412_);
lean_inc(v___x_2411_);
v___x_2414_ = lean_array_push(v___x_2413_, v___x_2411_);
v___y_2387_ = v___x_2414_;
goto v___jp_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain___boxed(lean_object* v_format_2416_, lean_object* v_chain_2417_, lean_object* v_isHeadless_2418_){
_start:
{
uint8_t v_isHeadless_boxed_2419_; lean_object* v_res_2420_; 
v_isHeadless_boxed_2419_ = lean_unbox(v_isHeadless_2418_);
v_res_2420_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2416_, v_chain_2417_, v_isHeadless_boxed_2419_);
lean_dec_ref(v_chain_2417_);
lean_dec_ref(v_format_2416_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(lean_object* v_chain_2421_, lean_object* v_format_2422_, lean_object* v_inst_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2421_, v_format_2422_, v_a_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___boxed(lean_object* v_chain_2426_, lean_object* v_format_2427_, lean_object* v_inst_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(v_chain_2426_, v_format_2427_, v_inst_2428_, v_a_2429_);
lean_dec_ref(v_format_2427_);
lean_dec_ref(v_chain_2426_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(lean_object* v_chain_2431_, lean_object* v_format_2432_, lean_object* v_inst_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2431_, v_format_2432_, v_a_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___boxed(lean_object* v_chain_2436_, lean_object* v_format_2437_, lean_object* v_inst_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(v_chain_2436_, v_format_2437_, v_inst_2438_, v_a_2439_);
lean_dec_ref(v_format_2437_);
lean_dec_ref(v_chain_2436_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(lean_object* v_format_2441_, lean_object* v_docs_2442_){
_start:
{
uint8_t v___y_2444_; uint8_t v___x_2447_; 
v___x_2447_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_format_2441_);
if (v___x_2447_ == 0)
{
uint8_t v___x_2448_; 
v___x_2448_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_format_2441_);
if (v___x_2448_ == 0)
{
uint8_t v_spacing_2449_; 
v_spacing_2449_ = lean_ctor_get_uint8(v_format_2441_, 2);
v___y_2444_ = v_spacing_2449_;
goto v___jp_2443_;
}
else
{
lean_object* v___x_2450_; uint8_t v___y_2452_; uint8_t v_spacing_2479_; 
v___x_2450_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_spacing_2479_ = lean_ctor_get_uint8(v_format_2441_, 2);
v___y_2452_ = v_spacing_2479_;
goto v___jp_2451_;
v___jp_2451_:
{
if (v___y_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2453_ = lean_unsigned_to_nat(0u);
v___x_2454_ = lean_array_get_size(v_docs_2442_);
v___x_2455_ = lean_unsigned_to_nat(1u);
v___x_2456_ = lean_nat_sub(v___x_2454_, v___x_2455_);
lean_inc(v___x_2456_);
lean_inc_ref(v_docs_2442_);
v___x_2457_ = l_Array_toSubarray___redArg(v_docs_2442_, v___x_2453_, v___x_2456_);
v___x_2458_ = l_Subarray_copy___redArg(v___x_2457_);
v___x_2459_ = l_Lean_Fmt_TaggedDoc_fill(v___x_2458_);
v___x_2460_ = lean_array_get(v___x_2450_, v_docs_2442_, v___x_2456_);
lean_dec(v___x_2456_);
lean_dec_ref(v_docs_2442_);
v___x_2461_ = lean_unsigned_to_nat(2u);
v___x_2462_ = lean_mk_empty_array_with_capacity(v___x_2461_);
v___x_2463_ = lean_array_push(v___x_2462_, v___x_2459_);
v___x_2464_ = lean_array_push(v___x_2463_, v___x_2460_);
v___x_2465_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2464_, v___y_2452_);
lean_dec_ref(v___x_2464_);
return v___x_2465_;
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = lean_array_get_size(v_docs_2442_);
v___x_2468_ = lean_unsigned_to_nat(1u);
v___x_2469_ = lean_nat_sub(v___x_2467_, v___x_2468_);
lean_inc(v___x_2469_);
lean_inc_ref(v_docs_2442_);
v___x_2470_ = l_Array_toSubarray___redArg(v_docs_2442_, v___x_2466_, v___x_2469_);
v___x_2471_ = l_Subarray_copy___redArg(v___x_2470_);
v___x_2472_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_2471_);
v___x_2473_ = lean_array_get(v___x_2450_, v_docs_2442_, v___x_2469_);
lean_dec(v___x_2469_);
lean_dec_ref(v_docs_2442_);
v___x_2474_ = lean_unsigned_to_nat(2u);
v___x_2475_ = lean_mk_empty_array_with_capacity(v___x_2474_);
v___x_2476_ = lean_array_push(v___x_2475_, v___x_2472_);
v___x_2477_ = lean_array_push(v___x_2476_, v___x_2473_);
v___x_2478_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2477_, v___x_2448_);
lean_dec_ref(v___x_2477_);
return v___x_2478_;
}
}
}
}
else
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lean_Fmt_Layouts_lines(v_docs_2442_);
lean_dec_ref(v_docs_2442_);
return v___x_2480_;
}
v___jp_2443_:
{
if (v___y_2444_ == 0)
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_Fmt_TaggedDoc_fill(v_docs_2442_);
return v___x_2445_;
}
else
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v_docs_2442_);
return v___x_2446_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill___boxed(lean_object* v_format_2481_, lean_object* v_docs_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2481_, v_docs_2482_);
lean_dec_ref(v_format_2481_);
return v_res_2483_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(lean_object* v_columnPos_2484_, lean_object* v_indentation_2485_, lean_object* v_nonCumulativeIndentation_2486_){
_start:
{
lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = lean_nat_add(v_indentation_2485_, v_nonCumulativeIndentation_2486_);
v___x_2488_ = lean_nat_dec_le(v_columnPos_2484_, v___x_2487_);
lean_dec(v___x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed(lean_object* v_columnPos_2489_, lean_object* v_indentation_2490_, lean_object* v_nonCumulativeIndentation_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(v_columnPos_2489_, v_indentation_2490_, v_nonCumulativeIndentation_2491_);
lean_dec(v_nonCumulativeIndentation_2491_);
lean_dec(v_indentation_2490_);
lean_dec(v_columnPos_2489_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(lean_object* v_format_2510_, lean_object* v_combinedChain_2511_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v_firstOperand_2514_; lean_object* v___y_2516_; uint8_t v___y_2536_; uint8_t v_hardNestedFirstOperand_2543_; 
v___x_2512_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2513_ = lean_unsigned_to_nat(0u);
v_firstOperand_2514_ = lean_array_get_borrowed(v___x_2512_, v_combinedChain_2511_, v___x_2513_);
v_hardNestedFirstOperand_2543_ = lean_ctor_get_uint8(v_format_2510_, 0);
v___y_2536_ = v_hardNestedFirstOperand_2543_;
goto v___jp_2535_;
v___jp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_compactFirstOperation_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_compactedChain_2530_; lean_object* v___x_2531_; 
v___x_2517_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion));
v___x_2518_ = l_Lean_Fmt_TaggedDoc_guarded(v___x_2517_, v___y_2516_);
v___x_2519_ = lean_unsigned_to_nat(2u);
v___x_2520_ = lean_mk_empty_array_with_capacity(v___x_2519_);
lean_inc(v_firstOperand_2514_);
v___x_2521_ = lean_array_push(v___x_2520_, v_firstOperand_2514_);
v___x_2522_ = lean_array_push(v___x_2521_, v___x_2518_);
v_compactFirstOperation_2523_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2510_, v___x_2522_);
lean_dec_ref(v___x_2522_);
v___x_2524_ = lean_unsigned_to_nat(1u);
v___x_2525_ = lean_mk_empty_array_with_capacity(v___x_2524_);
v___x_2526_ = lean_array_push(v___x_2525_, v_compactFirstOperation_2523_);
v___x_2527_ = lean_array_get_size(v_combinedChain_2511_);
v___x_2528_ = l_Array_toSubarray___redArg(v_combinedChain_2511_, v___x_2519_, v___x_2527_);
v___x_2529_ = l_Subarray_copy___redArg(v___x_2528_);
v_compactedChain_2530_ = l_Array_append___redArg(v___x_2526_, v___x_2529_);
lean_dec_ref(v___x_2529_);
v___x_2531_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2510_, v_compactedChain_2530_);
return v___x_2531_;
}
v___jp_2532_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_unsigned_to_nat(1u);
v___x_2534_ = lean_array_get_borrowed(v___x_2512_, v_combinedChain_2511_, v___x_2533_);
lean_inc(v___x_2534_);
v___y_2516_ = v___x_2534_;
goto v___jp_2515_;
}
v___jp_2535_:
{
if (v___y_2536_ == 0)
{
goto v___jp_2532_;
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2537_ = lean_unsigned_to_nat(2u);
v___x_2538_ = lean_array_get_size(v_combinedChain_2511_);
v___x_2539_ = lean_nat_dec_lt(v___x_2537_, v___x_2538_);
if (v___x_2539_ == 0)
{
goto v___jp_2532_;
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = lean_unsigned_to_nat(1u);
v___x_2541_ = lean_array_get_borrowed(v___x_2512_, v_combinedChain_2511_, v___x_2540_);
lean_inc(v___x_2541_);
v___x_2542_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_2541_);
v___y_2516_ = v___x_2542_;
goto v___jp_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation___boxed(lean_object* v_format_2544_, lean_object* v_combinedChain_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2544_, v_combinedChain_2545_);
lean_dec_ref(v_format_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(lean_object* v_format_2547_, lean_object* v_docs_2548_, lean_object* v_wrap_2549_){
_start:
{
uint8_t v___y_2551_; uint8_t v_spacing_2554_; 
v_spacing_2554_ = lean_ctor_get_uint8(v_format_2547_, 2);
v___y_2551_ = v_spacing_2554_;
goto v___jp_2550_;
v___jp_2550_:
{
if (v___y_2551_ == 0)
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Fmt_TaggedDoc_fillWrapping(v_docs_2548_, v_wrap_2549_);
return v___x_2552_;
}
else
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(v_docs_2548_, v_wrap_2549_);
return v___x_2553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping___boxed(lean_object* v_format_2555_, lean_object* v_docs_2556_, lean_object* v_wrap_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2555_, v_docs_2556_, v_wrap_2557_);
lean_dec_ref(v_format_2555_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(lean_object* v___x_2559_, size_t v_sz_2560_, size_t v_i_2561_, lean_object* v_bs_2562_){
_start:
{
uint8_t v___x_2563_; 
v___x_2563_ = lean_usize_dec_lt(v_i_2561_, v_sz_2560_);
if (v___x_2563_ == 0)
{
return v_bs_2562_;
}
else
{
lean_object* v___x_2564_; lean_object* v_v_2565_; lean_object* v___x_2566_; lean_object* v_bs_x27_2567_; lean_object* v___y_2569_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2564_ = lean_unsigned_to_nat(1u);
v_v_2565_ = lean_array_uget(v_bs_2562_, v_i_2561_);
v___x_2566_ = lean_unsigned_to_nat(0u);
v_bs_x27_2567_ = lean_array_uset(v_bs_2562_, v_i_2561_, v___x_2566_);
v___x_2574_ = lean_usize_to_nat(v_i_2561_);
v___x_2575_ = lean_nat_sub(v___x_2559_, v___x_2564_);
v___x_2576_ = lean_nat_dec_lt(v___x_2574_, v___x_2575_);
lean_dec(v___x_2575_);
lean_dec(v___x_2574_);
if (v___x_2576_ == 0)
{
v___y_2569_ = v_v_2565_;
goto v___jp_2568_;
}
else
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2565_);
v___y_2569_ = v___x_2577_;
goto v___jp_2568_;
}
v___jp_2568_:
{
size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = ((size_t)1ULL);
v___x_2571_ = lean_usize_add(v_i_2561_, v___x_2570_);
v___x_2572_ = lean_array_uset(v_bs_x27_2567_, v_i_2561_, v___y_2569_);
v_i_2561_ = v___x_2571_;
v_bs_2562_ = v___x_2572_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg___boxed(lean_object* v___x_2578_, lean_object* v_sz_2579_, lean_object* v_i_2580_, lean_object* v_bs_2581_){
_start:
{
size_t v_sz_boxed_2582_; size_t v_i_boxed_2583_; lean_object* v_res_2584_; 
v_sz_boxed_2582_ = lean_unbox_usize(v_sz_2579_);
lean_dec(v_sz_2579_);
v_i_boxed_2583_ = lean_unbox_usize(v_i_2580_);
lean_dec(v_i_2580_);
v_res_2584_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2578_, v_sz_boxed_2582_, v_i_boxed_2583_, v_bs_2581_);
lean_dec(v___x_2578_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object* v_chain_2598_, lean_object* v_format_2599_){
_start:
{
lean_object* v___x_2600_; lean_object* v_snd_2601_; lean_object* v_fst_2602_; lean_object* v_fst_2603_; lean_object* v_snd_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2600_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2599_, v_chain_2598_);
v_snd_2601_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_snd_2601_);
v_fst_2602_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_fst_2602_);
lean_dec_ref(v___x_2600_);
v_fst_2603_ = lean_ctor_get(v_snd_2601_, 0);
lean_inc(v_fst_2603_);
v_snd_2604_ = lean_ctor_get(v_snd_2601_, 1);
lean_inc(v_snd_2604_);
lean_dec(v_snd_2601_);
v___x_2605_ = lean_array_get_size(v_fst_2602_);
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_nat_dec_eq(v___x_2605_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; uint8_t v___y_2610_; lean_object* v_doc_2611_; uint8_t v___x_2618_; lean_object* v_combinedChain_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___y_2623_; lean_object* v___y_2624_; lean_object* v_doc_2625_; uint8_t v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; uint8_t v___x_2650_; lean_object* v___y_2652_; uint8_t v___y_2653_; lean_object* v_combinedChain_2659_; uint8_t v___y_2662_; uint8_t v___y_2669_; uint8_t v___y_2670_; uint8_t v___y_2678_; 
v___x_2608_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2618_ = lean_unbox(v_fst_2603_);
v_combinedChain_2619_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2599_, v_fst_2602_, v___x_2618_);
v___x_2620_ = lean_array_get_size(v_combinedChain_2619_);
v___x_2621_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_nat_dec_eq(v___x_2620_, v___x_2621_);
if (v___x_2650_ == 0)
{
uint8_t v_trailingOperator_2680_; 
v_trailingOperator_2680_ = lean_ctor_get_uint8(v_format_2599_, 1);
v___y_2678_ = v_trailingOperator_2680_;
goto v___jp_2677_;
}
else
{
lean_object* v___x_2681_; 
lean_dec(v_snd_2604_);
lean_dec(v_fst_2603_);
lean_dec(v_fst_2602_);
v___x_2681_ = lean_array_get(v___x_2608_, v_combinedChain_2619_, v___x_2606_);
lean_dec_ref(v_combinedChain_2619_);
return v___x_2681_;
}
v___jp_2609_:
{
if (v___y_2610_ == 0)
{
lean_object* v___x_2612_; 
lean_dec(v_fst_2602_);
v___x_2612_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2611_);
return v___x_2612_;
}
else
{
lean_object* v___x_2613_; lean_object* v_doc_2614_; uint8_t v___x_2615_; lean_object* v_doc_2616_; lean_object* v___x_2617_; 
v___x_2613_ = lean_array_get(v___x_2608_, v_fst_2602_, v___x_2606_);
lean_dec(v_fst_2602_);
v_doc_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_doc_2614_);
lean_dec(v___x_2613_);
v___x_2615_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2614_);
v_doc_2616_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2611_, v___x_2615_);
v___x_2617_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2616_);
return v___x_2617_;
}
}
v___jp_2622_:
{
lean_object* v___x_2626_; lean_object* v_lastOperand_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; 
v___x_2626_ = lean_nat_sub(v___x_2605_, v___x_2621_);
v_lastOperand_2627_ = lean_array_get_borrowed(v___x_2608_, v_fst_2602_, v___x_2626_);
lean_dec(v___x_2626_);
v___x_2628_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
v___x_2629_ = lean_unbox(v_snd_2604_);
lean_inc_ref(v___y_2624_);
lean_inc(v_lastOperand_2627_);
lean_inc_ref(v_doc_2625_);
v___x_2630_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2599_, v_doc_2625_, v_lastOperand_2627_, v___x_2629_, v___y_2624_, v___x_2628_);
if (lean_obj_tag(v___x_2630_) == 1)
{
lean_object* v_val_2631_; 
lean_dec_ref(v_doc_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v_snd_2604_);
v_val_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_val_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v___y_2610_ = v___y_2623_;
v_doc_2611_ = v_val_2631_;
goto v___jp_2609_;
}
else
{
uint8_t v___x_2632_; lean_object* v___x_2633_; 
lean_dec(v___x_2630_);
v___x_2632_ = lean_unbox(v_snd_2604_);
lean_inc_ref(v___y_2624_);
lean_inc(v_lastOperand_2627_);
lean_inc_ref(v_doc_2625_);
v___x_2633_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2599_, v_doc_2625_, v_lastOperand_2627_, v___x_2632_, v___y_2624_);
if (lean_obj_tag(v___x_2633_) == 1)
{
lean_object* v_val_2634_; 
lean_dec_ref(v_doc_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v_snd_2604_);
v_val_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v___y_2610_ = v___y_2623_;
v_doc_2611_ = v_val_2634_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; 
lean_dec(v___x_2633_);
v___x_2635_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
v___x_2636_ = lean_unbox(v_snd_2604_);
lean_dec(v_snd_2604_);
lean_inc(v_lastOperand_2627_);
lean_inc_ref(v_doc_2625_);
v___x_2637_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2599_, v_doc_2625_, v_lastOperand_2627_, v___x_2636_, v___y_2624_, v___x_2635_);
if (lean_obj_tag(v___x_2637_) == 1)
{
lean_object* v_val_2638_; 
lean_dec_ref(v_doc_2625_);
v_val_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_val_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v___y_2610_ = v___y_2623_;
v_doc_2611_ = v_val_2638_;
goto v___jp_2609_;
}
else
{
lean_dec(v___x_2637_);
v___y_2610_ = v___y_2623_;
v_doc_2611_ = v_doc_2625_;
goto v___jp_2609_;
}
}
}
}
v___jp_2639_:
{
uint8_t v___x_2643_; 
v___x_2643_ = lean_unbox(v_fst_2603_);
lean_dec(v_fst_2603_);
if (v___x_2643_ == 0)
{
if (v___y_2640_ == 0)
{
v___y_2623_ = v___y_2640_;
v___y_2624_ = v___y_2641_;
v_doc_2625_ = v___y_2642_;
goto v___jp_2622_;
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v_doc_2649_; 
lean_inc_ref(v___y_2641_);
v___x_2644_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2599_, v___y_2641_);
v___x_2645_ = lean_unsigned_to_nat(2u);
v___x_2646_ = lean_mk_empty_array_with_capacity(v___x_2645_);
v___x_2647_ = lean_array_push(v___x_2646_, v___x_2644_);
v___x_2648_ = lean_array_push(v___x_2647_, v___y_2642_);
v_doc_2649_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2648_);
v___y_2623_ = v___y_2640_;
v___y_2624_ = v___y_2641_;
v_doc_2625_ = v_doc_2649_;
goto v___jp_2622_;
}
}
else
{
v___y_2623_ = v___y_2640_;
v___y_2624_ = v___y_2641_;
v_doc_2625_ = v___y_2642_;
goto v___jp_2622_;
}
}
v___jp_2651_:
{
if (v___y_2653_ == 0)
{
uint8_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = 1;
lean_inc_ref(v___y_2652_);
v___x_2655_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2599_, v___y_2652_);
v___y_2640_ = v___x_2654_;
v___y_2641_ = v___y_2652_;
v___y_2642_ = v___x_2655_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
lean_inc_ref(v___y_2652_);
v___x_2657_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2599_, v___y_2652_, v___x_2656_);
v___y_2640_ = v___x_2650_;
v___y_2641_ = v___y_2652_;
v___y_2642_ = v___x_2657_;
goto v___jp_2639_;
}
}
v___jp_2658_:
{
uint8_t v_trailingOperator_2660_; 
v_trailingOperator_2660_ = lean_ctor_get_uint8(v_format_2599_, 1);
v___y_2652_ = v_combinedChain_2659_;
v___y_2653_ = v_trailingOperator_2660_;
goto v___jp_2651_;
}
v___jp_2661_:
{
if (v___y_2662_ == 0)
{
v_combinedChain_2659_ = v_combinedChain_2619_;
goto v___jp_2658_;
}
else
{
size_t v_sz_2663_; size_t v___x_2664_; lean_object* v_combinedChain_2665_; 
v_sz_2663_ = lean_array_size(v_combinedChain_2619_);
v___x_2664_ = ((size_t)0ULL);
v_combinedChain_2665_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2620_, v_sz_2663_, v___x_2664_, v_combinedChain_2619_);
v_combinedChain_2659_ = v_combinedChain_2665_;
goto v___jp_2658_;
}
}
v___jp_2666_:
{
uint8_t v_hardNestedFirstOperand_2667_; 
v_hardNestedFirstOperand_2667_ = lean_ctor_get_uint8(v_format_2599_, 0);
v___y_2662_ = v_hardNestedFirstOperand_2667_;
goto v___jp_2661_;
}
v___jp_2668_:
{
if (v___y_2670_ == 0)
{
if (v___y_2669_ == 0)
{
v_combinedChain_2659_ = v_combinedChain_2619_;
goto v___jp_2658_;
}
else
{
goto v___jp_2666_;
}
}
else
{
uint8_t v___x_2671_; 
v___x_2671_ = lean_nat_dec_lt(v___x_2606_, v___x_2620_);
if (v___x_2671_ == 0)
{
v_combinedChain_2659_ = v_combinedChain_2619_;
goto v___jp_2658_;
}
else
{
lean_object* v_v_2672_; lean_object* v___x_2673_; lean_object* v_xs_x27_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_v_2672_ = lean_array_fget(v_combinedChain_2619_, v___x_2606_);
v___x_2673_ = lean_box(0);
v_xs_x27_2674_ = lean_array_fset(v_combinedChain_2619_, v___x_2606_, v___x_2673_);
v___x_2675_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2672_);
v___x_2676_ = lean_array_fset(v_xs_x27_2674_, v___x_2606_, v___x_2675_);
v_combinedChain_2659_ = v___x_2676_;
goto v___jp_2658_;
}
}
}
v___jp_2677_:
{
if (v___y_2678_ == 0)
{
uint8_t v_hardNestedFirstOperand_2679_; 
v_hardNestedFirstOperand_2679_ = lean_ctor_get_uint8(v_format_2599_, 0);
v___y_2669_ = v___y_2678_;
v___y_2670_ = v_hardNestedFirstOperand_2679_;
goto v___jp_2668_;
}
else
{
goto v___jp_2666_;
}
}
}
else
{
lean_object* v___x_2682_; 
lean_dec(v_snd_2604_);
lean_dec(v_fst_2603_);
lean_dec(v_fst_2602_);
v___x_2682_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_2682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator___boxed(lean_object* v_chain_2683_, lean_object* v_format_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_2683_, v_format_2684_);
lean_dec_ref(v_format_2684_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(lean_object* v___x_2686_, lean_object* v_as_2687_, size_t v_sz_2688_, size_t v_i_2689_, lean_object* v_bs_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2686_, v_sz_2688_, v_i_2689_, v_bs_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___boxed(lean_object* v___x_2692_, lean_object* v_as_2693_, lean_object* v_sz_2694_, lean_object* v_i_2695_, lean_object* v_bs_2696_){
_start:
{
size_t v_sz_boxed_2697_; size_t v_i_boxed_2698_; lean_object* v_res_2699_; 
v_sz_boxed_2697_ = lean_unbox_usize(v_sz_2694_);
lean_dec(v_sz_2694_);
v_i_boxed_2698_ = lean_unbox_usize(v_i_2695_);
lean_dec(v_i_2695_);
v_res_2699_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(v___x_2692_, v_as_2693_, v_sz_boxed_2697_, v_i_boxed_2698_, v_bs_2696_);
lean_dec_ref(v_as_2693_);
lean_dec(v___x_2692_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object* v_lhs_2700_, lean_object* v_typeAscriptionTk_2701_, lean_object* v_rhs_2702_, lean_object* v_format_2703_){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2704_ = lean_unsigned_to_nat(3u);
v___x_2705_ = lean_mk_empty_array_with_capacity(v___x_2704_);
v___x_2706_ = lean_array_push(v___x_2705_, v_lhs_2700_);
v___x_2707_ = lean_array_push(v___x_2706_, v_typeAscriptionTk_2701_);
v___x_2708_ = lean_array_push(v___x_2707_, v_rhs_2702_);
v___x_2709_ = l_Lean_Fmt_Layouts_infixOperator(v___x_2708_, v_format_2703_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription___boxed(lean_object* v_lhs_2710_, lean_object* v_typeAscriptionTk_2711_, lean_object* v_rhs_2712_, lean_object* v_format_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Fmt_Layouts_typeAscription(v_lhs_2710_, v_typeAscriptionTk_2711_, v_rhs_2712_, v_format_2713_);
lean_dec_ref(v_format_2713_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl(lean_object* v_x_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_obj_tag_nat(v_x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl___boxed(lean_object* v_x_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl(v_x_2717_);
lean_dec_ref(v_x_2717_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(lean_object* v_t_2719_, lean_object* v_k_2720_){
_start:
{
if (lean_obj_tag(v_t_2719_) == 0)
{
uint8_t v_spacing_2721_; uint8_t v_alwaysPropagateStickiness_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_spacing_2721_ = lean_ctor_get_uint8(v_t_2719_, 0);
v_alwaysPropagateStickiness_2722_ = lean_ctor_get_uint8(v_t_2719_, 1);
lean_dec_ref_known(v_t_2719_, 0);
v___x_2723_ = lean_box(v_spacing_2721_);
v___x_2724_ = lean_box(v_alwaysPropagateStickiness_2722_);
v___x_2725_ = lean_apply_2(v_k_2720_, v___x_2723_, v___x_2724_);
return v___x_2725_;
}
else
{
lean_object* v_sep_2726_; uint8_t v_unindentedRb_2727_; uint8_t v_stickynessKind_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_sep_2726_ = lean_ctor_get(v_t_2719_, 0);
lean_inc_ref(v_sep_2726_);
v_unindentedRb_2727_ = lean_ctor_get_uint8(v_t_2719_, sizeof(void*)*1);
v_stickynessKind_2728_ = lean_ctor_get_uint8(v_t_2719_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_2719_, 1);
v___x_2729_ = lean_box(v_unindentedRb_2727_);
v___x_2730_ = lean_box(v_stickynessKind_2728_);
v___x_2731_ = lean_apply_3(v_k_2720_, v_sep_2726_, v___x_2729_, v___x_2730_);
return v___x_2731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(lean_object* v_motive_2732_, lean_object* v_ctorIdx_2733_, lean_object* v_t_2734_, lean_object* v_h_2735_, lean_object* v_k_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2734_, v_k_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___boxed(lean_object* v_motive_2738_, lean_object* v_ctorIdx_2739_, lean_object* v_t_2740_, lean_object* v_h_2741_, lean_object* v_k_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(v_motive_2738_, v_ctorIdx_2739_, v_t_2740_, v_h_2741_, v_k_2742_);
lean_dec(v_ctorIdx_2739_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim___redArg(lean_object* v_t_2744_, lean_object* v_dense_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2744_, v_dense_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim(lean_object* v_motive_2747_, lean_object* v_t_2748_, lean_object* v_h_2749_, lean_object* v_dense_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2748_, v_dense_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim___redArg(lean_object* v_t_2752_, lean_object* v_sparse_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2752_, v_sparse_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim(lean_object* v_motive_2755_, lean_object* v_t_2756_, lean_object* v_h_2757_, lean_object* v_sparse_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2756_, v_sparse_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object* v_lb_2760_, lean_object* v_rb_2761_, uint8_t v_isBodyAligned_2762_, lean_object* v_bodyPseudoAligned_x3f_2763_, uint8_t v___x_2764_, lean_object* v_body_2765_){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v_doc_2772_; 
v___x_2766_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2765_);
v___x_2767_ = lean_unsigned_to_nat(3u);
v___x_2768_ = lean_mk_empty_array_with_capacity(v___x_2767_);
v___x_2769_ = lean_array_push(v___x_2768_, v_lb_2760_);
v___x_2770_ = lean_array_push(v___x_2769_, v___x_2766_);
v___x_2771_ = lean_array_push(v___x_2770_, v_rb_2761_);
v_doc_2772_ = l_Lean_Fmt_Layouts_atomic(v___x_2771_);
lean_dec_ref(v___x_2771_);
if (v_isBodyAligned_2762_ == 0)
{
if (lean_obj_tag(v_bodyPseudoAligned_x3f_2763_) == 1)
{
lean_object* v_val_2773_; uint8_t v___x_2774_; lean_object* v_doc_2775_; lean_object* v___x_2776_; 
v_val_2773_ = lean_ctor_get(v_bodyPseudoAligned_x3f_2763_, 0);
v___x_2774_ = lean_unbox(v_val_2773_);
v_doc_2775_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2772_, v___x_2774_);
v___x_2776_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2775_, v___x_2764_);
return v___x_2776_;
}
else
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2772_, v___x_2764_);
return v___x_2777_;
}
}
else
{
lean_object* v_doc_2778_; lean_object* v___x_2779_; 
v_doc_2778_ = l_Lean_Fmt_TaggedDoc_aligned(v_doc_2772_);
v___x_2779_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2778_, v___x_2764_);
return v___x_2779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0___boxed(lean_object* v_lb_2780_, lean_object* v_rb_2781_, lean_object* v_isBodyAligned_2782_, lean_object* v_bodyPseudoAligned_x3f_2783_, lean_object* v___x_2784_, lean_object* v_body_2785_){
_start:
{
uint8_t v_isBodyAligned_boxed_2786_; uint8_t v___x_701__boxed_2787_; lean_object* v_res_2788_; 
v_isBodyAligned_boxed_2786_ = lean_unbox(v_isBodyAligned_2782_);
v___x_701__boxed_2787_ = lean_unbox(v___x_2784_);
v_res_2788_ = l_Lean_Fmt_Layouts_bracketed___lam__0(v_lb_2780_, v_rb_2781_, v_isBodyAligned_boxed_2786_, v_bodyPseudoAligned_x3f_2783_, v___x_701__boxed_2787_, v_body_2785_);
lean_dec(v_bodyPseudoAligned_x3f_2783_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object* v_lb_2792_, lean_object* v_body_2793_, lean_object* v_rb_2794_, lean_object* v_format_2795_){
_start:
{
uint8_t v___x_2796_; 
v___x_2796_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2793_);
if (v___x_2796_ == 0)
{
lean_object* v_doc_2797_; uint8_t v___x_2798_; 
v_doc_2797_ = lean_ctor_get(v_body_2793_, 0);
v___x_2798_ = 1;
if (lean_obj_tag(v_format_2795_) == 0)
{
uint8_t v_spacing_2799_; 
v_spacing_2799_ = lean_ctor_get_uint8(v_format_2795_, 0);
if (v_spacing_2799_ == 0)
{
uint8_t v_alwaysPropagateStickiness_2800_; uint8_t v_isBodyAligned_2801_; lean_object* v_bodyPseudoAligned_x3f_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v_f_2805_; 
v_alwaysPropagateStickiness_2800_ = lean_ctor_get_uint8(v_format_2795_, 1);
lean_dec_ref_known(v_format_2795_, 0);
lean_inc(v_doc_2797_);
v_isBodyAligned_2801_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2797_);
lean_inc_ref(v_body_2793_);
v_bodyPseudoAligned_x3f_2802_ = l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(v_body_2793_);
v___x_2803_ = lean_box(v_isBodyAligned_2801_);
v___x_2804_ = lean_box(v___x_2798_);
lean_inc(v_bodyPseudoAligned_x3f_2802_);
lean_inc_ref(v_rb_2794_);
lean_inc_ref(v_lb_2792_);
v_f_2805_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_bracketed___lam__0___boxed), 6, 5);
lean_closure_set(v_f_2805_, 0, v_lb_2792_);
lean_closure_set(v_f_2805_, 1, v_rb_2794_);
lean_closure_set(v_f_2805_, 2, v___x_2803_);
lean_closure_set(v_f_2805_, 3, v_bodyPseudoAligned_x3f_2802_);
lean_closure_set(v_f_2805_, 4, v___x_2804_);
if (v_alwaysPropagateStickiness_2800_ == 0)
{
uint8_t v___x_2809_; 
lean_inc_ref(v_body_2793_);
v___x_2809_ = l_Lean_Fmt_TaggedDoc_isBracketed(v_body_2793_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec_ref(v_f_2805_);
v___x_2810_ = l_Lean_Fmt_Layouts_bracketed___lam__0(v_lb_2792_, v_rb_2794_, v_isBodyAligned_2801_, v_bodyPseudoAligned_x3f_2802_, v___x_2798_, v_body_2793_);
lean_dec(v_bodyPseudoAligned_x3f_2802_);
return v___x_2810_;
}
else
{
lean_dec(v_bodyPseudoAligned_x3f_2802_);
lean_dec_ref(v_rb_2794_);
lean_dec_ref(v_lb_2792_);
goto v___jp_2806_;
}
}
else
{
lean_dec(v_bodyPseudoAligned_x3f_2802_);
lean_dec_ref(v_rb_2794_);
lean_dec_ref(v_lb_2792_);
goto v___jp_2806_;
}
v___jp_2806_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l_Lean_Fmt_Layouts_bracketed___closed__0));
v___x_2808_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_body_2793_, v_f_2805_, v___x_2807_);
return v___x_2808_;
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
lean_dec_ref_known(v_format_2795_, 0);
v___x_2811_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2793_);
v___x_2812_ = lean_unsigned_to_nat(3u);
v___x_2813_ = lean_mk_empty_array_with_capacity(v___x_2812_);
v___x_2814_ = lean_array_push(v___x_2813_, v_lb_2792_);
v___x_2815_ = lean_array_push(v___x_2814_, v___x_2811_);
v___x_2816_ = lean_array_push(v___x_2815_, v_rb_2794_);
v___x_2817_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2816_);
lean_dec_ref(v___x_2816_);
return v___x_2817_;
}
}
else
{
lean_object* v_sep_2818_; uint8_t v_unindentedRb_2819_; uint8_t v_stickynessKind_2820_; lean_object* v_sparse_2822_; lean_object* v___y_2833_; lean_object* v___y_2836_; lean_object* v___y_2848_; lean_object* v___y_2860_; lean_object* v_body_2872_; uint8_t v___x_2873_; 
v_sep_2818_ = lean_ctor_get(v_format_2795_, 0);
lean_inc_ref(v_sep_2818_);
v_unindentedRb_2819_ = lean_ctor_get_uint8(v_format_2795_, sizeof(void*)*1);
v_stickynessKind_2820_ = lean_ctor_get_uint8(v_format_2795_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_format_2795_, 1);
v_body_2872_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_2793_);
v___x_2873_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2818_);
if (v___x_2873_ == 0)
{
uint8_t v___x_2874_; 
v___x_2874_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2872_);
if (v___x_2874_ == 0)
{
lean_object* v_doc_2875_; lean_object* v_doc_2876_; uint8_t v___x_2877_; 
v_doc_2875_ = lean_ctor_get(v_sep_2818_, 0);
v_doc_2876_ = lean_ctor_get(v_body_2872_, 0);
lean_inc(v_doc_2876_);
lean_dec_ref(v_body_2872_);
v___x_2877_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2875_);
if (v___x_2877_ == 0)
{
uint8_t v___x_2878_; 
v___x_2878_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2876_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_inc(v_doc_2875_);
v___x_2879_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2875_, v_doc_2876_);
v___x_2880_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2879_);
v___y_2860_ = v___x_2880_;
goto v___jp_2859_;
}
else
{
lean_object* v___x_2881_; 
lean_dec(v_doc_2876_);
lean_inc(v_doc_2875_);
v___x_2881_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2875_);
v___y_2860_ = v___x_2881_;
goto v___jp_2859_;
}
}
else
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2876_);
v___y_2860_ = v___x_2882_;
goto v___jp_2859_;
}
}
else
{
lean_dec_ref(v_body_2872_);
lean_inc_ref(v_sep_2818_);
v___y_2860_ = v_sep_2818_;
goto v___jp_2859_;
}
}
else
{
v___y_2860_ = v_body_2872_;
goto v___jp_2859_;
}
v___jp_2821_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v_stickyVariant_2829_; lean_object* v_nonStickyVariant_2830_; lean_object* v___x_2831_; 
lean_inc_ref(v_sparse_2822_);
v___x_2823_ = l_Lean_Fmt_TaggedDoc_aligned(v_sparse_2822_);
v___x_2824_ = lean_unsigned_to_nat(2u);
v___x_2825_ = lean_mk_empty_array_with_capacity(v___x_2824_);
v___x_2826_ = lean_array_push(v___x_2825_, v_sparse_2822_);
v___x_2827_ = lean_array_push(v___x_2826_, v___x_2823_);
v___x_2828_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2827_);
v_stickyVariant_2829_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_2828_, v___x_2798_);
lean_inc_ref(v_stickyVariant_2829_);
v_nonStickyVariant_2830_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_stickyVariant_2829_);
v___x_2831_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_2830_, v_stickyVariant_2829_, v_stickynessKind_2820_);
return v___x_2831_;
}
v___jp_2832_:
{
if (v_unindentedRb_2819_ == 0)
{
v_sparse_2822_ = v___y_2833_;
goto v___jp_2821_;
}
else
{
lean_object* v_sparse_2834_; 
v_sparse_2834_ = l_Lean_Fmt_TaggedDoc_unindented(v___y_2833_, v___x_2798_);
v_sparse_2822_ = v_sparse_2834_;
goto v___jp_2821_;
}
}
v___jp_2835_:
{
uint8_t v___x_2837_; 
v___x_2837_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_2836_);
if (v___x_2837_ == 0)
{
uint8_t v___x_2838_; 
v___x_2838_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rb_2794_);
if (v___x_2838_ == 0)
{
lean_object* v_doc_2839_; lean_object* v_doc_2840_; uint8_t v___x_2841_; 
v_doc_2839_ = lean_ctor_get(v___y_2836_, 0);
lean_inc(v_doc_2839_);
lean_dec_ref(v___y_2836_);
v_doc_2840_ = lean_ctor_get(v_rb_2794_, 0);
lean_inc(v_doc_2840_);
lean_dec_ref(v_rb_2794_);
v___x_2841_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2839_);
if (v___x_2841_ == 0)
{
uint8_t v___x_2842_; 
v___x_2842_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2840_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2839_, v_doc_2840_);
v___x_2844_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2843_);
v___y_2833_ = v___x_2844_;
goto v___jp_2832_;
}
else
{
lean_object* v___x_2845_; 
lean_dec(v_doc_2840_);
v___x_2845_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2839_);
v___y_2833_ = v___x_2845_;
goto v___jp_2832_;
}
}
else
{
lean_object* v___x_2846_; 
lean_dec(v_doc_2839_);
v___x_2846_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2840_);
v___y_2833_ = v___x_2846_;
goto v___jp_2832_;
}
}
else
{
lean_dec_ref(v_rb_2794_);
v___y_2833_ = v___y_2836_;
goto v___jp_2832_;
}
}
else
{
lean_dec_ref(v___y_2836_);
v___y_2833_ = v_rb_2794_;
goto v___jp_2832_;
}
}
v___jp_2847_:
{
uint8_t v___x_2849_; 
v___x_2849_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_2848_);
if (v___x_2849_ == 0)
{
uint8_t v___x_2850_; 
v___x_2850_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2818_);
if (v___x_2850_ == 0)
{
lean_object* v_doc_2851_; lean_object* v_doc_2852_; uint8_t v___x_2853_; 
v_doc_2851_ = lean_ctor_get(v___y_2848_, 0);
lean_inc(v_doc_2851_);
lean_dec_ref(v___y_2848_);
v_doc_2852_ = lean_ctor_get(v_sep_2818_, 0);
lean_inc(v_doc_2852_);
lean_dec_ref(v_sep_2818_);
v___x_2853_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2851_);
if (v___x_2853_ == 0)
{
uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2852_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2851_, v_doc_2852_);
v___x_2856_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2855_);
v___y_2836_ = v___x_2856_;
goto v___jp_2835_;
}
else
{
lean_object* v___x_2857_; 
lean_dec(v_doc_2852_);
v___x_2857_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2851_);
v___y_2836_ = v___x_2857_;
goto v___jp_2835_;
}
}
else
{
lean_object* v___x_2858_; 
lean_dec(v_doc_2851_);
v___x_2858_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2852_);
v___y_2836_ = v___x_2858_;
goto v___jp_2835_;
}
}
else
{
lean_dec_ref(v_sep_2818_);
v___y_2836_ = v___y_2848_;
goto v___jp_2835_;
}
}
else
{
lean_dec_ref(v___y_2848_);
v___y_2836_ = v_sep_2818_;
goto v___jp_2835_;
}
}
v___jp_2859_:
{
lean_object* v___x_2861_; uint8_t v___x_2862_; 
v___x_2861_ = l_Lean_Fmt_TaggedDoc_hardNested(v___y_2860_);
v___x_2862_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_lb_2792_);
if (v___x_2862_ == 0)
{
uint8_t v___x_2863_; 
v___x_2863_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2861_);
if (v___x_2863_ == 0)
{
lean_object* v_doc_2864_; lean_object* v_doc_2865_; uint8_t v___x_2866_; 
v_doc_2864_ = lean_ctor_get(v_lb_2792_, 0);
lean_inc(v_doc_2864_);
lean_dec_ref(v_lb_2792_);
v_doc_2865_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_doc_2865_);
lean_dec_ref(v___x_2861_);
v___x_2866_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2864_);
if (v___x_2866_ == 0)
{
uint8_t v___x_2867_; 
v___x_2867_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2865_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2864_, v_doc_2865_);
v___x_2869_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2868_);
v___y_2848_ = v___x_2869_;
goto v___jp_2847_;
}
else
{
lean_object* v___x_2870_; 
lean_dec(v_doc_2865_);
v___x_2870_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2864_);
v___y_2848_ = v___x_2870_;
goto v___jp_2847_;
}
}
else
{
lean_object* v___x_2871_; 
lean_dec(v_doc_2864_);
v___x_2871_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2865_);
v___y_2848_ = v___x_2871_;
goto v___jp_2847_;
}
}
else
{
lean_dec_ref(v___x_2861_);
v___y_2848_ = v_lb_2792_;
goto v___jp_2847_;
}
}
else
{
lean_dec_ref(v_lb_2792_);
v___y_2848_ = v___x_2861_;
goto v___jp_2847_;
}
}
}
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_dec_ref(v_format_2795_);
lean_dec_ref(v_body_2793_);
v___x_2883_ = lean_unsigned_to_nat(2u);
v___x_2884_ = lean_mk_empty_array_with_capacity(v___x_2883_);
v___x_2885_ = lean_array_push(v___x_2884_, v_lb_2792_);
v___x_2886_ = lean_array_push(v___x_2885_, v_rb_2794_);
v___x_2887_ = l_Lean_Fmt_Layouts_atomic(v___x_2886_);
lean_dec_ref(v___x_2886_);
return v___x_2887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object* v_lbTk_2891_, lean_object* v_body_2892_, lean_object* v_rbTk_2893_){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_2895_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2891_, v_body_2892_, v_rbTk_2893_, v___x_2894_);
return v___x_2895_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0(void){
_start:
{
uint8_t v___x_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2896_ = 1;
v___x_2897_ = 1;
v___x_2898_ = l_Lean_Fmt_TaggedDoc_break;
v___x_2899_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
lean_ctor_set_uint8(v___x_2899_, sizeof(void*)*1, v___x_2897_);
lean_ctor_set_uint8(v___x_2899_, sizeof(void*)*1 + 1, v___x_2896_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object* v_lbTk_2900_, lean_object* v_seq_2901_, lean_object* v_rbTk_2902_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_obj_once(&l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0, &l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0);
v___x_2904_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2900_, v_seq_2901_, v_rbTk_2902_, v___x_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(uint8_t v_isComplex_2905_, lean_object* v_subAlts_2906_){
_start:
{
if (v_isComplex_2905_ == 0)
{
uint8_t v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = 1;
v___x_2908_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_subAlts_2906_, v___x_2907_);
return v___x_2908_;
}
else
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_Fmt_Layouts_lines(v_subAlts_2906_);
return v___x_2909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts___boxed(lean_object* v_isComplex_2910_, lean_object* v_subAlts_2911_){
_start:
{
uint8_t v_isComplex_boxed_2912_; lean_object* v_res_2913_; 
v_isComplex_boxed_2912_ = lean_unbox(v_isComplex_2910_);
v_res_2913_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_boxed_2912_, v_subAlts_2911_);
lean_dec_ref(v_subAlts_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t v_sz_2914_, size_t v_i_2915_, lean_object* v_bs_2916_){
_start:
{
uint8_t v___x_2917_; 
v___x_2917_ = lean_usize_dec_lt(v_i_2915_, v_sz_2914_);
if (v___x_2917_ == 0)
{
return v_bs_2916_;
}
else
{
lean_object* v_v_2918_; lean_object* v___x_2919_; lean_object* v_bs_x27_2920_; lean_object* v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; lean_object* v___x_2924_; 
v_v_2918_ = lean_array_uget(v_bs_2916_, v_i_2915_);
v___x_2919_ = lean_unsigned_to_nat(0u);
v_bs_x27_2920_ = lean_array_uset(v_bs_2916_, v_i_2915_, v___x_2919_);
v___x_2921_ = l_Lean_Fmt_TaggedDoc_nested(v_v_2918_);
v___x_2922_ = ((size_t)1ULL);
v___x_2923_ = lean_usize_add(v_i_2915_, v___x_2922_);
v___x_2924_ = lean_array_uset(v_bs_x27_2920_, v_i_2915_, v___x_2921_);
v_i_2915_ = v___x_2923_;
v_bs_2916_ = v___x_2924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object* v_sz_2926_, lean_object* v_i_2927_, lean_object* v_bs_2928_){
_start:
{
size_t v_sz_boxed_2929_; size_t v_i_boxed_2930_; lean_object* v_res_2931_; 
v_sz_boxed_2929_ = lean_unbox_usize(v_sz_2926_);
lean_dec(v_sz_2926_);
v_i_boxed_2930_ = lean_unbox_usize(v_i_2927_);
lean_dec(v_i_2927_);
v_res_2931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_boxed_2929_, v_i_boxed_2930_, v_bs_2928_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object* v_subAlts_2932_, lean_object* v_arrowTk_2933_, lean_object* v_rhs_2934_, uint8_t v_isComplex_2935_){
_start:
{
lean_object* v___y_2937_; uint8_t v___y_2938_; lean_object* v___y_2939_; uint8_t v___y_2979_; uint8_t v___x_2993_; 
v___x_2993_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_arrowTk_2933_);
if (v___x_2993_ == 0)
{
v___y_2979_ = v___x_2993_;
goto v___jp_2978_;
}
else
{
uint8_t v___x_2994_; 
v___x_2994_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_2934_);
if (v___x_2994_ == 0)
{
v___y_2979_ = v___x_2994_;
goto v___jp_2978_;
}
else
{
lean_object* v_subAlts_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
lean_dec_ref(v_rhs_2934_);
lean_dec_ref(v_arrowTk_2933_);
v_subAlts_2995_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_2935_, v_subAlts_2932_);
lean_dec_ref(v_subAlts_2932_);
lean_inc_ref(v_subAlts_2995_);
v___x_2996_ = l_Lean_Fmt_TaggedDoc_flattened(v_subAlts_2995_);
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
lean_ctor_set(v___x_2997_, 1, v_subAlts_2995_);
return v___x_2997_;
}
}
v___jp_2936_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v_lhs_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_nonStickyDoc_2955_; lean_object* v_flat_2956_; lean_object* v___x_2957_; 
v___x_2940_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_2935_, v___y_2939_);
lean_dec_ref(v___y_2939_);
v___x_2941_ = lean_unsigned_to_nat(2u);
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2941_);
lean_inc_ref_n(v___x_2942_, 2);
v___x_2943_ = lean_array_push(v___x_2942_, v___x_2940_);
v___x_2944_ = lean_array_push(v___x_2943_, v_arrowTk_2933_);
v_lhs_2945_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2944_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_lhs_2945_);
v___x_2947_ = l_Lean_Fmt_TaggedDoc_nl;
lean_inc_ref(v___y_2937_);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v___y_2937_);
lean_inc_ref(v___x_2946_);
v___x_2949_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2946_, v___x_2948_);
v___x_2950_ = lean_box(0);
lean_inc_ref(v_rhs_2934_);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_rhs_2934_);
v___x_2952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
lean_ctor_set(v___x_2952_, 2, v___x_2950_);
v___x_2953_ = lean_array_push(v___x_2942_, v___x_2949_);
v___x_2954_ = lean_array_push(v___x_2953_, v___x_2952_);
v_nonStickyDoc_2955_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2954_);
lean_dec_ref(v___x_2954_);
lean_inc_ref(v_nonStickyDoc_2955_);
v_flat_2956_ = l_Lean_Fmt_TaggedDoc_flattened(v_nonStickyDoc_2955_);
v___x_2957_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_2934_);
if (lean_obj_tag(v___x_2957_) == 1)
{
lean_object* v_val_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2976_; 
v_val_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2976_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_val_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2976_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v_stickyVariant_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v_stickyVariant_2962_ = lean_ctor_get(v_val_2958_, 0);
v___x_2963_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v___y_2937_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v___y_2937_);
v___x_2965_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2946_, v___x_2964_);
lean_inc_ref(v_stickyVariant_2962_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v_stickyVariant_2962_);
v___x_2967_ = v___x_2960_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_stickyVariant_2962_);
v___x_2967_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_stickyDoc_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2950_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
lean_ctor_set(v___x_2968_, 2, v___x_2950_);
v___x_2969_ = lean_array_push(v___x_2942_, v___x_2965_);
v___x_2970_ = lean_array_push(v___x_2969_, v___x_2968_);
v_stickyDoc_2971_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2970_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_2958_, v___y_2938_);
lean_dec(v_val_2958_);
v___x_2973_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_2955_, v_stickyDoc_2971_, v___x_2972_);
lean_dec(v___x_2972_);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v_flat_2956_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
return v___x_2974_;
}
}
}
else
{
lean_object* v___x_2977_; 
lean_dec(v___x_2957_);
lean_dec_ref_known(v___x_2946_, 1);
lean_dec_ref(v___x_2942_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v_flat_2956_);
lean_ctor_set(v___x_2977_, 1, v_nonStickyDoc_2955_);
return v___x_2977_;
}
}
v___jp_2978_:
{
lean_object* v___x_2980_; size_t v_sz_2981_; size_t v___x_2982_; lean_object* v_subAlts_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2980_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v_sz_2981_ = lean_array_size(v_subAlts_2932_);
v___x_2982_ = ((size_t)0ULL);
v_subAlts_2983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_2981_, v___x_2982_, v_subAlts_2932_);
v___x_2984_ = lean_array_get_size(v_subAlts_2983_);
v___x_2985_ = lean_unsigned_to_nat(1u);
v___x_2986_ = lean_nat_sub(v___x_2984_, v___x_2985_);
v___x_2987_ = lean_nat_dec_lt(v___x_2986_, v___x_2984_);
if (v___x_2987_ == 0)
{
lean_dec(v___x_2986_);
v___y_2937_ = v___x_2980_;
v___y_2938_ = v___y_2979_;
v___y_2939_ = v_subAlts_2983_;
goto v___jp_2936_;
}
else
{
lean_object* v_v_2988_; lean_object* v___x_2989_; lean_object* v_xs_x27_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_v_2988_ = lean_array_fget(v_subAlts_2983_, v___x_2986_);
v___x_2989_ = lean_box(0);
v_xs_x27_2990_ = lean_array_fset(v_subAlts_2983_, v___x_2986_, v___x_2989_);
v___x_2991_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2988_);
v___x_2992_ = lean_array_fset(v_xs_x27_2990_, v___x_2986_, v___x_2991_);
lean_dec(v___x_2986_);
v___y_2937_ = v___x_2980_;
v___y_2938_ = v___y_2979_;
v___y_2939_ = v___x_2992_;
goto v___jp_2936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt___boxed(lean_object* v_subAlts_2998_, lean_object* v_arrowTk_2999_, lean_object* v_rhs_3000_, lean_object* v_isComplex_3001_){
_start:
{
uint8_t v_isComplex_boxed_3002_; lean_object* v_res_3003_; 
v_isComplex_boxed_3002_ = lean_unbox(v_isComplex_3001_);
v_res_3003_ = l_Lean_Fmt_Layouts_alt(v_subAlts_2998_, v_arrowTk_2999_, v_rhs_3000_, v_isComplex_boxed_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t v_sz_3004_, size_t v_i_3005_, lean_object* v_bs_3006_){
_start:
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_usize_dec_lt(v_i_3005_, v_sz_3004_);
if (v___x_3007_ == 0)
{
return v_bs_3006_;
}
else
{
lean_object* v_v_3008_; lean_object* v_nonFlat_3009_; lean_object* v___x_3010_; lean_object* v_bs_x27_3011_; size_t v___x_3012_; size_t v___x_3013_; lean_object* v___x_3014_; 
v_v_3008_ = lean_array_uget_borrowed(v_bs_3006_, v_i_3005_);
v_nonFlat_3009_ = lean_ctor_get(v_v_3008_, 1);
lean_inc_ref(v_nonFlat_3009_);
v___x_3010_ = lean_unsigned_to_nat(0u);
v_bs_x27_3011_ = lean_array_uset(v_bs_3006_, v_i_3005_, v___x_3010_);
v___x_3012_ = ((size_t)1ULL);
v___x_3013_ = lean_usize_add(v_i_3005_, v___x_3012_);
v___x_3014_ = lean_array_uset(v_bs_x27_3011_, v_i_3005_, v_nonFlat_3009_);
v_i_3005_ = v___x_3013_;
v_bs_3006_ = v___x_3014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object* v_sz_3016_, lean_object* v_i_3017_, lean_object* v_bs_3018_){
_start:
{
size_t v_sz_boxed_3019_; size_t v_i_boxed_3020_; lean_object* v_res_3021_; 
v_sz_boxed_3019_ = lean_unbox_usize(v_sz_3016_);
lean_dec(v_sz_3016_);
v_i_boxed_3020_ = lean_unbox_usize(v_i_3017_);
lean_dec(v_i_3017_);
v_res_3021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_boxed_3019_, v_i_boxed_3020_, v_bs_3018_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1(lean_object* v_as_3022_, size_t v_sz_3023_, size_t v_i_3024_, lean_object* v_b_3025_){
_start:
{
uint8_t v___x_3026_; 
v___x_3026_ = lean_usize_dec_lt(v_i_3024_, v_sz_3023_);
if (v___x_3026_ == 0)
{
return v_b_3025_;
}
else
{
lean_object* v_snd_3027_; lean_object* v_fst_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3073_; 
v_snd_3027_ = lean_ctor_get(v_b_3025_, 1);
v_fst_3028_ = lean_ctor_get(v_b_3025_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v_b_3025_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3030_ = v_b_3025_;
v_isShared_3031_ = v_isSharedCheck_3073_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_snd_3027_);
lean_inc(v_fst_3028_);
lean_dec(v_b_3025_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3073_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v_fst_3032_; lean_object* v_snd_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3072_; 
v_fst_3032_ = lean_ctor_get(v_snd_3027_, 0);
v_snd_3033_ = lean_ctor_get(v_snd_3027_, 1);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_snd_3027_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3035_ = v_snd_3027_;
v_isShared_3036_ = v_isSharedCheck_3072_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_snd_3033_);
lean_inc(v_fst_3032_);
lean_dec(v_snd_3027_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3072_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v_a_3037_; lean_object* v___y_3039_; 
v_a_3037_ = lean_array_uget_borrowed(v_as_3022_, v_i_3024_);
if (lean_obj_tag(v_fst_3032_) == 0)
{
lean_object* v_flatSuffix_3065_; 
v_flatSuffix_3065_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_3039_ = v_flatSuffix_3065_;
goto v___jp_3038_;
}
else
{
lean_object* v_val_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_val_3066_ = lean_ctor_get(v_fst_3032_, 0);
lean_inc(v_val_3066_);
lean_dec_ref_known(v_fst_3032_, 1);
v___x_3067_ = lean_unsigned_to_nat(2u);
v___x_3068_ = lean_mk_empty_array_with_capacity(v___x_3067_);
v___x_3069_ = lean_array_push(v___x_3068_, v_val_3066_);
lean_inc(v_fst_3028_);
v___x_3070_ = lean_array_push(v___x_3069_, v_fst_3028_);
v___x_3071_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3070_);
v___y_3039_ = v___x_3071_;
goto v___jp_3038_;
}
v___jp_3038_:
{
lean_object* v_flat_3040_; lean_object* v_nonFlat_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v_flat_3040_ = lean_ctor_get(v_a_3037_, 0);
v_nonFlat_3041_ = lean_ctor_get(v_a_3037_, 1);
v___x_3042_ = lean_unsigned_to_nat(2u);
v___x_3043_ = lean_mk_empty_array_with_capacity(v___x_3042_);
lean_inc_ref(v_nonFlat_3041_);
lean_inc_ref_n(v___x_3043_, 2);
v___x_3044_ = lean_array_push(v___x_3043_, v_nonFlat_3041_);
v___x_3045_ = lean_array_push(v___x_3044_, v___y_3039_);
v___x_3046_ = l_Lean_Fmt_Layouts_lines(v___x_3045_);
lean_dec_ref(v___x_3045_);
lean_inc_ref(v_flat_3040_);
v___x_3047_ = lean_array_push(v___x_3043_, v_flat_3040_);
lean_inc_ref(v___x_3047_);
v___x_3048_ = lean_array_push(v___x_3047_, v_snd_3033_);
v___x_3049_ = l_Lean_Fmt_Layouts_lines(v___x_3048_);
lean_dec_ref(v___x_3048_);
v___x_3050_ = lean_array_push(v___x_3043_, v___x_3049_);
lean_inc_ref(v___x_3046_);
v___x_3051_ = lean_array_push(v___x_3050_, v___x_3046_);
v___x_3052_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3051_);
v___x_3053_ = lean_array_push(v___x_3047_, v_fst_3028_);
v___x_3054_ = l_Lean_Fmt_Layouts_lines(v___x_3053_);
lean_dec_ref(v___x_3053_);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3046_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 1, v___x_3052_);
lean_ctor_set(v___x_3035_, 0, v___x_3055_);
v___x_3057_ = v___x_3035_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3052_);
v___x_3057_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3059_; 
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v___x_3057_);
lean_ctor_set(v___x_3030_, 0, v___x_3054_);
v___x_3059_ = v___x_3030_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3057_);
v___x_3059_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
size_t v___x_3060_; size_t v___x_3061_; 
v___x_3060_ = ((size_t)1ULL);
v___x_3061_ = lean_usize_add(v_i_3024_, v___x_3060_);
v_i_3024_ = v___x_3061_;
v_b_3025_ = v___x_3059_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object* v_as_3074_, lean_object* v_sz_3075_, lean_object* v_i_3076_, lean_object* v_b_3077_){
_start:
{
size_t v_sz_boxed_3078_; size_t v_i_boxed_3079_; lean_object* v_res_3080_; 
v_sz_boxed_3078_ = lean_unbox_usize(v_sz_3075_);
lean_dec(v_sz_3075_);
v_i_boxed_3079_ = lean_unbox_usize(v_i_3076_);
lean_dec(v_i_3076_);
v_res_3080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1(v_as_3074_, v_sz_boxed_3078_, v_i_boxed_3079_, v_b_3077_);
lean_dec_ref(v_as_3074_);
return v_res_3080_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_alts___closed__0(void){
_start:
{
lean_object* v_flatSuffix_3081_; lean_object* v_middle_x3f_3082_; lean_object* v___x_3083_; 
v_flatSuffix_3081_ = l_Lean_Fmt_TaggedDoc_empty;
v_middle_x3f_3082_ = lean_box(0);
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v_middle_x3f_3082_);
lean_ctor_set(v___x_3083_, 1, v_flatSuffix_3081_);
return v___x_3083_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_alts___closed__1(void){
_start:
{
lean_object* v___x_3084_; lean_object* v_flatSuffix_3085_; lean_object* v___x_3086_; 
v___x_3084_ = lean_obj_once(&l_Lean_Fmt_Layouts_alts___closed__0, &l_Lean_Fmt_Layouts_alts___closed__0_once, _init_l_Lean_Fmt_Layouts_alts___closed__0);
v_flatSuffix_3085_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3086_, 0, v_flatSuffix_3085_);
lean_ctor_set(v___x_3086_, 1, v___x_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts(lean_object* v_alts_3087_, uint8_t v_allowFlattenedAlts_3088_){
_start:
{
if (v_allowFlattenedAlts_3088_ == 0)
{
size_t v_sz_3089_; size_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_sz_3089_ = lean_array_size(v_alts_3087_);
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_3089_, v___x_3090_, v_alts_3087_);
v___x_3092_ = l_Lean_Fmt_Layouts_lines(v___x_3091_);
lean_dec_ref(v___x_3091_);
v___x_3093_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_3092_);
return v___x_3093_;
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; size_t v_sz_3096_; size_t v___x_3097_; lean_object* v___x_3098_; lean_object* v_snd_3099_; lean_object* v_snd_3100_; lean_object* v___x_3101_; 
v___x_3094_ = l_Array_reverse___redArg(v_alts_3087_);
v___x_3095_ = lean_obj_once(&l_Lean_Fmt_Layouts_alts___closed__1, &l_Lean_Fmt_Layouts_alts___closed__1_once, _init_l_Lean_Fmt_Layouts_alts___closed__1);
v_sz_3096_ = lean_array_size(v___x_3094_);
v___x_3097_ = ((size_t)0ULL);
v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1(v___x_3094_, v_sz_3096_, v___x_3097_, v___x_3095_);
lean_dec_ref(v___x_3094_);
v_snd_3099_ = lean_ctor_get(v___x_3098_, 1);
lean_inc(v_snd_3099_);
lean_dec_ref(v___x_3098_);
v_snd_3100_ = lean_ctor_get(v_snd_3099_, 1);
lean_inc(v_snd_3100_);
lean_dec(v_snd_3099_);
v___x_3101_ = l_Lean_Fmt_TaggedDoc_withPosition(v_snd_3100_);
return v___x_3101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts___boxed(lean_object* v_alts_3102_, lean_object* v_allowFlattenedAlts_3103_){
_start:
{
uint8_t v_allowFlattenedAlts_boxed_3104_; lean_object* v_res_3105_; 
v_allowFlattenedAlts_boxed_3104_ = lean_unbox(v_allowFlattenedAlts_3103_);
v_res_3105_ = l_Lean_Fmt_Layouts_alts(v_alts_3102_, v_allowFlattenedAlts_boxed_3104_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl(uint8_t v_x_3106_){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_box(v_x_3106_);
v___x_3108_ = lean_obj_tag_nat(v___x_3107_);
lean_dec(v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl___boxed(lean_object* v_x_3109_){
_start:
{
uint8_t v_x_4__boxed_3110_; lean_object* v_res_3111_; 
v_x_4__boxed_3110_ = lean_unbox(v_x_3109_);
v_res_3111_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl(v_x_4__boxed_3110_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(lean_object* v_k_3112_){
_start:
{
lean_inc(v_k_3112_);
return v_k_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg___boxed(lean_object* v_k_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(v_k_3113_);
lean_dec(v_k_3113_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(lean_object* v_motive_3115_, lean_object* v_ctorIdx_3116_, uint8_t v_t_3117_, lean_object* v_h_3118_, lean_object* v_k_3119_){
_start:
{
lean_inc(v_k_3119_);
return v_k_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___boxed(lean_object* v_motive_3120_, lean_object* v_ctorIdx_3121_, lean_object* v_t_3122_, lean_object* v_h_3123_, lean_object* v_k_3124_){
_start:
{
uint8_t v_t_boxed_3125_; lean_object* v_res_3126_; 
v_t_boxed_3125_ = lean_unbox(v_t_3122_);
v_res_3126_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(v_motive_3120_, v_ctorIdx_3121_, v_t_boxed_3125_, v_h_3123_, v_k_3124_);
lean_dec(v_k_3124_);
lean_dec(v_ctorIdx_3121_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(lean_object* v_sticky_3127_){
_start:
{
lean_inc(v_sticky_3127_);
return v_sticky_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(v_sticky_3128_);
lean_dec(v_sticky_3128_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(lean_object* v_motive_3130_, uint8_t v_t_3131_, lean_object* v_h_3132_, lean_object* v_sticky_3133_){
_start:
{
lean_inc(v_sticky_3133_);
return v_sticky_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___boxed(lean_object* v_motive_3134_, lean_object* v_t_3135_, lean_object* v_h_3136_, lean_object* v_sticky_3137_){
_start:
{
uint8_t v_t_boxed_3138_; lean_object* v_res_3139_; 
v_t_boxed_3138_ = lean_unbox(v_t_3135_);
v_res_3139_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(v_motive_3134_, v_t_boxed_3138_, v_h_3136_, v_sticky_3137_);
lean_dec(v_sticky_3137_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3140_){
_start:
{
lean_inc(v_nonSticky_3140_);
return v_nonSticky_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(v_nonSticky_3141_);
lean_dec(v_nonSticky_3141_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(lean_object* v_motive_3143_, uint8_t v_t_3144_, lean_object* v_h_3145_, lean_object* v_nonSticky_3146_){
_start:
{
lean_inc(v_nonSticky_3146_);
return v_nonSticky_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___boxed(lean_object* v_motive_3147_, lean_object* v_t_3148_, lean_object* v_h_3149_, lean_object* v_nonSticky_3150_){
_start:
{
uint8_t v_t_boxed_3151_; lean_object* v_res_3152_; 
v_t_boxed_3151_ = lean_unbox(v_t_3148_);
v_res_3152_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(v_motive_3147_, v_t_boxed_3151_, v_h_3149_, v_nonSticky_3150_);
lean_dec(v_nonSticky_3150_);
return v_res_3152_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0(void){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_3154_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
lean_ctor_set(v___x_3155_, 1, v___x_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object* v_keywordTk_3156_, lean_object* v_seq_3157_, uint8_t v_format_3158_){
_start:
{
lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v_doc_3161_; 
v___x_3159_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3160_ = 1;
v_doc_3161_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_keywordTk_3156_, v___x_3159_, v_seq_3157_, v___x_3160_);
if (v_format_3158_ == 0)
{
lean_object* v___x_3162_; uint8_t v___x_3163_; lean_object* v___x_3164_; 
lean_inc_ref(v_doc_3161_);
v___x_3162_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3161_);
v___x_3163_ = 1;
v___x_3164_ = l_Lean_Fmt_TaggedDoc_sticky(v___x_3162_, v_doc_3161_, v___x_3163_);
return v___x_3164_;
}
else
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3161_);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___boxed(lean_object* v_keywordTk_3166_, lean_object* v_seq_3167_, lean_object* v_format_3168_){
_start:
{
uint8_t v_format_boxed_3169_; lean_object* v_res_3170_; 
v_format_boxed_3169_ = lean_unbox(v_format_3168_);
v_res_3170_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_keywordTk_3166_, v_seq_3167_, v_format_boxed_3169_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl(uint8_t v_x_3171_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_box(v_x_3171_);
v___x_3173_ = lean_obj_tag_nat(v___x_3172_);
lean_dec(v___x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl___boxed(lean_object* v_x_3174_){
_start:
{
uint8_t v_x_4__boxed_3175_; lean_object* v_res_3176_; 
v_x_4__boxed_3175_ = lean_unbox(v_x_3174_);
v_res_3176_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl(v_x_4__boxed_3175_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(lean_object* v_k_3177_){
_start:
{
lean_inc(v_k_3177_);
return v_k_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg___boxed(lean_object* v_k_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(v_k_3178_);
lean_dec(v_k_3178_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(lean_object* v_motive_3180_, lean_object* v_ctorIdx_3181_, uint8_t v_t_3182_, lean_object* v_h_3183_, lean_object* v_k_3184_){
_start:
{
lean_inc(v_k_3184_);
return v_k_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___boxed(lean_object* v_motive_3185_, lean_object* v_ctorIdx_3186_, lean_object* v_t_3187_, lean_object* v_h_3188_, lean_object* v_k_3189_){
_start:
{
uint8_t v_t_boxed_3190_; lean_object* v_res_3191_; 
v_t_boxed_3190_ = lean_unbox(v_t_3187_);
v_res_3191_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(v_motive_3185_, v_ctorIdx_3186_, v_t_boxed_3190_, v_h_3188_, v_k_3189_);
lean_dec(v_k_3189_);
lean_dec(v_ctorIdx_3186_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(lean_object* v_sticky_3192_){
_start:
{
lean_inc(v_sticky_3192_);
return v_sticky_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(v_sticky_3193_);
lean_dec(v_sticky_3193_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(lean_object* v_motive_3195_, uint8_t v_t_3196_, lean_object* v_h_3197_, lean_object* v_sticky_3198_){
_start:
{
lean_inc(v_sticky_3198_);
return v_sticky_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___boxed(lean_object* v_motive_3199_, lean_object* v_t_3200_, lean_object* v_h_3201_, lean_object* v_sticky_3202_){
_start:
{
uint8_t v_t_boxed_3203_; lean_object* v_res_3204_; 
v_t_boxed_3203_ = lean_unbox(v_t_3200_);
v_res_3204_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(v_motive_3199_, v_t_boxed_3203_, v_h_3201_, v_sticky_3202_);
lean_dec(v_sticky_3202_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3205_){
_start:
{
lean_inc(v_nonSticky_3205_);
return v_nonSticky_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(v_nonSticky_3206_);
lean_dec(v_nonSticky_3206_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(lean_object* v_motive_3208_, uint8_t v_t_3209_, lean_object* v_h_3210_, lean_object* v_nonSticky_3211_){
_start:
{
lean_inc(v_nonSticky_3211_);
return v_nonSticky_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___boxed(lean_object* v_motive_3212_, lean_object* v_t_3213_, lean_object* v_h_3214_, lean_object* v_nonSticky_3215_){
_start:
{
uint8_t v_t_boxed_3216_; lean_object* v_res_3217_; 
v_t_boxed_3216_ = lean_unbox(v_t_3213_);
v_res_3217_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(v_motive_3212_, v_t_boxed_3216_, v_h_3214_, v_nonSticky_3215_);
lean_dec(v_nonSticky_3215_);
return v_res_3217_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_3219_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_ctor_set(v___x_3220_, 1, v___x_3218_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object* v_keyword_3221_, lean_object* v_term_3222_, uint8_t v_format_3223_){
_start:
{
uint8_t v___x_3224_; 
v___x_3224_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_term_3222_);
if (v___x_3224_ == 0)
{
uint8_t v___x_3225_; lean_object* v___y_3227_; uint8_t v___x_3259_; 
v___x_3225_ = 1;
lean_inc_ref(v_term_3222_);
v___x_3259_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_term_3222_, v___x_3224_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
lean_inc_ref(v_keyword_3221_);
v___x_3260_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3221_);
v___x_3261_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_term_3222_);
v___x_3262_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3260_, v___x_3261_, v_term_3222_, v___x_3225_);
v___x_3263_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3262_);
v___y_3227_ = v___x_3263_;
goto v___jp_3226_;
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_inc_ref(v_keyword_3221_);
v___x_3264_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3221_);
v___x_3265_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v_term_3222_);
v___x_3266_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3264_, v___x_3265_, v_term_3222_, v___x_3225_);
v___y_3227_ = v___x_3266_;
goto v___jp_3226_;
}
v___jp_3226_:
{
if (v_format_3223_ == 0)
{
lean_object* v___x_3228_; 
lean_inc_ref(v_term_3222_);
v___x_3228_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_term_3222_);
if (lean_obj_tag(v___x_3228_) == 1)
{
lean_object* v_val_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3253_; 
v_val_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3253_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_val_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3253_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
uint8_t v_kind_3233_; 
v_kind_3233_ = lean_ctor_get_uint8(v_val_3229_, sizeof(void*)*1);
lean_dec(v_val_3229_);
if (v_kind_3233_ == 1)
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3234_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3221_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3234_);
v___x_3236_ = v___x_3231_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3237_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3238_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3236_, v___x_3237_);
v___x_3239_ = lean_box(0);
v___x_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3240_, 0, v_term_3222_);
v___x_3241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3239_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
lean_ctor_set(v___x_3241_, 2, v___x_3239_);
v___x_3242_ = lean_unsigned_to_nat(2u);
v___x_3243_ = lean_mk_empty_array_with_capacity(v___x_3242_);
v___x_3244_ = lean_array_push(v___x_3243_, v___x_3238_);
v___x_3245_ = lean_array_push(v___x_3244_, v___x_3241_);
v___x_3246_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3245_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3227_, v___x_3246_, v_kind_3233_);
return v___x_3247_;
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_del_object(v___x_3231_);
v___x_3249_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3221_);
v___x_3250_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3251_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3249_, v___x_3250_, v_term_3222_, v___x_3225_);
v___x_3252_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3227_, v___x_3251_, v_kind_3233_);
return v___x_3252_;
}
}
}
else
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; 
lean_dec(v___x_3228_);
v___x_3254_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3221_);
v___x_3255_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3256_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3254_, v___x_3255_, v_term_3222_, v___x_3225_);
v___x_3257_ = 0;
v___x_3258_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3227_, v___x_3256_, v___x_3257_);
return v___x_3258_;
}
}
else
{
lean_dec_ref(v_term_3222_);
lean_dec_ref(v_keyword_3221_);
return v___y_3227_;
}
}
}
else
{
uint8_t v___x_3267_; 
lean_dec_ref(v_term_3222_);
v___x_3267_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keyword_3221_);
if (v___x_3267_ == 0)
{
if (v_format_3223_ == 0)
{
lean_object* v___x_3268_; uint8_t v___x_3269_; lean_object* v___x_3270_; 
lean_inc_ref(v_keyword_3221_);
v___x_3268_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3221_);
v___x_3269_ = 0;
v___x_3270_ = l_Lean_Fmt_TaggedDoc_sticky(v_keyword_3221_, v___x_3268_, v___x_3269_);
return v___x_3270_;
}
else
{
return v_keyword_3221_;
}
}
else
{
lean_object* v___x_3271_; 
lean_dec_ref(v_keyword_3221_);
v___x_3271_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___boxed(lean_object* v_keyword_3272_, lean_object* v_term_3273_, lean_object* v_format_3274_){
_start:
{
uint8_t v_format_boxed_3275_; lean_object* v_res_3276_; 
v_format_boxed_3275_ = lean_unbox(v_format_3274_);
v_res_3276_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3272_, v_term_3273_, v_format_boxed_3275_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl(uint8_t v_x_3277_){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = lean_box(v_x_3277_);
v___x_3279_ = lean_obj_tag_nat(v___x_3278_);
lean_dec(v___x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl___boxed(lean_object* v_x_3280_){
_start:
{
uint8_t v_x_4__boxed_3281_; lean_object* v_res_3282_; 
v_x_4__boxed_3281_ = lean_unbox(v_x_3280_);
v_res_3282_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl(v_x_4__boxed_3281_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(lean_object* v_k_3283_){
_start:
{
lean_inc(v_k_3283_);
return v_k_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg___boxed(lean_object* v_k_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(v_k_3284_);
lean_dec(v_k_3284_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(lean_object* v_motive_3286_, lean_object* v_ctorIdx_3287_, uint8_t v_t_3288_, lean_object* v_h_3289_, lean_object* v_k_3290_){
_start:
{
lean_inc(v_k_3290_);
return v_k_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___boxed(lean_object* v_motive_3291_, lean_object* v_ctorIdx_3292_, lean_object* v_t_3293_, lean_object* v_h_3294_, lean_object* v_k_3295_){
_start:
{
uint8_t v_t_boxed_3296_; lean_object* v_res_3297_; 
v_t_boxed_3296_ = lean_unbox(v_t_3293_);
v_res_3297_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(v_motive_3291_, v_ctorIdx_3292_, v_t_boxed_3296_, v_h_3294_, v_k_3295_);
lean_dec(v_k_3295_);
lean_dec(v_ctorIdx_3292_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(lean_object* v_sticky_3298_){
_start:
{
lean_inc(v_sticky_3298_);
return v_sticky_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(v_sticky_3299_);
lean_dec(v_sticky_3299_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(lean_object* v_motive_3301_, uint8_t v_t_3302_, lean_object* v_h_3303_, lean_object* v_sticky_3304_){
_start:
{
lean_inc(v_sticky_3304_);
return v_sticky_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___boxed(lean_object* v_motive_3305_, lean_object* v_t_3306_, lean_object* v_h_3307_, lean_object* v_sticky_3308_){
_start:
{
uint8_t v_t_boxed_3309_; lean_object* v_res_3310_; 
v_t_boxed_3309_ = lean_unbox(v_t_3306_);
v_res_3310_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(v_motive_3305_, v_t_boxed_3309_, v_h_3307_, v_sticky_3308_);
lean_dec(v_sticky_3308_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3311_){
_start:
{
lean_inc(v_nonSticky_3311_);
return v_nonSticky_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(v_nonSticky_3312_);
lean_dec(v_nonSticky_3312_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(lean_object* v_motive_3314_, uint8_t v_t_3315_, lean_object* v_h_3316_, lean_object* v_nonSticky_3317_){
_start:
{
lean_inc(v_nonSticky_3317_);
return v_nonSticky_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___boxed(lean_object* v_motive_3318_, lean_object* v_t_3319_, lean_object* v_h_3320_, lean_object* v_nonSticky_3321_){
_start:
{
uint8_t v_t_boxed_3322_; lean_object* v_res_3323_; 
v_t_boxed_3322_ = lean_unbox(v_t_3319_);
v_res_3323_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(v_motive_3318_, v_t_boxed_3322_, v_h_3320_, v_nonSticky_3321_);
lean_dec(v_nonSticky_3321_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object* v_keyword_3324_, lean_object* v_alts_3325_, uint8_t v_format_3326_){
_start:
{
uint8_t v___x_3327_; lean_object* v_alts_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v_nonStickyDoc_3333_; 
v___x_3327_ = 1;
v_alts_3328_ = l_Lean_Fmt_Layouts_alts(v_alts_3325_, v___x_3327_);
v___x_3329_ = lean_unsigned_to_nat(2u);
v___x_3330_ = lean_mk_empty_array_with_capacity(v___x_3329_);
lean_inc_ref(v_keyword_3324_);
lean_inc_ref(v___x_3330_);
v___x_3331_ = lean_array_push(v___x_3330_, v_keyword_3324_);
lean_inc_ref(v_alts_3328_);
v___x_3332_ = lean_array_push(v___x_3331_, v_alts_3328_);
v_nonStickyDoc_3333_ = l_Lean_Fmt_Layouts_lines(v___x_3332_);
lean_dec_ref(v___x_3332_);
if (v_format_3326_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v_stickyDoc_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; 
v___x_3334_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3324_);
v___x_3335_ = lean_array_push(v___x_3330_, v___x_3334_);
v___x_3336_ = lean_array_push(v___x_3335_, v_alts_3328_);
v_stickyDoc_3337_ = l_Lean_Fmt_Layouts_lines(v___x_3336_);
lean_dec_ref(v___x_3336_);
v___x_3338_ = 0;
v___x_3339_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3333_, v_stickyDoc_3337_, v___x_3338_);
return v___x_3339_;
}
else
{
lean_dec_ref(v___x_3330_);
lean_dec_ref(v_alts_3328_);
lean_dec_ref(v_keyword_3324_);
return v_nonStickyDoc_3333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts___boxed(lean_object* v_keyword_3340_, lean_object* v_alts_3341_, lean_object* v_format_3342_){
_start:
{
uint8_t v_format_boxed_3343_; lean_object* v_res_3344_; 
v_format_boxed_3343_ = lean_unbox(v_format_3342_);
v_res_3344_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v_keyword_3340_, v_alts_3341_, v_format_boxed_3343_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl(lean_object* v_x_3345_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_obj_tag_nat(v_x_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl___boxed(lean_object* v_x_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl(v_x_3347_);
lean_dec_ref(v_x_3347_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(lean_object* v_t_3349_, lean_object* v_k_3350_){
_start:
{
lean_object* v_sepArrayFormat_3351_; lean_object* v___x_3352_; 
v_sepArrayFormat_3351_ = lean_ctor_get(v_t_3349_, 0);
lean_inc_ref(v_sepArrayFormat_3351_);
lean_dec_ref(v_t_3349_);
v___x_3352_ = lean_apply_1(v_k_3350_, v_sepArrayFormat_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(lean_object* v_motive_3353_, lean_object* v_ctorIdx_3354_, lean_object* v_t_3355_, lean_object* v_h_3356_, lean_object* v_k_3357_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3355_, v_k_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___boxed(lean_object* v_motive_3359_, lean_object* v_ctorIdx_3360_, lean_object* v_t_3361_, lean_object* v_h_3362_, lean_object* v_k_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(v_motive_3359_, v_ctorIdx_3360_, v_t_3361_, v_h_3362_, v_k_3363_);
lean_dec(v_ctorIdx_3360_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim___redArg(lean_object* v_t_3365_, lean_object* v_sticky_3366_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3365_, v_sticky_3366_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim(lean_object* v_motive_3368_, lean_object* v_t_3369_, lean_object* v_h_3370_, lean_object* v_sticky_3371_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3369_, v_sticky_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim___redArg(lean_object* v_t_3373_, lean_object* v_nonSticky_3374_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3373_, v_nonSticky_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim(lean_object* v_motive_3376_, lean_object* v_t_3377_, lean_object* v_h_3378_, lean_object* v_nonSticky_3379_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3377_, v_nonSticky_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(lean_object* v_x_3381_){
_start:
{
if (lean_obj_tag(v_x_3381_) == 0)
{
uint8_t v___x_3382_; 
v___x_3382_ = 1;
return v___x_3382_;
}
else
{
uint8_t v___x_3383_; 
v___x_3383_ = 0;
return v___x_3383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky___boxed(lean_object* v_x_3384_){
_start:
{
uint8_t v_res_3385_; lean_object* v_r_3386_; 
v_res_3385_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_x_3384_);
lean_dec_ref(v_x_3384_);
v_r_3386_ = lean_box(v_res_3385_);
return v_r_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(lean_object* v_x_3387_){
_start:
{
lean_object* v_sepArrayFormat_3388_; 
v_sepArrayFormat_3388_ = lean_ctor_get(v_x_3387_, 0);
lean_inc_ref(v_sepArrayFormat_3388_);
return v_sepArrayFormat_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat___boxed(lean_object* v_x_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(v_x_3389_);
lean_dec_ref(v_x_3389_);
return v_res_3390_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_3392_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v___x_3391_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray(lean_object* v_sep_3394_, lean_object* v_keyword_3395_, lean_object* v_sepArray_3396_, lean_object* v_format_3397_){
_start:
{
lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___x_3436_; lean_object* v___y_3438_; uint8_t v___y_3439_; lean_object* v___y_3444_; uint8_t v___y_3445_; lean_object* v___y_3461_; lean_object* v_sepArrayFormat_3465_; 
v___x_3436_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_sepArrayFormat_3465_ = lean_ctor_get(v_format_3397_, 0);
lean_inc_ref(v_sepArrayFormat_3465_);
v___y_3461_ = v_sepArrayFormat_3465_;
goto v___jp_3460_;
v___jp_3398_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v_nonStickyDoc_3425_; uint8_t v___x_3426_; 
lean_inc_ref(v_keyword_3395_);
v___x_3402_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3395_);
v___x_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
v___x_3404_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v___x_3403_);
v___x_3405_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3403_, v___x_3404_);
v___x_3406_ = lean_box(0);
lean_inc_ref(v___y_3400_);
lean_inc_ref(v_sep_3394_);
v___x_3407_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3394_, v___y_3401_, v___y_3400_);
lean_dec_ref(v___y_3401_);
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
v___x_3409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3406_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
lean_ctor_set(v___x_3409_, 2, v___x_3406_);
v___x_3410_ = lean_unsigned_to_nat(2u);
v___x_3411_ = lean_mk_empty_array_with_capacity(v___x_3410_);
lean_inc_ref_n(v___x_3411_, 3);
v___x_3412_ = lean_array_push(v___x_3411_, v___x_3405_);
v___x_3413_ = lean_array_push(v___x_3412_, v___x_3409_);
v___x_3414_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3413_);
lean_dec_ref(v___x_3413_);
v___x_3415_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_3416_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3403_, v___x_3415_);
v___x_3417_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3394_, v___y_3399_, v___y_3400_);
lean_dec_ref(v___y_3399_);
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
v___x_3419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3406_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
lean_ctor_set(v___x_3419_, 2, v___x_3406_);
v___x_3420_ = lean_array_push(v___x_3411_, v___x_3416_);
lean_inc_ref(v___x_3419_);
v___x_3421_ = lean_array_push(v___x_3420_, v___x_3419_);
v___x_3422_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3421_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = lean_array_push(v___x_3411_, v___x_3414_);
v___x_3424_ = lean_array_push(v___x_3423_, v___x_3422_);
v_nonStickyDoc_3425_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3424_);
v___x_3426_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3397_);
lean_dec_ref(v_format_3397_);
if (v___x_3426_ == 0)
{
lean_dec_ref_known(v___x_3419_, 3);
lean_dec_ref(v___x_3411_);
lean_dec_ref(v_keyword_3395_);
return v_nonStickyDoc_3425_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v_stickyDoc_3433_; uint8_t v___x_3434_; lean_object* v___x_3435_; 
v___x_3427_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3395_);
v___x_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
v___x_3429_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3430_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3428_, v___x_3429_);
v___x_3431_ = lean_array_push(v___x_3411_, v___x_3430_);
v___x_3432_ = lean_array_push(v___x_3431_, v___x_3419_);
v_stickyDoc_3433_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3432_);
lean_dec_ref(v___x_3432_);
v___x_3434_ = 0;
v___x_3435_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3425_, v_stickyDoc_3433_, v___x_3434_);
return v___x_3435_;
}
}
v___jp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = lean_unsigned_to_nat(0u);
v___x_3441_ = lean_array_get(v___x_3436_, v___y_3438_, v___x_3440_);
lean_dec_ref(v___y_3438_);
v___x_3442_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3395_, v___x_3441_, v___y_3439_);
return v___x_3442_;
}
v___jp_3443_:
{
lean_object* v_sepArray_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
lean_inc_ref(v_sep_3394_);
v_sepArray_3446_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_3394_, v_sepArray_3396_, v___y_3445_);
v___x_3447_ = lean_array_get_size(v_sepArray_3446_);
v___x_3448_ = lean_unsigned_to_nat(1u);
v___x_3449_ = lean_nat_dec_eq(v___x_3447_, v___x_3448_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = lean_nat_dec_lt(v___x_3450_, v___x_3447_);
if (v___x_3451_ == 0)
{
lean_inc_ref(v_sepArray_3446_);
v___y_3399_ = v_sepArray_3446_;
v___y_3400_ = v___y_3444_;
v___y_3401_ = v_sepArray_3446_;
goto v___jp_3398_;
}
else
{
lean_object* v_v_3452_; lean_object* v___x_3453_; lean_object* v_xs_x27_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_v_3452_ = lean_array_fget_borrowed(v_sepArray_3446_, v___x_3450_);
v___x_3453_ = lean_box(0);
lean_inc_ref(v_sepArray_3446_);
v_xs_x27_3454_ = lean_array_fset(v_sepArray_3446_, v___x_3450_, v___x_3453_);
lean_inc(v_v_3452_);
v___x_3455_ = l_Lean_Fmt_TaggedDoc_flattened(v_v_3452_);
v___x_3456_ = lean_array_fset(v_xs_x27_3454_, v___x_3450_, v___x_3455_);
v___y_3399_ = v_sepArray_3446_;
v___y_3400_ = v___y_3444_;
v___y_3401_ = v___x_3456_;
goto v___jp_3398_;
}
}
else
{
uint8_t v___x_3457_; 
lean_dec_ref(v___y_3444_);
lean_dec_ref(v_sep_3394_);
v___x_3457_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3397_);
lean_dec_ref(v_format_3397_);
if (v___x_3457_ == 0)
{
uint8_t v___x_3458_; 
v___x_3458_ = 1;
v___y_3438_ = v_sepArray_3446_;
v___y_3439_ = v___x_3458_;
goto v___jp_3437_;
}
else
{
uint8_t v___x_3459_; 
v___x_3459_ = 0;
v___y_3438_ = v_sepArray_3446_;
v___y_3439_ = v___x_3459_;
goto v___jp_3437_;
}
}
}
v___jp_3460_:
{
switch(lean_obj_tag(v___y_3461_))
{
case 1:
{
uint8_t v_trailingSep_3462_; 
v_trailingSep_3462_ = lean_ctor_get_uint8(v___y_3461_, sizeof(void*)*1 + 1);
v___y_3444_ = v___y_3461_;
v___y_3445_ = v_trailingSep_3462_;
goto v___jp_3443_;
}
case 3:
{
uint8_t v_trailingSep_3463_; 
v_trailingSep_3463_ = lean_ctor_get_uint8(v___y_3461_, sizeof(void*)*1);
v___y_3444_ = v___y_3461_;
v___y_3445_ = v_trailingSep_3463_;
goto v___jp_3443_;
}
default: 
{
uint8_t v_trailingSep_3464_; 
v_trailingSep_3464_ = lean_ctor_get_uint8(v___y_3461_, sizeof(void*)*2);
v___y_3444_ = v___y_3461_;
v___y_3445_ = v_trailingSep_3464_;
goto v___jp_3443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___boxed(lean_object* v_sep_3466_, lean_object* v_keyword_3467_, lean_object* v_sepArray_3468_, lean_object* v_format_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3466_, v_keyword_3467_, v_sepArray_3468_, v_format_3469_);
lean_dec_ref(v_sepArray_3468_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl(uint8_t v_x_3471_){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_box(v_x_3471_);
v___x_3473_ = lean_obj_tag_nat(v___x_3472_);
lean_dec(v___x_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl___boxed(lean_object* v_x_3474_){
_start:
{
uint8_t v_x_4__boxed_3475_; lean_object* v_res_3476_; 
v_x_4__boxed_3475_ = lean_unbox(v_x_3474_);
v_res_3476_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl(v_x_4__boxed_3475_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(lean_object* v_k_3477_){
_start:
{
lean_inc(v_k_3477_);
return v_k_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg___boxed(lean_object* v_k_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(v_k_3478_);
lean_dec(v_k_3478_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(lean_object* v_motive_3480_, lean_object* v_ctorIdx_3481_, uint8_t v_t_3482_, lean_object* v_h_3483_, lean_object* v_k_3484_){
_start:
{
lean_inc(v_k_3484_);
return v_k_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___boxed(lean_object* v_motive_3485_, lean_object* v_ctorIdx_3486_, lean_object* v_t_3487_, lean_object* v_h_3488_, lean_object* v_k_3489_){
_start:
{
uint8_t v_t_boxed_3490_; lean_object* v_res_3491_; 
v_t_boxed_3490_ = lean_unbox(v_t_3487_);
v_res_3491_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(v_motive_3485_, v_ctorIdx_3486_, v_t_boxed_3490_, v_h_3488_, v_k_3489_);
lean_dec(v_k_3489_);
lean_dec(v_ctorIdx_3486_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(lean_object* v_sticky_3492_){
_start:
{
lean_inc(v_sticky_3492_);
return v_sticky_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(v_sticky_3493_);
lean_dec(v_sticky_3493_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(lean_object* v_motive_3495_, uint8_t v_t_3496_, lean_object* v_h_3497_, lean_object* v_sticky_3498_){
_start:
{
lean_inc(v_sticky_3498_);
return v_sticky_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___boxed(lean_object* v_motive_3499_, lean_object* v_t_3500_, lean_object* v_h_3501_, lean_object* v_sticky_3502_){
_start:
{
uint8_t v_t_boxed_3503_; lean_object* v_res_3504_; 
v_t_boxed_3503_ = lean_unbox(v_t_3500_);
v_res_3504_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(v_motive_3499_, v_t_boxed_3503_, v_h_3501_, v_sticky_3502_);
lean_dec(v_sticky_3502_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3505_){
_start:
{
lean_inc(v_nonSticky_3505_);
return v_nonSticky_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(v_nonSticky_3506_);
lean_dec(v_nonSticky_3506_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(lean_object* v_motive_3508_, uint8_t v_t_3509_, lean_object* v_h_3510_, lean_object* v_nonSticky_3511_){
_start:
{
lean_inc(v_nonSticky_3511_);
return v_nonSticky_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___boxed(lean_object* v_motive_3512_, lean_object* v_t_3513_, lean_object* v_h_3514_, lean_object* v_nonSticky_3515_){
_start:
{
uint8_t v_t_boxed_3516_; lean_object* v_res_3517_; 
v_t_boxed_3516_ = lean_unbox(v_t_3513_);
v_res_3517_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(v_motive_3512_, v_t_boxed_3516_, v_h_3514_, v_nonSticky_3515_);
lean_dec(v_nonSticky_3515_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object* v_sep_3522_, lean_object* v_keyword_3523_, lean_object* v_sepArray_3524_, uint8_t v_format_3525_){
_start:
{
if (v_format_3525_ == 0)
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0));
v___x_3527_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3522_, v_keyword_3523_, v_sepArray_3524_, v___x_3526_);
return v___x_3527_;
}
else
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1));
v___x_3529_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3522_, v_keyword_3523_, v_sepArray_3524_, v___x_3528_);
return v___x_3529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___boxed(lean_object* v_sep_3530_, lean_object* v_keyword_3531_, lean_object* v_sepArray_3532_, lean_object* v_format_3533_){
_start:
{
uint8_t v_format_boxed_3534_; lean_object* v_res_3535_; 
v_format_boxed_3534_ = lean_unbox(v_format_3533_);
v_res_3535_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v_sep_3530_, v_keyword_3531_, v_sepArray_3532_, v_format_boxed_3534_);
lean_dec_ref(v_sepArray_3532_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(lean_object* v_format_3536_, lean_object* v_a_3537_){
_start:
{
uint8_t v_nestedRhs_3538_; 
v_nestedRhs_3538_ = lean_ctor_get_uint8(v_format_3536_, 1);
if (v_nestedRhs_3538_ == 0)
{
return v_a_3537_;
}
else
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_Fmt_TaggedDoc_nested(v_a_3537_);
return v___x_3539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed(lean_object* v_format_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(v_format_3540_, v_a_3541_);
lean_dec_ref(v_format_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(lean_object* v_format_3543_){
_start:
{
uint8_t v_allowFlattening_3544_; 
v_allowFlattening_3544_ = lean_ctor_get_uint8(v_format_3543_, 0);
if (v_allowFlattening_3544_ == 0)
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_Fmt_TaggedDoc_hardNl;
return v___x_3545_;
}
else
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Fmt_TaggedDoc_nl;
return v___x_3546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep___boxed(lean_object* v_format_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3547_);
lean_dec_ref(v_format_3547_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(lean_object* v_rhs_3549_, lean_object* v_format_3550_, lean_object* v_lhs_3551_){
_start:
{
uint8_t v_allowFlattening_3552_; 
v_allowFlattening_3552_ = lean_ctor_get_uint8(v_format_3550_, 0);
if (v_allowFlattening_3552_ == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3553_, 0, v_lhs_3551_);
v___x_3554_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3550_);
v___x_3555_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3555_, 0, v_format_3550_);
v___x_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3554_);
lean_ctor_set(v___x_3556_, 1, v___x_3555_);
v___x_3557_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3553_, v___x_3556_);
v___x_3558_ = lean_box(0);
v___x_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_rhs_3549_);
v___x_3560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3558_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
lean_ctor_set(v___x_3560_, 2, v___x_3558_);
v___x_3561_ = lean_unsigned_to_nat(2u);
v___x_3562_ = lean_mk_empty_array_with_capacity(v___x_3561_);
v___x_3563_ = lean_array_push(v___x_3562_, v___x_3557_);
v___x_3564_ = lean_array_push(v___x_3563_, v___x_3560_);
v___x_3565_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3564_);
lean_dec_ref(v___x_3564_);
return v___x_3565_;
}
else
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3566_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3550_);
v___x_3567_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3567_, 0, v_format_3550_);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_3551_, v___x_3568_, v_rhs_3549_, v_allowFlattening_3552_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object* v_lhs_3570_, lean_object* v_keywordTk_3571_, lean_object* v_rhs_3572_, lean_object* v_format_3573_){
_start:
{
lean_object* v___y_3575_; uint8_t v___x_3578_; 
v___x_3578_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keywordTk_3571_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v_trailingKeywordLhs_3583_; uint8_t v___x_3584_; 
v___x_3579_ = lean_unsigned_to_nat(2u);
v___x_3580_ = lean_mk_empty_array_with_capacity(v___x_3579_);
v___x_3581_ = lean_array_push(v___x_3580_, v_lhs_3570_);
v___x_3582_ = lean_array_push(v___x_3581_, v_keywordTk_3571_);
v_trailingKeywordLhs_3583_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3582_);
lean_dec_ref(v___x_3582_);
v___x_3584_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_3572_);
if (v___x_3584_ == 0)
{
uint8_t v_nestedRhs_3585_; 
v_nestedRhs_3585_ = lean_ctor_get_uint8(v_format_3573_, 1);
if (v_nestedRhs_3585_ == 0)
{
v___y_3575_ = v_trailingKeywordLhs_3583_;
goto v___jp_3574_;
}
else
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Lean_Fmt_TaggedDoc_hardNested(v_trailingKeywordLhs_3583_);
v___y_3575_ = v___x_3586_;
goto v___jp_3574_;
}
}
else
{
v___y_3575_ = v_trailingKeywordLhs_3583_;
goto v___jp_3574_;
}
}
else
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec_ref(v_keywordTk_3571_);
v___x_3587_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3572_, v_format_3573_, v_lhs_3570_);
v___x_3588_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3587_);
return v___x_3588_;
}
v___jp_3574_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3572_, v_format_3573_, v___y_3575_);
v___x_3577_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3576_);
return v___x_3577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0(lean_object* v___y_3589_){
_start:
{
lean_inc_ref(v___y_3589_);
return v___y_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0___boxed(lean_object* v___y_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0(v___y_3590_);
lean_dec_ref(v___y_3590_);
return v_res_3591_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1(void){
_start:
{
lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___f_3593_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0));
v___x_3594_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v___f_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(lean_object* v_terms_3596_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3597_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3598_ = lean_box(0);
v___x_3599_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v_terms_3596_);
v___x_3600_ = lean_array_pop(v_terms_3596_);
v___x_3601_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_3599_, v___x_3600_);
v___x_3602_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3601_);
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3598_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
lean_ctor_set(v___x_3604_, 2, v___x_3598_);
v___x_3605_ = lean_array_get_size(v_terms_3596_);
v___x_3606_ = lean_unsigned_to_nat(1u);
v___x_3607_ = lean_nat_sub(v___x_3605_, v___x_3606_);
v___x_3608_ = lean_array_get(v___x_3597_, v_terms_3596_, v___x_3607_);
lean_dec(v___x_3607_);
lean_dec_ref(v_terms_3596_);
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
v___x_3610_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1);
v___x_3611_ = l_Lean_Fmt_TaggedDoc_Component_withSepBefore(v___x_3609_, v___x_3610_);
v___x_3612_ = lean_unsigned_to_nat(2u);
v___x_3613_ = lean_mk_empty_array_with_capacity(v___x_3612_);
v___x_3614_ = lean_array_push(v___x_3613_, v___x_3604_);
v___x_3615_ = lean_array_push(v___x_3614_, v___x_3611_);
v___x_3616_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3615_);
lean_dec_ref(v___x_3615_);
return v___x_3616_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0(void){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3618_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(lean_object* v_app_3619_, lean_object* v_fillableTerms_3620_, lean_object* v_terms_3621_, lean_object* v_eligibleKinds_3622_){
_start:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; uint8_t v_allowFill_3629_; 
v___x_3623_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3624_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3625_ = lean_array_get_size(v_fillableTerms_3620_);
v___x_3626_ = lean_unsigned_to_nat(1u);
v___x_3627_ = lean_nat_sub(v___x_3625_, v___x_3626_);
v___x_3628_ = lean_array_get_borrowed(v___x_3624_, v_fillableTerms_3620_, v___x_3627_);
lean_dec(v___x_3627_);
v_allowFill_3629_ = lean_ctor_get_uint8(v___x_3628_, sizeof(void*)*1);
if (v_allowFill_3629_ == 0)
{
lean_object* v___x_3630_; 
lean_dec_ref(v_terms_3621_);
lean_dec_ref(v_app_3619_);
v___x_3630_ = lean_box(0);
return v___x_3630_;
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3631_ = lean_array_get_size(v_terms_3621_);
v___x_3632_ = lean_nat_sub(v___x_3631_, v___x_3626_);
v___x_3633_ = lean_array_get_borrowed(v___x_3623_, v_terms_3621_, v___x_3632_);
lean_inc(v___x_3633_);
v___x_3634_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v___x_3633_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v___x_3635_; 
lean_dec(v___x_3632_);
lean_dec_ref(v_terms_3621_);
lean_dec_ref(v_app_3619_);
v___x_3635_ = lean_box(0);
return v___x_3635_;
}
else
{
lean_object* v_val_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3657_; 
v_val_3636_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3638_ = v___x_3634_;
v_isShared_3639_ = v_isSharedCheck_3657_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_val_3636_);
lean_dec(v___x_3634_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3657_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
uint8_t v___x_3640_; uint8_t v___x_3641_; lean_object* v___y_3643_; 
v___x_3640_ = lean_unbox(v_val_3636_);
lean_dec(v_val_3636_);
v___x_3641_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_3622_, v___x_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3652_; 
lean_del_object(v___x_3638_);
lean_dec(v___x_3632_);
lean_dec_ref(v_terms_3621_);
lean_dec_ref(v_app_3619_);
v___x_3652_ = lean_box(0);
return v___x_3652_;
}
else
{
lean_object* v___x_3653_; 
lean_inc(v___x_3633_);
v___x_3653_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v___x_3633_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__4, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__4);
v___x_3655_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_3654_);
v___y_3643_ = v___x_3655_;
goto v___jp_3642_;
}
else
{
lean_object* v_val_3656_; 
v_val_3656_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_val_3656_);
lean_dec_ref_known(v___x_3653_, 1);
v___y_3643_ = v_val_3656_;
goto v___jp_3642_;
}
}
v___jp_3642_:
{
lean_object* v_stickyVariant_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v_stickyVariant_3644_ = lean_ctor_get(v___y_3643_, 0);
lean_inc_ref(v_stickyVariant_3644_);
v___x_3645_ = lean_array_set(v_terms_3621_, v___x_3632_, v_stickyVariant_3644_);
lean_dec(v___x_3632_);
v___x_3646_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v___x_3645_);
v___x_3647_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_3643_, v___x_3641_);
lean_dec_ref(v___y_3643_);
v___x_3648_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_app_3619_, v___x_3646_, v___x_3647_);
lean_dec(v___x_3647_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v___x_3648_);
v___x_3650_ = v___x_3638_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___boxed(lean_object* v_app_3658_, lean_object* v_fillableTerms_3659_, lean_object* v_terms_3660_, lean_object* v_eligibleKinds_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3658_, v_fillableTerms_3659_, v_terms_3660_, v_eligibleKinds_3661_);
lean_dec_ref(v_eligibleKinds_3661_);
lean_dec_ref(v_fillableTerms_3659_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(lean_object* v_format_3663_, lean_object* v_app_3664_, lean_object* v_terms_3665_){
_start:
{
uint8_t v_sparse_3666_; 
v_sparse_3666_ = lean_ctor_get_uint8(v_format_3663_, 1);
if (v_sparse_3666_ == 0)
{
uint8_t v_respectPseudoAlignment_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; uint8_t v___x_3670_; 
v_respectPseudoAlignment_3667_ = lean_ctor_get_uint8(v_format_3663_, 3);
v___x_3668_ = lean_array_get_size(v_terms_3665_);
v___x_3669_ = lean_unsigned_to_nat(2u);
v___x_3670_ = lean_nat_dec_eq(v___x_3668_, v___x_3669_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; 
lean_dec_ref(v_terms_3665_);
lean_dec_ref(v_app_3664_);
v___x_3671_ = lean_box(0);
return v___x_3671_;
}
else
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v___x_3672_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_nat_sub(v___x_3668_, v___x_3673_);
v___x_3675_ = lean_array_get_borrowed(v___x_3672_, v_terms_3665_, v___x_3674_);
lean_dec(v___x_3674_);
lean_inc(v___x_3675_);
v___x_3676_ = l_Lean_Fmt_Layouts_permitDenseLayout(v___x_3675_, v_respectPseudoAlignment_3667_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; 
lean_dec_ref(v_terms_3665_);
lean_dec_ref(v_app_3664_);
v___x_3677_ = lean_box(0);
return v___x_3677_;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3678_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v_terms_3665_);
v___x_3679_ = lean_mk_empty_array_with_capacity(v___x_3669_);
v___x_3680_ = lean_array_push(v___x_3679_, v___x_3678_);
v___x_3681_ = lean_array_push(v___x_3680_, v_app_3664_);
v___x_3682_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3681_);
v___x_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
return v___x_3683_;
}
}
}
else
{
lean_object* v___x_3684_; 
lean_dec_ref(v_terms_3665_);
lean_dec_ref(v_app_3664_);
v___x_3684_ = lean_box(0);
return v___x_3684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f___boxed(lean_object* v_format_3685_, lean_object* v_app_3686_, lean_object* v_terms_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3685_, v_app_3686_, v_terms_3687_);
lean_dec_ref(v_format_3685_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(lean_object* v_upperBound_3689_, lean_object* v_a_3690_, lean_object* v_b_3691_){
_start:
{
uint8_t v___x_3692_; 
v___x_3692_ = lean_nat_dec_lt(v_a_3690_, v_upperBound_3689_);
if (v___x_3692_ == 0)
{
lean_dec(v_a_3690_);
lean_inc_ref(v_b_3691_);
return v_b_3691_;
}
else
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = lean_unsigned_to_nat(1u);
v___x_3694_ = lean_nat_add(v_a_3690_, v___x_3693_);
lean_dec(v_a_3690_);
v_a_3690_ = v___x_3694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___boxed(lean_object* v_upperBound_3696_, lean_object* v_a_3697_, lean_object* v_b_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3696_, v_a_3697_, v_b_3698_);
lean_dec_ref(v_b_3698_);
lean_dec(v_upperBound_3696_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(lean_object* v_as_3700_, size_t v_i_3701_, size_t v_stop_3702_, lean_object* v_b_3703_){
_start:
{
lean_object* v___y_3705_; uint8_t v___x_3709_; 
v___x_3709_ = lean_usize_dec_eq(v_i_3701_, v_stop_3702_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; lean_object* v_v_3711_; uint8_t v___x_3712_; 
v___x_3710_ = lean_array_uget_borrowed(v_as_3700_, v_i_3701_);
v_v_3711_ = lean_ctor_get(v___x_3710_, 0);
v___x_3712_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_3711_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; 
lean_inc(v___x_3710_);
v___x_3713_ = lean_array_push(v_b_3703_, v___x_3710_);
v___y_3705_ = v___x_3713_;
goto v___jp_3704_;
}
else
{
v___y_3705_ = v_b_3703_;
goto v___jp_3704_;
}
}
else
{
return v_b_3703_;
}
v___jp_3704_:
{
size_t v___x_3706_; size_t v___x_3707_; 
v___x_3706_ = ((size_t)1ULL);
v___x_3707_ = lean_usize_add(v_i_3701_, v___x_3706_);
v_i_3701_ = v___x_3707_;
v_b_3703_ = v___y_3705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2___boxed(lean_object* v_as_3714_, lean_object* v_i_3715_, lean_object* v_stop_3716_, lean_object* v_b_3717_){
_start:
{
size_t v_i_boxed_3718_; size_t v_stop_boxed_3719_; lean_object* v_res_3720_; 
v_i_boxed_3718_ = lean_unbox_usize(v_i_3715_);
lean_dec(v_i_3715_);
v_stop_boxed_3719_ = lean_unbox_usize(v_stop_3716_);
lean_dec(v_stop_3716_);
v_res_3720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_as_3714_, v_i_boxed_3718_, v_stop_boxed_3719_, v_b_3717_);
lean_dec_ref(v_as_3714_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(size_t v_sz_3721_, size_t v_i_3722_, lean_object* v_bs_3723_){
_start:
{
uint8_t v___x_3724_; 
v___x_3724_ = lean_usize_dec_lt(v_i_3722_, v_sz_3721_);
if (v___x_3724_ == 0)
{
return v_bs_3723_;
}
else
{
lean_object* v_v_3725_; lean_object* v_v_3726_; lean_object* v___x_3727_; lean_object* v_bs_x27_3728_; size_t v___x_3729_; size_t v___x_3730_; lean_object* v___x_3731_; 
v_v_3725_ = lean_array_uget_borrowed(v_bs_3723_, v_i_3722_);
v_v_3726_ = lean_ctor_get(v_v_3725_, 0);
lean_inc(v_v_3726_);
v___x_3727_ = lean_unsigned_to_nat(0u);
v_bs_x27_3728_ = lean_array_uset(v_bs_3723_, v_i_3722_, v___x_3727_);
v___x_3729_ = ((size_t)1ULL);
v___x_3730_ = lean_usize_add(v_i_3722_, v___x_3729_);
v___x_3731_ = lean_array_uset(v_bs_x27_3728_, v_i_3722_, v_v_3726_);
v_i_3722_ = v___x_3730_;
v_bs_3723_ = v___x_3731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0___boxed(lean_object* v_sz_3733_, lean_object* v_i_3734_, lean_object* v_bs_3735_){
_start:
{
size_t v_sz_boxed_3736_; size_t v_i_boxed_3737_; lean_object* v_res_3738_; 
v_sz_boxed_3736_ = lean_unbox_usize(v_sz_3733_);
lean_dec(v_sz_3733_);
v_i_boxed_3737_ = lean_unbox_usize(v_i_3734_);
lean_dec(v_i_3734_);
v_res_3738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_boxed_3736_, v_i_boxed_3737_, v_bs_3735_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object* v_terms_3741_, lean_object* v_format_3742_){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___y_3746_; uint8_t v___y_3747_; lean_object* v_app_3748_; uint8_t v___y_3761_; lean_object* v___y_3762_; lean_object* v_fillableTerms_3763_; uint8_t v___y_3780_; lean_object* v___y_3781_; lean_object* v_fillableTerms_3782_; lean_object* v___y_3788_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v___x_3743_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3744_ = lean_unsigned_to_nat(0u);
v___x_3814_ = lean_array_get_size(v_terms_3741_);
v___x_3815_ = ((lean_object*)(l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0));
v___x_3816_ = lean_nat_dec_lt(v___x_3744_, v___x_3814_);
if (v___x_3816_ == 0)
{
v___y_3788_ = v___x_3815_;
goto v___jp_3787_;
}
else
{
size_t v___x_3817_; size_t v___x_3818_; lean_object* v___x_3819_; 
v___x_3817_ = ((size_t)0ULL);
v___x_3818_ = lean_usize_of_nat(v___x_3814_);
v___x_3819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3741_, v___x_3817_, v___x_3818_, v___x_3815_);
v___y_3788_ = v___x_3819_;
goto v___jp_3787_;
}
v___jp_3745_:
{
lean_object* v___x_3749_; lean_object* v_v_3750_; lean_object* v_doc_3751_; lean_object* v___x_3752_; lean_object* v_doc_3753_; uint8_t v___x_3754_; 
v___x_3749_ = lean_array_get(v___x_3743_, v___y_3746_, v___x_3744_);
lean_dec_ref(v___y_3746_);
v_v_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_v_3750_);
lean_dec(v___x_3749_);
v_doc_3751_ = lean_ctor_get(v_v_3750_, 0);
v___x_3752_ = l_Lean_Fmt_TaggedDoc_nested(v_app_3748_);
v_doc_3753_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3752_);
lean_inc(v_doc_3751_);
v___x_3754_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_3751_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(v_v_3750_);
if (lean_obj_tag(v___x_3755_) == 1)
{
lean_object* v_val_3756_; uint8_t v___x_3757_; lean_object* v_doc_3758_; 
v_val_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_val_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v___x_3757_ = lean_unbox(v_val_3756_);
lean_dec(v_val_3756_);
v_doc_3758_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_3753_, v___x_3757_);
return v_doc_3758_;
}
else
{
lean_dec(v___x_3755_);
return v_doc_3753_;
}
}
else
{
lean_object* v_doc_3759_; 
lean_dec(v_v_3750_);
v_doc_3759_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_3753_, v___y_3747_);
return v_doc_3759_;
}
}
v___jp_3760_:
{
lean_object* v_app_3764_; size_t v_sz_3765_; size_t v___x_3766_; lean_object* v_terms_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
lean_inc_ref_n(v_fillableTerms_3763_, 2);
v_app_3764_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(v_fillableTerms_3763_);
v_sz_3765_ = lean_array_size(v_fillableTerms_3763_);
v___x_3766_ = ((size_t)0ULL);
v_terms_3767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_3765_, v___x_3766_, v_fillableTerms_3763_);
v___x_3768_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
lean_inc_ref(v_terms_3767_);
lean_inc_ref(v_app_3764_);
v___x_3769_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3764_, v_fillableTerms_3763_, v_terms_3767_, v___x_3768_);
if (lean_obj_tag(v___x_3769_) == 1)
{
lean_object* v_val_3770_; 
lean_dec_ref(v_terms_3767_);
lean_dec_ref(v_app_3764_);
lean_dec(v___y_3762_);
v_val_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_val_3770_);
lean_dec_ref_known(v___x_3769_, 1);
v___y_3746_ = v_fillableTerms_3763_;
v___y_3747_ = v___y_3761_;
v_app_3748_ = v_val_3770_;
goto v___jp_3745_;
}
else
{
lean_object* v___x_3771_; 
lean_dec(v___x_3769_);
lean_inc_ref(v_terms_3767_);
lean_inc_ref(v_app_3764_);
v___x_3771_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3742_, v_app_3764_, v_terms_3767_);
if (lean_obj_tag(v___x_3771_) == 1)
{
lean_object* v_val_3772_; 
lean_dec_ref(v_terms_3767_);
lean_dec_ref(v_app_3764_);
lean_dec(v___y_3762_);
v_val_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_val_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___y_3746_ = v_fillableTerms_3763_;
v___y_3747_ = v___y_3761_;
v_app_3748_ = v_val_3772_;
goto v___jp_3745_;
}
else
{
uint8_t v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_dec(v___x_3771_);
v___x_3773_ = 2;
v___x_3774_ = lean_mk_empty_array_with_capacity(v___y_3762_);
lean_dec(v___y_3762_);
v___x_3775_ = lean_box(v___x_3773_);
v___x_3776_ = lean_array_push(v___x_3774_, v___x_3775_);
lean_inc_ref(v_app_3764_);
v___x_3777_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3764_, v_fillableTerms_3763_, v_terms_3767_, v___x_3776_);
lean_dec_ref(v___x_3776_);
if (lean_obj_tag(v___x_3777_) == 1)
{
lean_object* v_val_3778_; 
lean_dec_ref(v_app_3764_);
v_val_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_val_3778_);
lean_dec_ref_known(v___x_3777_, 1);
v___y_3746_ = v_fillableTerms_3763_;
v___y_3747_ = v___y_3761_;
v_app_3748_ = v_val_3778_;
goto v___jp_3745_;
}
else
{
lean_dec(v___x_3777_);
v___y_3746_ = v_fillableTerms_3763_;
v___y_3747_ = v___y_3761_;
v_app_3748_ = v_app_3764_;
goto v___jp_3745_;
}
}
}
}
v___jp_3779_:
{
uint8_t v_parenthesize_3783_; 
v_parenthesize_3783_ = lean_ctor_get_uint8(v_format_3742_, 2);
if (v_parenthesize_3783_ == 0)
{
v___y_3761_ = v___y_3780_;
v___y_3762_ = v___y_3781_;
v_fillableTerms_3763_ = v_fillableTerms_3782_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3784_ = lean_array_get_size(v_fillableTerms_3782_);
v___x_3785_ = lean_nat_sub(v___x_3784_, v___y_3781_);
lean_inc(v___y_3781_);
v___x_3786_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v___x_3785_, v___y_3781_, v_fillableTerms_3782_);
lean_dec_ref(v_fillableTerms_3782_);
lean_dec(v___x_3785_);
v___y_3761_ = v___y_3780_;
v___y_3762_ = v___y_3781_;
v_fillableTerms_3763_ = v___x_3786_;
goto v___jp_3760_;
}
}
v___jp_3787_:
{
lean_object* v___x_3789_; uint8_t v___x_3790_; 
v___x_3789_ = lean_array_get_size(v___y_3788_);
v___x_3790_ = lean_nat_dec_eq(v___x_3789_, v___x_3744_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3791_ = lean_unsigned_to_nat(1u);
v___x_3792_ = lean_nat_dec_eq(v___x_3789_, v___x_3791_);
if (v___x_3792_ == 0)
{
uint8_t v___x_3793_; uint8_t v___x_3794_; 
v___x_3793_ = 1;
v___x_3794_ = lean_nat_dec_lt(v___x_3791_, v___x_3789_);
if (v___x_3794_ == 0)
{
v___y_3780_ = v___x_3793_;
v___y_3781_ = v___x_3791_;
v_fillableTerms_3782_ = v___y_3788_;
goto v___jp_3779_;
}
else
{
uint8_t v_hardNestedFirstTerm_3795_; 
v_hardNestedFirstTerm_3795_ = lean_ctor_get_uint8(v_format_3742_, 0);
if (v_hardNestedFirstTerm_3795_ == 0)
{
v___y_3780_ = v___x_3793_;
v___y_3781_ = v___x_3791_;
v_fillableTerms_3782_ = v___y_3788_;
goto v___jp_3779_;
}
else
{
uint8_t v___x_3796_; 
v___x_3796_ = lean_nat_dec_lt(v___x_3744_, v___x_3789_);
if (v___x_3796_ == 0)
{
v___y_3780_ = v___x_3793_;
v___y_3781_ = v___x_3791_;
v_fillableTerms_3782_ = v___y_3788_;
goto v___jp_3779_;
}
else
{
lean_object* v_v_3797_; lean_object* v_v_3798_; uint8_t v_allowFill_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3810_; 
v_v_3797_ = lean_array_fget(v___y_3788_, v___x_3744_);
v_v_3798_ = lean_ctor_get(v_v_3797_, 0);
v_allowFill_3799_ = lean_ctor_get_uint8(v_v_3797_, sizeof(void*)*1);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_v_3797_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3801_ = v_v_3797_;
v_isShared_3802_ = v_isSharedCheck_3810_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_v_3798_);
lean_dec(v_v_3797_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3810_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v_xs_x27_3804_; lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3803_ = lean_box(0);
v_xs_x27_3804_ = lean_array_fset(v___y_3788_, v___x_3744_, v___x_3803_);
v___x_3805_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3798_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3805_);
v___x_3807_ = v___x_3801_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3805_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, sizeof(void*)*1, v_allowFill_3799_);
v___x_3807_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_array_fset(v_xs_x27_3804_, v___x_3744_, v___x_3807_);
v___y_3780_ = v___x_3793_;
v___y_3781_ = v___x_3791_;
v_fillableTerms_3782_ = v___x_3808_;
goto v___jp_3779_;
}
}
}
}
}
}
else
{
lean_object* v___x_3811_; lean_object* v_v_3812_; 
v___x_3811_ = lean_array_get(v___x_3743_, v___y_3788_, v___x_3744_);
lean_dec_ref(v___y_3788_);
v_v_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_v_3812_);
lean_dec(v___x_3811_);
return v_v_3812_;
}
}
else
{
lean_object* v___x_3813_; 
lean_dec_ref(v___y_3788_);
v___x_3813_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___boxed(lean_object* v_terms_3820_, lean_object* v_format_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v_terms_3820_, v_format_3821_);
lean_dec_ref(v_format_3821_);
lean_dec_ref(v_terms_3820_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(lean_object* v_upperBound_3823_, lean_object* v_inst_3824_, lean_object* v_R_3825_, lean_object* v_a_3826_, lean_object* v_b_3827_, lean_object* v_c_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3823_, v_a_3826_, v_b_3827_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___boxed(lean_object* v_upperBound_3830_, lean_object* v_inst_3831_, lean_object* v_R_3832_, lean_object* v_a_3833_, lean_object* v_b_3834_, lean_object* v_c_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(v_upperBound_3830_, v_inst_3831_, v_R_3832_, v_a_3833_, v_b_3834_, v_c_3835_);
lean_dec_ref(v_b_3834_);
lean_dec(v_upperBound_3830_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(size_t v_sz_3837_, size_t v_i_3838_, lean_object* v_bs_3839_){
_start:
{
uint8_t v___x_3840_; 
v___x_3840_ = lean_usize_dec_lt(v_i_3838_, v_sz_3837_);
if (v___x_3840_ == 0)
{
return v_bs_3839_;
}
else
{
lean_object* v_v_3841_; lean_object* v___x_3842_; lean_object* v_bs_x27_3843_; lean_object* v___x_3844_; size_t v___x_3845_; size_t v___x_3846_; lean_object* v___x_3847_; 
v_v_3841_ = lean_array_uget(v_bs_3839_, v_i_3838_);
v___x_3842_ = lean_unsigned_to_nat(0u);
v_bs_x27_3843_ = lean_array_uset(v_bs_3839_, v_i_3838_, v___x_3842_);
v___x_3844_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3844_, 0, v_v_3841_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*1, v___x_3840_);
v___x_3845_ = ((size_t)1ULL);
v___x_3846_ = lean_usize_add(v_i_3838_, v___x_3845_);
v___x_3847_ = lean_array_uset(v_bs_x27_3843_, v_i_3838_, v___x_3844_);
v_i_3838_ = v___x_3846_;
v_bs_3839_ = v___x_3847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0___boxed(lean_object* v_sz_3849_, lean_object* v_i_3850_, lean_object* v_bs_3851_){
_start:
{
size_t v_sz_boxed_3852_; size_t v_i_boxed_3853_; lean_object* v_res_3854_; 
v_sz_boxed_3852_ = lean_unbox_usize(v_sz_3849_);
lean_dec(v_sz_3849_);
v_i_boxed_3853_ = lean_unbox_usize(v_i_3850_);
lean_dec(v_i_3850_);
v_res_3854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_boxed_3852_, v_i_boxed_3853_, v_bs_3851_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application(lean_object* v_terms_3855_, lean_object* v_format_3856_){
_start:
{
size_t v_sz_3857_; size_t v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_sz_3857_ = lean_array_size(v_terms_3855_);
v___x_3858_ = ((size_t)0ULL);
v___x_3859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_3857_, v___x_3858_, v_terms_3855_);
v___x_3860_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v___x_3859_, v_format_3856_);
lean_dec_ref(v___x_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application___boxed(lean_object* v_terms_3861_, lean_object* v_format_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Fmt_Layouts_application(v_terms_3861_, v_format_3862_);
lean_dec_ref(v_format_3862_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(lean_object* v_f_3864_){
_start:
{
uint8_t v_hardNestedFirstTerm_3865_; uint8_t v_sparse_3866_; uint8_t v_parenthesize_3867_; uint8_t v_respectPseudoAlignment_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
v_hardNestedFirstTerm_3865_ = lean_ctor_get_uint8(v_f_3864_, 0);
v_sparse_3866_ = lean_ctor_get_uint8(v_f_3864_, 1);
v_parenthesize_3867_ = lean_ctor_get_uint8(v_f_3864_, 2);
v_respectPseudoAlignment_3868_ = lean_ctor_get_uint8(v_f_3864_, 3);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_f_3864_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v_f_3864_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_dec(v_f_3864_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3874_, 0, v_hardNestedFirstTerm_3865_);
lean_ctor_set_uint8(v_reuseFailAlloc_3874_, 1, v_sparse_3866_);
lean_ctor_set_uint8(v_reuseFailAlloc_3874_, 2, v_parenthesize_3867_);
lean_ctor_set_uint8(v_reuseFailAlloc_3874_, 3, v_respectPseudoAlignment_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object* v_terms_3876_, lean_object* v_format_3877_){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(v_format_3877_);
v___x_3879_ = l_Lean_Fmt_Layouts_application(v_terms_3876_, v___x_3878_);
lean_dec_ref(v___x_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl(lean_object* v_x_3880_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_obj_tag_nat(v_x_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl___boxed(lean_object* v_x_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl(v_x_3882_);
lean_dec_ref(v_x_3882_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(lean_object* v_t_3884_, lean_object* v_k_3885_){
_start:
{
lean_object* v_doc_3886_; lean_object* v___x_3887_; 
v_doc_3886_ = lean_ctor_get(v_t_3884_, 0);
lean_inc_ref(v_doc_3886_);
lean_dec_ref(v_t_3884_);
v___x_3887_ = lean_apply_1(v_k_3885_, v_doc_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(lean_object* v_motive_3888_, lean_object* v_ctorIdx_3889_, lean_object* v_t_3890_, lean_object* v_h_3891_, lean_object* v_k_3892_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3890_, v_k_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___boxed(lean_object* v_motive_3894_, lean_object* v_ctorIdx_3895_, lean_object* v_t_3896_, lean_object* v_h_3897_, lean_object* v_k_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(v_motive_3894_, v_ctorIdx_3895_, v_t_3896_, v_h_3897_, v_k_3898_);
lean_dec(v_ctorIdx_3895_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim___redArg(lean_object* v_t_3900_, lean_object* v_sep_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3900_, v_sep_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim(lean_object* v_motive_3903_, lean_object* v_t_3904_, lean_object* v_h_3905_, lean_object* v_sep_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3904_, v_sep_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim___redArg(lean_object* v_t_3908_, lean_object* v_elems_3909_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3908_, v_elems_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim(lean_object* v_motive_3911_, lean_object* v_t_3912_, lean_object* v_h_3913_, lean_object* v_elems_3914_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3912_, v_elems_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(size_t v_sz_3916_, size_t v_i_3917_, lean_object* v_bs_3918_){
_start:
{
uint8_t v___x_3919_; 
v___x_3919_ = lean_usize_dec_lt(v_i_3917_, v_sz_3916_);
if (v___x_3919_ == 0)
{
return v_bs_3918_;
}
else
{
lean_object* v_v_3920_; lean_object* v___x_3921_; lean_object* v_bs_x27_3922_; lean_object* v___y_3924_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; uint8_t v___x_3932_; 
v_v_3920_ = lean_array_uget(v_bs_3918_, v_i_3917_);
v___x_3921_ = lean_unsigned_to_nat(0u);
v_bs_x27_3922_ = lean_array_uset(v_bs_3918_, v_i_3917_, v___x_3921_);
v___x_3929_ = lean_usize_to_nat(v_i_3917_);
v___x_3930_ = lean_unsigned_to_nat(2u);
v___x_3931_ = lean_nat_mod(v___x_3929_, v___x_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_nat_dec_eq(v___x_3931_, v___x_3921_);
lean_dec(v___x_3931_);
if (v___x_3932_ == 0)
{
lean_object* v___x_3933_; 
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v_v_3920_);
v___y_3924_ = v___x_3933_;
goto v___jp_3923_;
}
else
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3934_ = lean_unsigned_to_nat(1u);
v___x_3935_ = lean_mk_empty_array_with_capacity(v___x_3934_);
v___x_3936_ = lean_array_push(v___x_3935_, v_v_3920_);
v___x_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
v___y_3924_ = v___x_3937_;
goto v___jp_3923_;
}
v___jp_3923_:
{
size_t v___x_3925_; size_t v___x_3926_; lean_object* v___x_3927_; 
v___x_3925_ = ((size_t)1ULL);
v___x_3926_ = lean_usize_add(v_i_3917_, v___x_3925_);
v___x_3927_ = lean_array_uset(v_bs_x27_3922_, v_i_3917_, v___y_3924_);
v_i_3917_ = v___x_3926_;
v_bs_3918_ = v___x_3927_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg___boxed(lean_object* v_sz_3938_, lean_object* v_i_3939_, lean_object* v_bs_3940_){
_start:
{
size_t v_sz_boxed_3941_; size_t v_i_boxed_3942_; lean_object* v_res_3943_; 
v_sz_boxed_3941_ = lean_unbox_usize(v_sz_3938_);
lean_dec(v_sz_3938_);
v_i_boxed_3942_ = lean_unbox_usize(v_i_3939_);
lean_dec(v_i_3939_);
v_res_3943_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_boxed_3941_, v_i_boxed_3942_, v_bs_3940_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object* v_elems_3944_){
_start:
{
size_t v_sz_3945_; size_t v___x_3946_; lean_object* v___x_3947_; 
v_sz_3945_ = lean_array_size(v_elems_3944_);
v___x_3946_ = ((size_t)0ULL);
v___x_3947_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3945_, v___x_3946_, v_elems_3944_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(lean_object* v_s_3948_, lean_object* v_elems_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_elems_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___boxed(lean_object* v_s_3951_, lean_object* v_elems_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(v_s_3951_, v_elems_3952_);
lean_dec_ref(v_s_3951_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(lean_object* v_as_3954_, size_t v_sz_3955_, size_t v_i_3956_, lean_object* v_bs_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3955_, v_i_3956_, v_bs_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___boxed(lean_object* v_as_3959_, lean_object* v_sz_3960_, lean_object* v_i_3961_, lean_object* v_bs_3962_){
_start:
{
size_t v_sz_boxed_3963_; size_t v_i_boxed_3964_; lean_object* v_res_3965_; 
v_sz_boxed_3963_ = lean_unbox_usize(v_sz_3960_);
lean_dec(v_sz_3960_);
v_i_boxed_3964_ = lean_unbox_usize(v_i_3961_);
lean_dec(v_i_3961_);
v_res_3965_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(v_as_3959_, v_sz_boxed_3963_, v_i_boxed_3964_, v_bs_3962_);
lean_dec_ref(v_as_3959_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(size_t v_sz_3968_, size_t v_i_3969_, lean_object* v_bs_3970_){
_start:
{
uint8_t v___x_3971_; 
v___x_3971_ = lean_usize_dec_lt(v_i_3969_, v_sz_3968_);
if (v___x_3971_ == 0)
{
return v_bs_3970_;
}
else
{
lean_object* v_v_3972_; lean_object* v___x_3973_; lean_object* v_bs_x27_3974_; lean_object* v___y_3976_; 
v_v_3972_ = lean_array_uget(v_bs_3970_, v_i_3969_);
v___x_3973_ = lean_unsigned_to_nat(0u);
v_bs_x27_3974_ = lean_array_uset(v_bs_3970_, v_i_3969_, v___x_3973_);
if (lean_obj_tag(v_v_3972_) == 0)
{
v___y_3976_ = v_v_3972_;
goto v___jp_3975_;
}
else
{
lean_object* v_docs_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3995_; 
v_docs_3981_ = lean_ctor_get(v_v_3972_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_v_3972_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3983_ = v_v_3972_;
v_isShared_3984_ = v_isSharedCheck_3995_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_docs_3981_);
lean_dec(v_v_3972_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3995_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v___x_3985_ = lean_array_get_size(v_docs_3981_);
v___x_3986_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_3987_ = lean_nat_dec_lt(v___x_3973_, v___x_3985_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; 
lean_del_object(v___x_3983_);
lean_dec_ref(v_docs_3981_);
v___x_3988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_3976_ = v___x_3988_;
goto v___jp_3975_;
}
else
{
size_t v___x_3989_; size_t v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3989_ = ((size_t)0ULL);
v___x_3990_ = lean_usize_of_nat(v___x_3985_);
v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_docs_3981_, v___x_3989_, v___x_3990_, v___x_3986_);
lean_dec_ref(v_docs_3981_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v___x_3991_);
v___x_3993_ = v___x_3983_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
v___y_3976_ = v___x_3993_;
goto v___jp_3975_;
}
}
}
}
v___jp_3975_:
{
size_t v___x_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
v___x_3977_ = ((size_t)1ULL);
v___x_3978_ = lean_usize_add(v_i_3969_, v___x_3977_);
v___x_3979_ = lean_array_uset(v_bs_x27_3974_, v_i_3969_, v___y_3976_);
v_i_3969_ = v___x_3978_;
v_bs_3970_ = v___x_3979_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___boxed(lean_object* v_sz_3996_, lean_object* v_i_3997_, lean_object* v_bs_3998_){
_start:
{
size_t v_sz_boxed_3999_; size_t v_i_boxed_4000_; lean_object* v_res_4001_; 
v_sz_boxed_3999_ = lean_unbox_usize(v_sz_3996_);
lean_dec(v_sz_3996_);
v_i_boxed_4000_ = lean_unbox_usize(v_i_3997_);
lean_dec(v_i_3997_);
v_res_4001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_boxed_3999_, v_i_boxed_4000_, v_bs_3998_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(lean_object* v_as_4002_, lean_object* v_j_4003_){
_start:
{
lean_object* v___x_4008_; uint8_t v___x_4009_; 
v___x_4008_ = lean_array_get_size(v_as_4002_);
v___x_4009_ = lean_nat_dec_lt(v_j_4003_, v___x_4008_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; 
lean_dec(v_j_4003_);
v___x_4010_ = lean_box(0);
return v___x_4010_;
}
else
{
lean_object* v___x_4011_; 
v___x_4011_ = lean_array_fget(v_as_4002_, v_j_4003_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_dec_ref_known(v___x_4011_, 1);
goto v___jp_4004_;
}
else
{
lean_object* v_docs_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4022_; 
v_docs_4012_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4014_ = v___x_4011_;
v_isShared_4015_ = v_isSharedCheck_4022_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_docs_4012_);
lean_dec(v___x_4011_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4022_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; 
v___x_4016_ = lean_array_get_size(v_docs_4012_);
lean_dec_ref(v_docs_4012_);
v___x_4017_ = lean_unsigned_to_nat(0u);
v___x_4018_ = lean_nat_dec_eq(v___x_4016_, v___x_4017_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4020_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v_j_4003_);
v___x_4020_ = v___x_4014_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_j_4003_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
else
{
lean_del_object(v___x_4014_);
goto v___jp_4004_;
}
}
}
}
v___jp_4004_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = lean_unsigned_to_nat(1u);
v___x_4006_ = lean_nat_add(v_j_4003_, v___x_4005_);
lean_dec(v_j_4003_);
v_j_4003_ = v___x_4006_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2___boxed(lean_object* v_as_4023_, lean_object* v_j_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_as_4023_, v_j_4024_);
lean_dec_ref(v_as_4023_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(size_t v_sz_4026_, size_t v_i_4027_, lean_object* v_bs_4028_){
_start:
{
uint8_t v___x_4029_; 
v___x_4029_ = lean_usize_dec_lt(v_i_4027_, v_sz_4026_);
if (v___x_4029_ == 0)
{
return v_bs_4028_;
}
else
{
lean_object* v_v_4030_; lean_object* v___x_4031_; lean_object* v_bs_x27_4032_; lean_object* v___y_4034_; 
v_v_4030_ = lean_array_uget(v_bs_4028_, v_i_4027_);
v___x_4031_ = lean_unsigned_to_nat(0u);
v_bs_x27_4032_ = lean_array_uset(v_bs_4028_, v_i_4027_, v___x_4031_);
if (lean_obj_tag(v_v_4030_) == 0)
{
lean_object* v_doc_4039_; 
v_doc_4039_ = lean_ctor_get(v_v_4030_, 0);
lean_inc_ref(v_doc_4039_);
lean_dec_ref_known(v_v_4030_, 1);
v___y_4034_ = v_doc_4039_;
goto v___jp_4033_;
}
else
{
lean_object* v_docs_4040_; lean_object* v___x_4041_; 
v_docs_4040_ = lean_ctor_get(v_v_4030_, 0);
lean_inc_ref(v_docs_4040_);
lean_dec_ref_known(v_v_4030_, 1);
v___x_4041_ = l_Lean_Fmt_Layouts_fill(v_docs_4040_);
lean_dec_ref(v_docs_4040_);
v___y_4034_ = v___x_4041_;
goto v___jp_4033_;
}
v___jp_4033_:
{
size_t v___x_4035_; size_t v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = ((size_t)1ULL);
v___x_4036_ = lean_usize_add(v_i_4027_, v___x_4035_);
v___x_4037_ = lean_array_uset(v_bs_x27_4032_, v_i_4027_, v___y_4034_);
v_i_4027_ = v___x_4036_;
v_bs_4028_ = v___x_4037_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0___boxed(lean_object* v_sz_4042_, lean_object* v_i_4043_, lean_object* v_bs_4044_){
_start:
{
size_t v_sz_boxed_4045_; size_t v_i_boxed_4046_; lean_object* v_res_4047_; 
v_sz_boxed_4045_ = lean_unbox_usize(v_sz_4042_);
lean_dec(v_sz_4042_);
v_i_boxed_4046_ = lean_unbox_usize(v_i_4043_);
lean_dec(v_i_4043_);
v_res_4047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_boxed_4045_, v_i_boxed_4046_, v_bs_4044_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object* v_lb_4049_, lean_object* v_terms_4050_, lean_object* v_rb_4051_){
_start:
{
lean_object* v_terms_4053_; size_t v_sz_4061_; size_t v___x_4062_; lean_object* v_terms_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v_sz_4061_ = lean_array_size(v_terms_4050_);
v___x_4062_ = ((size_t)0ULL);
v_terms_4063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_4061_, v___x_4062_, v_terms_4050_);
v___x_4064_ = lean_unsigned_to_nat(1u);
v___x_4065_ = lean_array_get_size(v_terms_4063_);
v___x_4066_ = lean_nat_dec_lt(v___x_4064_, v___x_4065_);
if (v___x_4066_ == 0)
{
v_terms_4053_ = v_terms_4063_;
goto v___jp_4052_;
}
else
{
lean_object* v___x_4067_; lean_object* v_firstElemsIdx_x3f_4068_; 
v___x_4067_ = lean_unsigned_to_nat(0u);
v_firstElemsIdx_x3f_4068_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_terms_4063_, v___x_4067_);
if (lean_obj_tag(v_firstElemsIdx_x3f_4068_) == 1)
{
lean_object* v_val_4069_; uint8_t v___x_4070_; 
v_val_4069_ = lean_ctor_get(v_firstElemsIdx_x3f_4068_, 0);
lean_inc(v_val_4069_);
lean_dec_ref_known(v_firstElemsIdx_x3f_4068_, 1);
v___x_4070_ = lean_nat_dec_lt(v_val_4069_, v___x_4065_);
if (v___x_4070_ == 0)
{
lean_dec(v_val_4069_);
v_terms_4053_ = v_terms_4063_;
goto v___jp_4052_;
}
else
{
lean_object* v_v_4071_; lean_object* v___x_4072_; lean_object* v_xs_x27_4073_; lean_object* v___y_4075_; 
v_v_4071_ = lean_array_fget(v_terms_4063_, v_val_4069_);
v___x_4072_ = lean_box(0);
v_xs_x27_4073_ = lean_array_fset(v_terms_4063_, v_val_4069_, v___x_4072_);
if (lean_obj_tag(v_v_4071_) == 0)
{
v___y_4075_ = v_v_4071_;
goto v___jp_4074_;
}
else
{
lean_object* v_docs_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; 
v_docs_4077_ = lean_ctor_get(v_v_4071_, 0);
v___x_4078_ = lean_array_get_size(v_docs_4077_);
v___x_4079_ = lean_nat_dec_lt(v___x_4067_, v___x_4078_);
if (v___x_4079_ == 0)
{
v___y_4075_ = v_v_4071_;
goto v___jp_4074_;
}
else
{
lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4090_; 
lean_inc_ref(v_docs_4077_);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_v_4071_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v_v_4071_, 0);
lean_dec(v_unused_4091_);
v___x_4081_ = v_v_4071_;
v_isShared_4082_ = v_isSharedCheck_4090_;
goto v_resetjp_4080_;
}
else
{
lean_dec(v_v_4071_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4090_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v_v_4083_; lean_object* v_xs_x27_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
v_v_4083_ = lean_array_fget(v_docs_4077_, v___x_4067_);
v_xs_x27_4084_ = lean_array_fset(v_docs_4077_, v___x_4067_, v___x_4072_);
v___x_4085_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4083_);
v___x_4086_ = lean_array_fset(v_xs_x27_4084_, v___x_4067_, v___x_4085_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 0, v___x_4086_);
v___x_4088_ = v___x_4081_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
v___y_4075_ = v___x_4088_;
goto v___jp_4074_;
}
}
}
}
v___jp_4074_:
{
lean_object* v___x_4076_; 
v___x_4076_ = lean_array_fset(v_xs_x27_4073_, v_val_4069_, v___y_4075_);
lean_dec(v_val_4069_);
v_terms_4053_ = v___x_4076_;
goto v___jp_4052_;
}
}
}
else
{
lean_dec(v_firstElemsIdx_x3f_4068_);
v_terms_4053_ = v_terms_4063_;
goto v___jp_4052_;
}
}
v___jp_4052_:
{
lean_object* v___x_4054_; size_t v_sz_4055_; size_t v___x_4056_; lean_object* v_terms_x27_4057_; lean_object* v_terms_x27_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4054_ = ((lean_object*)(l_Lean_Fmt_Layouts_metaApplication___closed__0));
v_sz_4055_ = lean_array_size(v_terms_4053_);
v___x_4056_ = ((size_t)0ULL);
v_terms_x27_4057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_4055_, v___x_4056_, v_terms_4053_);
v_terms_x27_4058_ = l_Lean_Fmt_Layouts_sepFill(v___x_4054_, v_terms_x27_4057_);
lean_dec_ref(v_terms_x27_4057_);
v___x_4059_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_4060_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4049_, v_terms_x27_4058_, v_rb_4051_, v___x_4059_);
return v___x_4060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object* v_chain_4094_){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = ((lean_object*)(l_Lean_Fmt_Layouts_pipeOperator___closed__0));
v___x_4096_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_4094_, v___x_4095_);
return v___x_4096_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0(void){
_start:
{
uint8_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = 1;
v___x_4098_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4099_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
lean_ctor_set_uint8(v___x_4099_, sizeof(void*)*1, v___x_4097_);
return v___x_4099_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default(void){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_obj_once(&l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0, &l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0);
return v___x_4100_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock(void){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0(lean_object* v_block_4102_){
_start:
{
uint8_t v___x_4103_; lean_object* v___x_4104_; 
v___x_4103_ = 1;
v___x_4104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4104_, 0, v_block_4102_);
lean_ctor_set_uint8(v___x_4104_, sizeof(void*)*1, v___x_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(lean_object* v_val_4107_, uint8_t v___x_4108_, lean_object* v___x_4109_, lean_object* v_____r_4110_, lean_object* v_stickyAcc_4111_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_4107_, v___x_4108_);
v___x_4113_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v___x_4109_, v_stickyAcc_4111_, v___x_4112_);
lean_dec(v___x_4112_);
v___x_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1___boxed(lean_object* v_val_4115_, lean_object* v___x_4116_, lean_object* v___x_4117_, lean_object* v_____r_4118_, lean_object* v_stickyAcc_4119_){
_start:
{
uint8_t v___x_1444__boxed_4120_; lean_object* v_res_4121_; 
v___x_1444__boxed_4120_ = lean_unbox(v___x_4116_);
v_res_4121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4115_, v___x_1444__boxed_4120_, v___x_4117_, v_____r_4118_, v_stickyAcc_4119_);
lean_dec_ref(v_val_4115_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(lean_object* v_upperBound_4122_, lean_object* v___y_4123_, lean_object* v___x_4124_, lean_object* v_a_4125_, lean_object* v_b_4126_){
_start:
{
uint8_t v___x_4127_; 
v___x_4127_ = lean_nat_dec_lt(v_a_4125_, v_upperBound_4122_);
if (v___x_4127_ == 0)
{
lean_dec(v_a_4125_);
return v_b_4126_;
}
else
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v_block_4130_; uint8_t v_hardNestedIfFirst_4131_; lean_object* v___x_4132_; lean_object* v_a_4134_; lean_object* v___y_4138_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4128_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4129_ = lean_array_get_borrowed(v___x_4128_, v___y_4123_, v_a_4125_);
v_block_4130_ = lean_ctor_get(v___x_4129_, 0);
v_hardNestedIfFirst_4131_ = lean_ctor_get_uint8(v___x_4129_, sizeof(void*)*1);
v___x_4132_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_b_4126_);
v___x_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4141_, 0, v_b_4126_);
v___x_4142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_4143_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4141_, v___x_4142_);
v___x_4144_ = lean_box(0);
lean_inc_ref_n(v_block_4130_, 2);
v___x_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4145_, 0, v_block_4130_);
v___x_4146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4144_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
lean_ctor_set(v___x_4146_, 2, v___x_4144_);
v___x_4147_ = lean_unsigned_to_nat(2u);
v___x_4148_ = lean_mk_empty_array_with_capacity(v___x_4147_);
lean_inc_ref(v___x_4148_);
v___x_4149_ = lean_array_push(v___x_4148_, v___x_4143_);
v___x_4150_ = lean_array_push(v___x_4149_, v___x_4146_);
v___x_4151_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4150_);
lean_dec_ref(v___x_4150_);
v___x_4152_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4151_);
v___x_4153_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_block_4130_);
if (lean_obj_tag(v___x_4153_) == 1)
{
lean_object* v_val_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4178_; 
v_val_4154_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4156_ = v___x_4153_;
v_isShared_4157_ = v_isSharedCheck_4178_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_val_4154_);
lean_dec(v___x_4153_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4178_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v_stickyVariant_4158_; lean_object* v___x_4159_; lean_object* v___x_4161_; 
v_stickyVariant_4158_ = lean_ctor_get(v_val_4154_, 0);
v___x_4159_ = l_Lean_Fmt_TaggedDoc_flattened(v_b_4126_);
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v___x_4159_);
v___x_4161_ = v___x_4156_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4163_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4161_, v___x_4162_);
lean_inc_ref(v_stickyVariant_4158_);
v___x_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4164_, 0, v_stickyVariant_4158_);
v___x_4165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4144_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
lean_ctor_set(v___x_4165_, 2, v___x_4144_);
v___x_4166_ = lean_array_push(v___x_4148_, v___x_4163_);
v___x_4167_ = lean_array_push(v___x_4166_, v___x_4165_);
v___x_4168_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4167_);
lean_dec_ref(v___x_4167_);
if (v_hardNestedIfFirst_4131_ == 0)
{
goto v___jp_4169_;
}
else
{
lean_object* v___x_4172_; uint8_t v___x_4173_; 
v___x_4172_ = lean_nat_sub(v___x_4124_, v___x_4132_);
v___x_4173_ = lean_nat_dec_lt(v_a_4125_, v___x_4172_);
lean_dec(v___x_4172_);
if (v___x_4173_ == 0)
{
goto v___jp_4169_;
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4174_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_4168_);
v___x_4175_ = lean_box(0);
v___x_4176_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4154_, v___x_4127_, v___x_4152_, v___x_4175_, v___x_4174_);
lean_dec(v_val_4154_);
v___y_4138_ = v___x_4176_;
goto v___jp_4137_;
}
}
v___jp_4169_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = lean_box(0);
v___x_4171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4154_, v___x_4127_, v___x_4152_, v___x_4170_, v___x_4168_);
lean_dec(v_val_4154_);
v___y_4138_ = v___x_4171_;
goto v___jp_4137_;
}
}
}
}
else
{
lean_dec(v___x_4153_);
lean_dec_ref(v___x_4148_);
lean_dec_ref(v_b_4126_);
v_a_4134_ = v___x_4152_;
goto v___jp_4133_;
}
v___jp_4133_:
{
lean_object* v___x_4135_; 
v___x_4135_ = lean_nat_add(v_a_4125_, v___x_4132_);
lean_dec(v_a_4125_);
v_a_4125_ = v___x_4135_;
v_b_4126_ = v_a_4134_;
goto _start;
}
v___jp_4137_:
{
if (lean_obj_tag(v___y_4138_) == 0)
{
lean_object* v_a_4139_; 
lean_dec(v_a_4125_);
v_a_4139_ = lean_ctor_get(v___y_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___y_4138_, 1);
return v_a_4139_;
}
else
{
lean_object* v_a_4140_; 
v_a_4140_ = lean_ctor_get(v___y_4138_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___y_4138_, 1);
v_a_4134_ = v_a_4140_;
goto v___jp_4133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___boxed(lean_object* v_upperBound_4179_, lean_object* v___y_4180_, lean_object* v___x_4181_, lean_object* v_a_4182_, lean_object* v_b_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4179_, v___y_4180_, v___x_4181_, v_a_4182_, v_b_4183_);
lean_dec(v___x_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v_upperBound_4179_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(lean_object* v_as_4185_, size_t v_i_4186_, size_t v_stop_4187_, lean_object* v_b_4188_){
_start:
{
lean_object* v___y_4190_; uint8_t v___x_4194_; 
v___x_4194_ = lean_usize_dec_eq(v_i_4186_, v_stop_4187_);
if (v___x_4194_ == 0)
{
lean_object* v___x_4195_; lean_object* v_block_4196_; uint8_t v___x_4197_; 
v___x_4195_ = lean_array_uget_borrowed(v_as_4185_, v_i_4186_);
v_block_4196_ = lean_ctor_get(v___x_4195_, 0);
v___x_4197_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_block_4196_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; 
lean_inc(v___x_4195_);
v___x_4198_ = lean_array_push(v_b_4188_, v___x_4195_);
v___y_4190_ = v___x_4198_;
goto v___jp_4189_;
}
else
{
v___y_4190_ = v_b_4188_;
goto v___jp_4189_;
}
}
else
{
return v_b_4188_;
}
v___jp_4189_:
{
size_t v___x_4191_; size_t v___x_4192_; 
v___x_4191_ = ((size_t)1ULL);
v___x_4192_ = lean_usize_add(v_i_4186_, v___x_4191_);
v_i_4186_ = v___x_4192_;
v_b_4188_ = v___y_4190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1___boxed(lean_object* v_as_4199_, lean_object* v_i_4200_, lean_object* v_stop_4201_, lean_object* v_b_4202_){
_start:
{
size_t v_i_boxed_4203_; size_t v_stop_boxed_4204_; lean_object* v_res_4205_; 
v_i_boxed_4203_ = lean_unbox_usize(v_i_4200_);
lean_dec(v_i_4200_);
v_stop_boxed_4204_ = lean_unbox_usize(v_stop_4201_);
lean_dec(v_stop_4201_);
v_res_4205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_as_4199_, v_i_boxed_4203_, v_stop_boxed_4204_, v_b_4202_);
lean_dec_ref(v_as_4199_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks(lean_object* v_blocks_4208_, uint8_t v_format_4209_){
_start:
{
lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___y_4220_; lean_object* v___x_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; 
v___x_4217_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4218_ = lean_unsigned_to_nat(0u);
v___x_4230_ = lean_array_get_size(v_blocks_4208_);
v___x_4231_ = ((lean_object*)(l_Lean_Fmt_Layouts_blocks___closed__0));
v___x_4232_ = lean_nat_dec_lt(v___x_4218_, v___x_4230_);
if (v___x_4232_ == 0)
{
v___y_4220_ = v___x_4231_;
goto v___jp_4219_;
}
else
{
size_t v___x_4233_; size_t v___x_4234_; lean_object* v___x_4235_; 
v___x_4233_ = ((size_t)0ULL);
v___x_4234_ = lean_usize_of_nat(v___x_4230_);
v___x_4235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4208_, v___x_4233_, v___x_4234_, v___x_4231_);
v___y_4220_ = v___x_4235_;
goto v___jp_4219_;
}
v___jp_4210_:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v___y_4213_, v___y_4211_, v___y_4213_, v___y_4212_, v___y_4214_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4213_);
if (v_format_4209_ == 0)
{
return v___x_4215_;
}
else
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4215_);
return v___x_4216_;
}
}
v___jp_4219_:
{
lean_object* v___x_4221_; uint8_t v___x_4222_; 
v___x_4221_ = lean_array_get_size(v___y_4220_);
v___x_4222_ = lean_nat_dec_eq(v___x_4221_, v___x_4218_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; lean_object* v_block_4224_; uint8_t v_hardNestedIfFirst_4225_; lean_object* v___x_4226_; uint8_t v___x_4227_; 
v___x_4223_ = lean_array_get_borrowed(v___x_4217_, v___y_4220_, v___x_4218_);
v_block_4224_ = lean_ctor_get(v___x_4223_, 0);
v_hardNestedIfFirst_4225_ = lean_ctor_get_uint8(v___x_4223_, sizeof(void*)*1);
v___x_4226_ = lean_unsigned_to_nat(1u);
v___x_4227_ = lean_nat_dec_eq(v___x_4221_, v___x_4226_);
if (v___x_4227_ == 0)
{
if (v_hardNestedIfFirst_4225_ == 0)
{
lean_inc_ref(v_block_4224_);
v___y_4211_ = v___y_4220_;
v___y_4212_ = v___x_4226_;
v___y_4213_ = v___x_4221_;
v___y_4214_ = v_block_4224_;
goto v___jp_4210_;
}
else
{
lean_object* v___x_4228_; 
lean_inc_ref(v_block_4224_);
v___x_4228_ = l_Lean_Fmt_TaggedDoc_hardNested(v_block_4224_);
v___y_4211_ = v___y_4220_;
v___y_4212_ = v___x_4226_;
v___y_4213_ = v___x_4221_;
v___y_4214_ = v___x_4228_;
goto v___jp_4210_;
}
}
else
{
lean_inc_ref(v_block_4224_);
lean_dec_ref(v___y_4220_);
return v_block_4224_;
}
}
else
{
lean_object* v___x_4229_; 
lean_dec_ref(v___y_4220_);
v___x_4229_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_4229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks___boxed(lean_object* v_blocks_4236_, lean_object* v_format_4237_){
_start:
{
uint8_t v_format_boxed_4238_; lean_object* v_res_4239_; 
v_format_boxed_4238_ = lean_unbox(v_format_4237_);
v_res_4239_ = l_Lean_Fmt_Layouts_blocks(v_blocks_4236_, v_format_boxed_4238_);
lean_dec_ref(v_blocks_4236_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(lean_object* v_upperBound_4240_, lean_object* v___y_4241_, lean_object* v___x_4242_, lean_object* v_inst_4243_, lean_object* v_R_4244_, lean_object* v_a_4245_, lean_object* v_b_4246_, lean_object* v_c_4247_){
_start:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4240_, v___y_4241_, v___x_4242_, v_a_4245_, v_b_4246_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___boxed(lean_object* v_upperBound_4249_, lean_object* v___y_4250_, lean_object* v___x_4251_, lean_object* v_inst_4252_, lean_object* v_R_4253_, lean_object* v_a_4254_, lean_object* v_b_4255_, lean_object* v_c_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(v_upperBound_4249_, v___y_4250_, v___x_4251_, v_inst_4252_, v_R_4253_, v_a_4254_, v_b_4255_, v_c_4256_);
lean_dec(v___x_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v_upperBound_4249_);
return v_res_4257_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_tuple___closed__0(void){
_start:
{
uint8_t v___x_4258_; uint8_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4258_ = 0;
v___x_4259_ = 1;
v___x_4260_ = l_Lean_Fmt_TaggedDoc_break;
v___x_4261_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
lean_ctor_set_uint8(v___x_4261_, sizeof(void*)*1, v___x_4259_);
lean_ctor_set_uint8(v___x_4261_, sizeof(void*)*1 + 1, v___x_4258_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple(lean_object* v_sep_4264_, lean_object* v_lb_4265_, lean_object* v_fields_4266_, lean_object* v_rb_4267_){
_start:
{
uint8_t v___x_4268_; lean_object* v_fields_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; uint8_t v___x_4272_; 
v___x_4268_ = 1;
lean_inc_ref(v_sep_4264_);
v_fields_4269_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4264_, v_fields_4266_, v___x_4268_);
v___x_4270_ = lean_array_get_size(v_fields_4269_);
v___x_4271_ = lean_unsigned_to_nat(1u);
v___x_4272_ = lean_nat_dec_eq(v___x_4270_, v___x_4271_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v_fields_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4273_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v_fields_4274_ = l_Lean_Fmt_Layouts_sepArray(v_sep_4264_, v_fields_4269_, v___x_4273_);
lean_dec_ref(v_fields_4269_);
v___x_4275_ = lean_obj_once(&l_Lean_Fmt_Layouts_tuple___closed__0, &l_Lean_Fmt_Layouts_tuple___closed__0_once, _init_l_Lean_Fmt_Layouts_tuple___closed__0);
v___x_4276_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4265_, v_fields_4274_, v_rb_4267_, v___x_4275_);
return v___x_4276_;
}
else
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
lean_dec_ref(v_sep_4264_);
v___x_4277_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4278_ = lean_unsigned_to_nat(0u);
v___x_4279_ = lean_array_get(v___x_4277_, v_fields_4269_, v___x_4278_);
lean_dec_ref(v_fields_4269_);
v___x_4280_ = ((lean_object*)(l_Lean_Fmt_Layouts_tuple___closed__1));
v___x_4281_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4265_, v___x_4279_, v_rb_4267_, v___x_4280_);
return v___x_4281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple___boxed(lean_object* v_sep_4282_, lean_object* v_lb_4283_, lean_object* v_fields_4284_, lean_object* v_rb_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_Fmt_Layouts_tuple(v_sep_4282_, v_lb_4283_, v_fields_4284_, v_rb_4285_);
lean_dec_ref(v_fields_4284_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection(lean_object* v_sep_4287_, lean_object* v_lb_4288_, lean_object* v_elems_4289_, lean_object* v_rb_4290_, lean_object* v_format_4291_){
_start:
{
lean_object* v___y_4293_; uint8_t v___x_4308_; lean_object* v_elems_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; 
v___x_4308_ = 1;
lean_inc_ref(v_sep_4287_);
v_elems_4309_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4287_, v_elems_4289_, v___x_4308_);
v___x_4310_ = lean_unsigned_to_nat(1u);
v___x_4311_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_elems_4309_);
v___x_4312_ = lean_nat_dec_lt(v___x_4310_, v___x_4311_);
lean_dec(v___x_4311_);
if (v___x_4312_ == 0)
{
v___y_4293_ = v_elems_4309_;
goto v___jp_4292_;
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; 
v___x_4313_ = lean_unsigned_to_nat(0u);
v___x_4314_ = lean_array_get_size(v_elems_4309_);
v___x_4315_ = lean_nat_dec_lt(v___x_4313_, v___x_4314_);
if (v___x_4315_ == 0)
{
v___y_4293_ = v_elems_4309_;
goto v___jp_4292_;
}
else
{
lean_object* v_v_4316_; lean_object* v___x_4317_; lean_object* v_xs_x27_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v_v_4316_ = lean_array_fget(v_elems_4309_, v___x_4313_);
v___x_4317_ = lean_box(0);
v_xs_x27_4318_ = lean_array_fset(v_elems_4309_, v___x_4313_, v___x_4317_);
v___x_4319_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4316_);
v___x_4320_ = lean_array_fset(v_xs_x27_4318_, v___x_4313_, v___x_4319_);
v___y_4293_ = v___x_4320_;
goto v___jp_4292_;
}
}
v___jp_4292_:
{
uint8_t v_spacing_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4307_; 
v_spacing_4294_ = lean_ctor_get_uint8(v_format_4291_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v_format_4291_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4296_ = v_format_4291_;
v_isShared_4297_ = v_isSharedCheck_4307_;
goto v_resetjp_4295_;
}
else
{
lean_dec(v_format_4291_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4307_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; lean_object* v_fields_4299_; uint8_t v___x_4300_; lean_object* v___x_4302_; 
v___x_4298_ = l_Lean_Fmt_Layouts_sepFill(v_sep_4287_, v___y_4293_);
lean_dec_ref(v___y_4293_);
v_fields_4299_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4298_);
v___x_4300_ = 1;
if (v_isShared_4297_ == 0)
{
v___x_4302_ = v___x_4296_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_4306_, 0, v_spacing_4294_);
v___x_4302_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
lean_object* v_doc_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; 
lean_ctor_set_uint8(v___x_4302_, 1, v___x_4300_);
v_doc_4303_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4288_, v_fields_4299_, v_rb_4290_, v___x_4302_);
v___x_4304_ = 1;
lean_inc_ref(v_doc_4303_);
v___x_4305_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4303_, v_doc_4303_, v___x_4304_);
return v___x_4305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection___boxed(lean_object* v_sep_4321_, lean_object* v_lb_4322_, lean_object* v_elems_4323_, lean_object* v_rb_4324_, lean_object* v_format_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_Fmt_Layouts_collection(v_sep_4321_, v_lb_4322_, v_elems_4323_, v_rb_4324_, v_format_4325_);
lean_dec_ref(v_elems_4323_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0(lean_object* v_keyword_4327_, lean_object* v_collection_4328_){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4329_ = lean_unsigned_to_nat(2u);
v___x_4330_ = lean_mk_empty_array_with_capacity(v___x_4329_);
v___x_4331_ = lean_array_push(v___x_4330_, v_keyword_4327_);
v___x_4332_ = lean_array_push(v___x_4331_, v_collection_4328_);
v___x_4333_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4332_);
lean_dec_ref(v___x_4332_);
v___x_4334_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4333_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object* v_sep_4335_, lean_object* v_keyword_4336_, lean_object* v_lb_4337_, lean_object* v_elems_4338_, lean_object* v_rb_4339_, lean_object* v_format_4340_){
_start:
{
lean_object* v___f_4341_; lean_object* v_collection_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___f_4341_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0), 2, 1);
lean_closure_set(v___f_4341_, 0, v_keyword_4336_);
v_collection_4342_ = l_Lean_Fmt_Layouts_collection(v_sep_4335_, v_lb_4337_, v_elems_4338_, v_rb_4339_, v_format_4340_);
v___x_4343_ = lean_box(0);
v___x_4344_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_collection_4342_, v___f_4341_, v___x_4343_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___boxed(lean_object* v_sep_4345_, lean_object* v_keyword_4346_, lean_object* v_lb_4347_, lean_object* v_elems_4348_, lean_object* v_rb_4349_, lean_object* v_format_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_Lean_Fmt_Layouts_keywordPrefixedCollection(v_sep_4345_, v_keyword_4346_, v_lb_4347_, v_elems_4348_, v_rb_4349_, v_format_4350_);
lean_dec_ref(v_elems_4348_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl(lean_object* v_x_4352_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = lean_obj_tag_nat(v_x_4352_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl___boxed(lean_object* v_x_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl(v_x_4354_);
lean_dec(v_x_4354_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object* v_t_4356_, lean_object* v_k_4357_){
_start:
{
if (lean_obj_tag(v_t_4356_) == 0)
{
uint8_t v_respectPseudoAlignment_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_respectPseudoAlignment_4358_ = lean_ctor_get_uint8(v_t_4356_, 0);
v___x_4359_ = lean_box(v_respectPseudoAlignment_4358_);
v___x_4360_ = lean_apply_1(v_k_4357_, v___x_4359_);
return v___x_4360_;
}
else
{
return v_k_4357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object* v_t_4361_, lean_object* v_k_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4361_, v_k_4362_);
lean_dec(v_t_4361_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object* v_motive_4364_, lean_object* v_ctorIdx_4365_, lean_object* v_t_4366_, lean_object* v_h_4367_, lean_object* v_k_4368_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4366_, v_k_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object* v_motive_4370_, lean_object* v_ctorIdx_4371_, lean_object* v_t_4372_, lean_object* v_h_4373_, lean_object* v_k_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(v_motive_4370_, v_ctorIdx_4371_, v_t_4372_, v_h_4373_, v_k_4374_);
lean_dec(v_t_4372_);
lean_dec(v_ctorIdx_4371_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object* v_t_4376_, lean_object* v_local_4377_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4376_, v_local_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object* v_t_4379_, lean_object* v_local_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(v_t_4379_, v_local_4380_);
lean_dec(v_t_4379_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object* v_motive_4382_, lean_object* v_t_4383_, lean_object* v_h_4384_, lean_object* v_local_4385_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4383_, v_local_4385_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object* v_motive_4387_, lean_object* v_t_4388_, lean_object* v_h_4389_, lean_object* v_local_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(v_motive_4387_, v_t_4388_, v_h_4389_, v_local_4390_);
lean_dec(v_t_4388_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object* v_t_4392_, lean_object* v_global_4393_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4392_, v_global_4393_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object* v_t_4395_, lean_object* v_global_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(v_t_4395_, v_global_4396_);
lean_dec(v_t_4395_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object* v_motive_4398_, lean_object* v_t_4399_, lean_object* v_h_4400_, lean_object* v_global_4401_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4399_, v_global_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object* v_motive_4403_, lean_object* v_t_4404_, lean_object* v_h_4405_, lean_object* v_global_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(v_motive_4403_, v_t_4404_, v_h_4405_, v_global_4406_);
lean_dec(v_t_4404_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(lean_object* v_as_4408_, size_t v_i_4409_, size_t v_stop_4410_, lean_object* v_b_4411_){
_start:
{
lean_object* v___y_4413_; uint8_t v___x_4417_; 
v___x_4417_ = lean_usize_dec_eq(v_i_4409_, v_stop_4410_);
if (v___x_4417_ == 0)
{
lean_object* v___x_4418_; uint8_t v___x_4419_; 
v___x_4418_ = lean_array_uget_borrowed(v_as_4408_, v_i_4409_);
v___x_4419_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_4418_);
if (v___x_4419_ == 0)
{
lean_object* v___x_4420_; 
lean_inc(v___x_4418_);
v___x_4420_ = lean_array_push(v_b_4411_, v___x_4418_);
v___y_4413_ = v___x_4420_;
goto v___jp_4412_;
}
else
{
v___y_4413_ = v_b_4411_;
goto v___jp_4412_;
}
}
else
{
return v_b_4411_;
}
v___jp_4412_:
{
size_t v___x_4414_; size_t v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = ((size_t)1ULL);
v___x_4415_ = lean_usize_add(v_i_4409_, v___x_4414_);
v___x_4416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_as_4408_, v___x_4415_, v_stop_4410_, v___y_4413_);
return v___x_4416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object* v_as_4421_, lean_object* v_i_4422_, lean_object* v_stop_4423_, lean_object* v_b_4424_){
_start:
{
size_t v_i_boxed_4425_; size_t v_stop_boxed_4426_; lean_object* v_res_4427_; 
v_i_boxed_4425_ = lean_unbox_usize(v_i_4422_);
lean_dec(v_i_4422_);
v_stop_boxed_4426_ = lean_unbox_usize(v_stop_4423_);
lean_dec(v_stop_4423_);
v_res_4427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_as_4421_, v_i_boxed_4425_, v_stop_boxed_4426_, v_b_4424_);
lean_dec_ref(v_as_4421_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(size_t v_sz_4428_, size_t v_i_4429_, lean_object* v_bs_4430_){
_start:
{
uint8_t v___x_4431_; 
v___x_4431_ = lean_usize_dec_lt(v_i_4429_, v_sz_4428_);
if (v___x_4431_ == 0)
{
return v_bs_4430_;
}
else
{
lean_object* v_v_4432_; lean_object* v___x_4433_; lean_object* v_bs_x27_4434_; lean_object* v___x_4435_; size_t v___x_4436_; size_t v___x_4437_; lean_object* v___x_4438_; 
v_v_4432_ = lean_array_uget(v_bs_4430_, v_i_4429_);
v___x_4433_ = lean_unsigned_to_nat(0u);
v_bs_x27_4434_ = lean_array_uset(v_bs_4430_, v_i_4429_, v___x_4433_);
v___x_4435_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(v_v_4432_);
v___x_4436_ = ((size_t)1ULL);
v___x_4437_ = lean_usize_add(v_i_4429_, v___x_4436_);
v___x_4438_ = lean_array_uset(v_bs_x27_4434_, v_i_4429_, v___x_4435_);
v_i_4429_ = v___x_4437_;
v_bs_4430_ = v___x_4438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3___boxed(lean_object* v_sz_4440_, lean_object* v_i_4441_, lean_object* v_bs_4442_){
_start:
{
size_t v_sz_boxed_4443_; size_t v_i_boxed_4444_; lean_object* v_res_4445_; 
v_sz_boxed_4443_ = lean_unbox_usize(v_sz_4440_);
lean_dec(v_sz_4440_);
v_i_boxed_4444_ = lean_unbox_usize(v_i_4441_);
lean_dec(v_i_4441_);
v_res_4445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(v_sz_boxed_4443_, v_i_boxed_4444_, v_bs_4442_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(lean_object* v_as_4446_, size_t v_i_4447_, size_t v_stop_4448_, lean_object* v_b_4449_){
_start:
{
lean_object* v___y_4451_; uint8_t v___x_4455_; 
v___x_4455_ = lean_usize_dec_eq(v_i_4447_, v_stop_4448_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; lean_object* v___y_4458_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; uint8_t v___x_4465_; 
v___x_4456_ = lean_unsigned_to_nat(0u);
v___x_4462_ = lean_array_uget_borrowed(v_as_4446_, v_i_4447_);
v___x_4463_ = lean_array_get_size(v___x_4462_);
v___x_4464_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4465_ = lean_nat_dec_lt(v___x_4456_, v___x_4463_);
if (v___x_4465_ == 0)
{
v___y_4458_ = v___x_4464_;
goto v___jp_4457_;
}
else
{
size_t v___x_4466_; size_t v___x_4467_; lean_object* v___x_4468_; 
v___x_4466_ = ((size_t)0ULL);
v___x_4467_ = lean_usize_of_nat(v___x_4463_);
v___x_4468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v___x_4462_, v___x_4466_, v___x_4467_, v___x_4464_);
v___y_4458_ = v___x_4468_;
goto v___jp_4457_;
}
v___jp_4457_:
{
lean_object* v___x_4459_; uint8_t v___x_4460_; 
v___x_4459_ = lean_array_get_size(v___y_4458_);
v___x_4460_ = lean_nat_dec_eq(v___x_4459_, v___x_4456_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; 
v___x_4461_ = lean_array_push(v_b_4449_, v___y_4458_);
v___y_4451_ = v___x_4461_;
goto v___jp_4450_;
}
else
{
lean_dec_ref(v___y_4458_);
v___y_4451_ = v_b_4449_;
goto v___jp_4450_;
}
}
}
else
{
return v_b_4449_;
}
v___jp_4450_:
{
size_t v___x_4452_; size_t v___x_4453_; 
v___x_4452_ = ((size_t)1ULL);
v___x_4453_ = lean_usize_add(v_i_4447_, v___x_4452_);
v_i_4447_ = v___x_4453_;
v_b_4449_ = v___y_4451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1___boxed(lean_object* v_as_4469_, lean_object* v_i_4470_, lean_object* v_stop_4471_, lean_object* v_b_4472_){
_start:
{
size_t v_i_boxed_4473_; size_t v_stop_boxed_4474_; lean_object* v_res_4475_; 
v_i_boxed_4473_ = lean_unbox_usize(v_i_4470_);
lean_dec(v_i_4470_);
v_stop_boxed_4474_ = lean_unbox_usize(v_stop_4471_);
lean_dec(v_stop_4471_);
v_res_4475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4469_, v_i_boxed_4473_, v_stop_boxed_4474_, v_b_4472_);
lean_dec_ref(v_as_4469_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(lean_object* v_as_4478_, lean_object* v_start_4479_, lean_object* v_stop_4480_){
_start:
{
lean_object* v___x_4481_; uint8_t v___x_4482_; 
v___x_4481_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0));
v___x_4482_ = lean_nat_dec_lt(v_start_4479_, v_stop_4480_);
if (v___x_4482_ == 0)
{
return v___x_4481_;
}
else
{
lean_object* v___x_4483_; uint8_t v___x_4484_; 
v___x_4483_ = lean_array_get_size(v_as_4478_);
v___x_4484_ = lean_nat_dec_le(v_stop_4480_, v___x_4483_);
if (v___x_4484_ == 0)
{
uint8_t v___x_4485_; 
v___x_4485_ = lean_nat_dec_lt(v_start_4479_, v___x_4483_);
if (v___x_4485_ == 0)
{
return v___x_4481_;
}
else
{
size_t v___x_4486_; size_t v___x_4487_; lean_object* v___x_4488_; 
v___x_4486_ = lean_usize_of_nat(v_start_4479_);
v___x_4487_ = lean_usize_of_nat(v___x_4483_);
v___x_4488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4478_, v___x_4486_, v___x_4487_, v___x_4481_);
return v___x_4488_;
}
}
else
{
size_t v___x_4489_; size_t v___x_4490_; lean_object* v___x_4491_; 
v___x_4489_ = lean_usize_of_nat(v_start_4479_);
v___x_4490_ = lean_usize_of_nat(v_stop_4480_);
v___x_4491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4478_, v___x_4489_, v___x_4490_, v___x_4481_);
return v___x_4491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___boxed(lean_object* v_as_4492_, lean_object* v_start_4493_, lean_object* v_stop_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v_as_4492_, v_start_4493_, v_stop_4494_);
lean_dec(v_stop_4494_);
lean_dec(v_start_4493_);
lean_dec_ref(v_as_4492_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(lean_object* v_as_4496_, size_t v_i_4497_, size_t v_stop_4498_, lean_object* v_b_4499_){
_start:
{
lean_object* v___y_4501_; uint8_t v___x_4505_; 
v___x_4505_ = lean_usize_dec_eq(v_i_4497_, v_stop_4498_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v_group_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4506_ = lean_unsigned_to_nat(0u);
v___x_4507_ = lean_array_uget_borrowed(v_as_4496_, v_i_4497_);
v___x_4508_ = lean_array_get_size(v___x_4507_);
v_group_4509_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v___x_4507_, v___x_4506_, v___x_4508_);
v___x_4510_ = lean_array_get_size(v_group_4509_);
v___x_4511_ = lean_nat_dec_eq(v___x_4510_, v___x_4506_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; 
v___x_4512_ = lean_array_push(v_b_4499_, v_group_4509_);
v___y_4501_ = v___x_4512_;
goto v___jp_4500_;
}
else
{
lean_dec_ref(v_group_4509_);
v___y_4501_ = v_b_4499_;
goto v___jp_4500_;
}
}
else
{
return v_b_4499_;
}
v___jp_4500_:
{
size_t v___x_4502_; size_t v___x_4503_; 
v___x_4502_ = ((size_t)1ULL);
v___x_4503_ = lean_usize_add(v_i_4497_, v___x_4502_);
v_i_4497_ = v___x_4503_;
v_b_4499_ = v___y_4501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3___boxed(lean_object* v_as_4513_, lean_object* v_i_4514_, lean_object* v_stop_4515_, lean_object* v_b_4516_){
_start:
{
size_t v_i_boxed_4517_; size_t v_stop_boxed_4518_; lean_object* v_res_4519_; 
v_i_boxed_4517_ = lean_unbox_usize(v_i_4514_);
lean_dec(v_i_4514_);
v_stop_boxed_4518_ = lean_unbox_usize(v_stop_4515_);
lean_dec(v_stop_4515_);
v_res_4519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4513_, v_i_boxed_4517_, v_stop_boxed_4518_, v_b_4516_);
lean_dec_ref(v_as_4513_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(lean_object* v_as_4522_, lean_object* v_start_4523_, lean_object* v_stop_4524_){
_start:
{
lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4525_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___closed__0));
v___x_4526_ = lean_nat_dec_lt(v_start_4523_, v_stop_4524_);
if (v___x_4526_ == 0)
{
return v___x_4525_;
}
else
{
lean_object* v___x_4527_; uint8_t v___x_4528_; 
v___x_4527_ = lean_array_get_size(v_as_4522_);
v___x_4528_ = lean_nat_dec_le(v_stop_4524_, v___x_4527_);
if (v___x_4528_ == 0)
{
uint8_t v___x_4529_; 
v___x_4529_ = lean_nat_dec_lt(v_start_4523_, v___x_4527_);
if (v___x_4529_ == 0)
{
return v___x_4525_;
}
else
{
size_t v___x_4530_; size_t v___x_4531_; lean_object* v___x_4532_; 
v___x_4530_ = lean_usize_of_nat(v_start_4523_);
v___x_4531_ = lean_usize_of_nat(v___x_4527_);
v___x_4532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4522_, v___x_4530_, v___x_4531_, v___x_4525_);
return v___x_4532_;
}
}
else
{
size_t v___x_4533_; size_t v___x_4534_; lean_object* v___x_4535_; 
v___x_4533_ = lean_usize_of_nat(v_start_4523_);
v___x_4534_ = lean_usize_of_nat(v_stop_4524_);
v___x_4535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4522_, v___x_4533_, v___x_4534_, v___x_4525_);
return v___x_4535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___boxed(lean_object* v_as_4536_, lean_object* v_start_4537_, lean_object* v_stop_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_as_4536_, v_start_4537_, v_stop_4538_);
lean_dec(v_stop_4538_);
lean_dec(v_start_4537_);
lean_dec_ref(v_as_4536_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object* v_lvals_4540_, lean_object* v_binderGroups_4541_, lean_object* v_typeAscriptionTk_4542_, lean_object* v_type_4543_, lean_object* v_kind_4544_, lean_object* v_lvalsLayout_4545_){
_start:
{
lean_object* v___y_4547_; uint8_t v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4564_; uint8_t v___y_4565_; lean_object* v___y_4566_; lean_object* v___x_4572_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4585_; lean_object* v___x_4595_; lean_object* v___x_4596_; uint8_t v___x_4597_; 
v___x_4572_ = lean_unsigned_to_nat(0u);
v___x_4595_ = lean_array_get_size(v_lvals_4540_);
v___x_4596_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4597_ = lean_nat_dec_lt(v___x_4572_, v___x_4595_);
if (v___x_4597_ == 0)
{
v___y_4585_ = v___x_4596_;
goto v___jp_4584_;
}
else
{
size_t v___x_4598_; size_t v___x_4599_; lean_object* v___x_4600_; 
v___x_4598_ = ((size_t)0ULL);
v___x_4599_ = lean_usize_of_nat(v___x_4595_);
v___x_4600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_lvals_4540_, v___x_4598_, v___x_4599_, v___x_4596_);
v___y_4585_ = v___x_4600_;
goto v___jp_4584_;
}
v___jp_4546_:
{
size_t v_sz_4551_; size_t v___x_4552_; lean_object* v___x_4553_; lean_object* v_binderGroups_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v_sz_4551_ = lean_array_size(v___y_4547_);
v___x_4552_ = ((size_t)0ULL);
v___x_4553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(v_sz_4551_, v___x_4552_, v___y_4547_);
v_binderGroups_4554_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4553_, v___y_4548_);
lean_dec_ref(v___x_4553_);
v___x_4555_ = lean_apply_1(v_lvalsLayout_4545_, v___y_4549_);
v___x_4556_ = lean_unsigned_to_nat(2u);
v___x_4557_ = lean_mk_empty_array_with_capacity(v___x_4556_);
v___x_4558_ = lean_array_push(v___x_4557_, v___x_4555_);
v___x_4559_ = lean_array_push(v___x_4558_, v_binderGroups_4554_);
v___x_4560_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4559_, v___y_4548_);
lean_dec_ref(v___x_4559_);
v___x_4561_ = l_Lean_Fmt_Layouts_typeAscription(v___x_4560_, v_typeAscriptionTk_4542_, v_type_4543_, v___y_4550_);
lean_dec_ref(v___y_4550_);
v___x_4562_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4561_);
return v___x_4562_;
}
v___jp_4563_:
{
if (lean_obj_tag(v_kind_4544_) == 0)
{
uint8_t v_respectPseudoAlignment_4567_; uint8_t v___x_4568_; lean_object* v___x_4569_; 
v_respectPseudoAlignment_4567_ = lean_ctor_get_uint8(v_kind_4544_, 0);
v___x_4568_ = 0;
v___x_4569_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4569_, 0, v___x_4568_);
lean_ctor_set_uint8(v___x_4569_, 1, v___x_4568_);
lean_ctor_set_uint8(v___x_4569_, 2, v___y_4565_);
lean_ctor_set_uint8(v___x_4569_, 3, v_respectPseudoAlignment_4567_);
v___y_4547_ = v___y_4564_;
v___y_4548_ = v___y_4565_;
v___y_4549_ = v___y_4566_;
v___y_4550_ = v___x_4569_;
goto v___jp_4546_;
}
else
{
uint8_t v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = 0;
v___x_4571_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_4571_, 0, v___x_4570_);
lean_ctor_set_uint8(v___x_4571_, 1, v___x_4570_);
lean_ctor_set_uint8(v___x_4571_, 2, v___y_4565_);
lean_ctor_set_uint8(v___x_4571_, 3, v___x_4570_);
lean_ctor_set_uint8(v___x_4571_, 4, v___x_4570_);
v___y_4547_ = v___y_4564_;
v___y_4548_ = v___y_4565_;
v___y_4549_ = v___y_4566_;
v___y_4550_ = v___x_4571_;
goto v___jp_4546_;
}
}
v___jp_4573_:
{
uint8_t v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4576_ = 1;
v___x_4577_ = lean_array_get_size(v___y_4575_);
v___x_4578_ = lean_nat_dec_lt(v___x_4572_, v___x_4577_);
if (v___x_4578_ == 0)
{
v___y_4564_ = v___y_4574_;
v___y_4565_ = v___x_4576_;
v___y_4566_ = v___y_4575_;
goto v___jp_4563_;
}
else
{
lean_object* v_v_4579_; lean_object* v___x_4580_; lean_object* v_xs_x27_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v_v_4579_ = lean_array_fget(v___y_4575_, v___x_4572_);
v___x_4580_ = lean_box(0);
v_xs_x27_4581_ = lean_array_fset(v___y_4575_, v___x_4572_, v___x_4580_);
v___x_4582_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4579_);
v___x_4583_ = lean_array_fset(v_xs_x27_4581_, v___x_4572_, v___x_4582_);
v___y_4564_ = v___y_4574_;
v___y_4565_ = v___x_4576_;
v___y_4566_ = v___x_4583_;
goto v___jp_4563_;
}
}
v___jp_4584_:
{
lean_object* v___x_4586_; lean_object* v_binderGroups_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; 
v___x_4586_ = lean_array_get_size(v_binderGroups_4541_);
v_binderGroups_4587_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_binderGroups_4541_, v___x_4572_, v___x_4586_);
v___x_4588_ = lean_array_get_size(v___y_4585_);
v___x_4589_ = lean_unsigned_to_nat(1u);
v___x_4590_ = lean_nat_dec_le(v___x_4588_, v___x_4589_);
if (v___x_4590_ == 0)
{
v___y_4574_ = v_binderGroups_4587_;
v___y_4575_ = v___y_4585_;
goto v___jp_4573_;
}
else
{
uint8_t v___x_4591_; 
v___x_4591_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_type_4543_);
if (v___x_4591_ == 0)
{
v___y_4574_ = v_binderGroups_4587_;
v___y_4575_ = v___y_4585_;
goto v___jp_4573_;
}
else
{
uint8_t v___x_4592_; 
v___x_4592_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_typeAscriptionTk_4542_);
if (v___x_4592_ == 0)
{
v___y_4574_ = v_binderGroups_4587_;
v___y_4575_ = v___y_4585_;
goto v___jp_4573_;
}
else
{
lean_object* v___x_4593_; uint8_t v___x_4594_; 
v___x_4593_ = lean_array_get_size(v_binderGroups_4587_);
v___x_4594_ = lean_nat_dec_eq(v___x_4593_, v___x_4572_);
if (v___x_4594_ == 0)
{
v___y_4574_ = v_binderGroups_4587_;
v___y_4575_ = v___y_4585_;
goto v___jp_4573_;
}
else
{
v___y_4564_ = v_binderGroups_4587_;
v___y_4565_ = v___x_4592_;
v___y_4566_ = v___y_4585_;
goto v___jp_4563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object* v_lvals_4601_, lean_object* v_binderGroups_4602_, lean_object* v_typeAscriptionTk_4603_, lean_object* v_type_4604_, lean_object* v_kind_4605_, lean_object* v_lvalsLayout_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4601_, v_binderGroups_4602_, v_typeAscriptionTk_4603_, v_type_4604_, v_kind_4605_, v_lvalsLayout_4606_);
lean_dec(v_kind_4605_);
lean_dec_ref(v_binderGroups_4602_);
lean_dec_ref(v_lvals_4601_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(uint8_t v___x_4608_, lean_object* v_terms_4609_){
_start:
{
lean_object* v___x_4610_; 
v___x_4610_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4609_, v___x_4608_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object* v___x_4611_, lean_object* v_terms_4612_){
_start:
{
uint8_t v___x_9__boxed_4613_; lean_object* v_res_4614_; 
v___x_9__boxed_4613_ = lean_unbox(v___x_4611_);
v_res_4614_ = l_Lean_Fmt_Layouts_localSignature___lam__0(v___x_9__boxed_4613_, v_terms_4612_);
lean_dec_ref(v_terms_4612_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object* v_lvals_4620_, lean_object* v_binderGroups_4621_, lean_object* v_typeAscriptionTk_4622_, lean_object* v_type_4623_){
_start:
{
lean_object* v___f_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___f_4624_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__0));
v___x_4625_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__1));
v___x_4626_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4620_, v_binderGroups_4621_, v_typeAscriptionTk_4622_, v_type_4623_, v___x_4625_, v___f_4624_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object* v_lvals_4627_, lean_object* v_binderGroups_4628_, lean_object* v_typeAscriptionTk_4629_, lean_object* v_type_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_Lean_Fmt_Layouts_localSignature(v_lvals_4627_, v_binderGroups_4628_, v_typeAscriptionTk_4629_, v_type_4630_);
lean_dec_ref(v_binderGroups_4628_);
lean_dec_ref(v_lvals_4627_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0(lean_object* v_terms_4632_){
_start:
{
uint8_t v___x_4633_; lean_object* v___x_4634_; 
v___x_4633_ = 1;
v___x_4634_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4632_, v___x_4633_);
return v___x_4634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0___boxed(lean_object* v_terms_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Lean_Fmt_Layouts_globalSignature___lam__0(v_terms_4635_);
lean_dec_ref(v_terms_4635_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object* v_lvals_4638_, lean_object* v_binderGroups_4639_, lean_object* v_typeAscriptionTk_4640_, lean_object* v_type_4641_){
_start:
{
lean_object* v___f_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___f_4642_ = ((lean_object*)(l_Lean_Fmt_Layouts_globalSignature___closed__0));
v___x_4643_ = lean_box(1);
v___x_4644_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4638_, v_binderGroups_4639_, v_typeAscriptionTk_4640_, v_type_4641_, v___x_4643_, v___f_4642_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object* v_lvals_4645_, lean_object* v_binderGroups_4646_, lean_object* v_typeAscriptionTk_4647_, lean_object* v_type_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Lean_Fmt_Layouts_globalSignature(v_lvals_4645_, v_binderGroups_4646_, v_typeAscriptionTk_4647_, v_type_4648_);
lean_dec_ref(v_binderGroups_4646_);
lean_dec_ref(v_lvals_4645_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object* v_signature_4650_, lean_object* v_separationTk_4651_, lean_object* v_body_4652_, uint8_t v_sticky_4653_){
_start:
{
uint8_t v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; uint8_t v___y_4659_; uint8_t v___y_4663_; lean_object* v___y_4664_; uint8_t v___x_4703_; 
v___x_4703_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_separationTk_4651_);
if (v___x_4703_ == 0)
{
goto v___jp_4687_;
}
else
{
uint8_t v___x_4704_; 
v___x_4704_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4652_);
if (v___x_4704_ == 0)
{
goto v___jp_4687_;
}
else
{
lean_inc_ref(v_signature_4650_);
v___y_4663_ = v___x_4703_;
v___y_4664_ = v_signature_4650_;
goto v___jp_4662_;
}
}
v___jp_4654_:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
lean_inc_ref(v___y_4656_);
v___x_4660_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___y_4657_, v___y_4656_, v_body_4652_, v___y_4659_);
v___x_4661_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_4658_, v___x_4660_, v___y_4655_);
return v___x_4661_;
}
v___jp_4662_:
{
lean_object* v_doc_4665_; 
v_doc_4665_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___y_4664_);
if (v_sticky_4653_ == 0)
{
lean_dec_ref(v_body_4652_);
lean_dec_ref(v_separationTk_4651_);
lean_dec_ref(v_signature_4650_);
return v_doc_4665_;
}
else
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v_lhs_4677_; lean_object* v___x_4678_; 
v___x_4666_ = l_Lean_Fmt_TaggedDoc_flattened(v_signature_4650_);
v___x_4667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
v___x_4668_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1);
v___x_4669_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4667_, v___x_4668_);
v___x_4670_ = lean_box(0);
v___x_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4671_, 0, v_separationTk_4651_);
v___x_4672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4670_);
lean_ctor_set(v___x_4672_, 1, v___x_4671_);
lean_ctor_set(v___x_4672_, 2, v___x_4670_);
v___x_4673_ = lean_unsigned_to_nat(2u);
v___x_4674_ = lean_mk_empty_array_with_capacity(v___x_4673_);
v___x_4675_ = lean_array_push(v___x_4674_, v___x_4669_);
v___x_4676_ = lean_array_push(v___x_4675_, v___x_4672_);
v_lhs_4677_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4676_);
lean_dec_ref(v___x_4676_);
lean_inc_ref(v_body_4652_);
v___x_4678_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_body_4652_);
if (lean_obj_tag(v___x_4678_) == 1)
{
lean_object* v_val_4679_; uint8_t v_kind_4680_; lean_object* v___x_4681_; 
v_val_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_val_4679_);
lean_dec_ref_known(v___x_4678_, 1);
v_kind_4680_ = lean_ctor_get_uint8(v_val_4679_, sizeof(void*)*1);
lean_dec(v_val_4679_);
v___x_4681_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
if (v_kind_4680_ == 1)
{
uint8_t v___x_4682_; 
v___x_4682_ = 0;
v___y_4655_ = v_kind_4680_;
v___y_4656_ = v___x_4681_;
v___y_4657_ = v_lhs_4677_;
v___y_4658_ = v_doc_4665_;
v___y_4659_ = v___x_4682_;
goto v___jp_4654_;
}
else
{
v___y_4655_ = v_kind_4680_;
v___y_4656_ = v___x_4681_;
v___y_4657_ = v_lhs_4677_;
v___y_4658_ = v_doc_4665_;
v___y_4659_ = v_sticky_4653_;
goto v___jp_4654_;
}
}
else
{
lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; lean_object* v___x_4686_; 
lean_dec(v___x_4678_);
v___x_4683_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4684_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4677_, v___x_4683_, v_body_4652_, v___y_4663_);
v___x_4685_ = 0;
v___x_4686_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4665_, v___x_4684_, v___x_4685_);
return v___x_4686_;
}
}
}
v___jp_4687_:
{
uint8_t v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v_lhs_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4688_ = 1;
lean_inc_ref(v_signature_4650_);
v___x_4689_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4650_);
v___x_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
v___x_4691_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1);
v___x_4692_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4690_, v___x_4691_);
v___x_4693_ = lean_box(0);
lean_inc_ref(v_separationTk_4651_);
v___x_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4694_, 0, v_separationTk_4651_);
v___x_4695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4693_);
lean_ctor_set(v___x_4695_, 1, v___x_4694_);
lean_ctor_set(v___x_4695_, 2, v___x_4693_);
v___x_4696_ = lean_unsigned_to_nat(2u);
v___x_4697_ = lean_mk_empty_array_with_capacity(v___x_4696_);
v___x_4698_ = lean_array_push(v___x_4697_, v___x_4692_);
v___x_4699_ = lean_array_push(v___x_4698_, v___x_4695_);
v_lhs_4700_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4699_);
lean_dec_ref(v___x_4699_);
v___x_4701_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_body_4652_);
v___x_4702_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4700_, v___x_4701_, v_body_4652_, v___x_4688_);
v___y_4663_ = v___x_4688_;
v___y_4664_ = v___x_4702_;
goto v___jp_4662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object* v_signature_4705_, lean_object* v_separationTk_4706_, lean_object* v_body_4707_, lean_object* v_sticky_4708_){
_start:
{
uint8_t v_sticky_boxed_4709_; lean_object* v_res_4710_; 
v_sticky_boxed_4709_ = lean_unbox(v_sticky_4708_);
v_res_4710_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_signature_4705_, v_separationTk_4706_, v_body_4707_, v_sticky_boxed_4709_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object* v_signature_4711_, lean_object* v_matchAlts_4712_){
_start:
{
uint8_t v___x_4713_; 
v___x_4713_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_matchAlts_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4714_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4711_);
v___x_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
v___x_4716_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4717_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4715_, v___x_4716_);
v___x_4718_ = lean_box(0);
v___x_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4719_, 0, v_matchAlts_4712_);
v___x_4720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4718_);
lean_ctor_set(v___x_4720_, 1, v___x_4719_);
lean_ctor_set(v___x_4720_, 2, v___x_4718_);
v___x_4721_ = lean_unsigned_to_nat(2u);
v___x_4722_ = lean_mk_empty_array_with_capacity(v___x_4721_);
v___x_4723_ = lean_array_push(v___x_4722_, v___x_4717_);
v___x_4724_ = lean_array_push(v___x_4723_, v___x_4720_);
v___x_4725_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4724_);
lean_dec_ref(v___x_4724_);
return v___x_4725_;
}
else
{
lean_dec_ref(v_matchAlts_4712_);
return v_signature_4711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object* v_signature_4729_, lean_object* v_whereTk_4730_, lean_object* v_body_4731_){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = ((lean_object*)(l_Lean_Fmt_Layouts_whereDeclaration___closed__0));
v___x_4733_ = l_Lean_Fmt_Layouts_keywordSeparated(v_signature_4729_, v_whereTk_4730_, v_body_4731_, v___x_4732_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object* v_lbs_4735_, lean_object* v_lhses_4736_, lean_object* v_subBinderGroups_4737_, lean_object* v_typeAscriptionTk_x3f_4738_, lean_object* v_type_x3f_4739_, lean_object* v_colonEqTk_x3f_4740_, lean_object* v_default_x3f_4741_, lean_object* v_rbs_4742_, lean_object* v_kind_4743_){
_start:
{
lean_object* v_lbs_4744_; lean_object* v___x_4745_; lean_object* v_binderSignature_4746_; uint8_t v___x_4747_; lean_object* v_simpleBinder_4748_; lean_object* v_rbs_4749_; lean_object* v___x_4750_; 
v_lbs_4744_ = l_Lean_Fmt_Layouts_atomic(v_lbs_4735_);
v___x_4745_ = ((lean_object*)(l_Lean_Fmt_Layouts_binder___closed__0));
v_binderSignature_4746_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lhses_4736_, v_subBinderGroups_4737_, v_typeAscriptionTk_x3f_4738_, v_type_x3f_4739_, v_kind_4743_, v___x_4745_);
v___x_4747_ = 0;
v_simpleBinder_4748_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_binderSignature_4746_, v_colonEqTk_x3f_4740_, v_default_x3f_4741_, v___x_4747_);
v_rbs_4749_ = l_Lean_Fmt_Layouts_atomic(v_rbs_4742_);
v___x_4750_ = l_Lean_Fmt_Layouts_parens(v_lbs_4744_, v_simpleBinder_4748_, v_rbs_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder___boxed(lean_object* v_lbs_4751_, lean_object* v_lhses_4752_, lean_object* v_subBinderGroups_4753_, lean_object* v_typeAscriptionTk_x3f_4754_, lean_object* v_type_x3f_4755_, lean_object* v_colonEqTk_x3f_4756_, lean_object* v_default_x3f_4757_, lean_object* v_rbs_4758_, lean_object* v_kind_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_Lean_Fmt_Layouts_binder(v_lbs_4751_, v_lhses_4752_, v_subBinderGroups_4753_, v_typeAscriptionTk_x3f_4754_, v_type_x3f_4755_, v_colonEqTk_x3f_4756_, v_default_x3f_4757_, v_rbs_4758_, v_kind_4759_);
lean_dec(v_kind_4759_);
lean_dec_ref(v_rbs_4758_);
lean_dec_ref(v_subBinderGroups_4753_);
lean_dec_ref(v_lhses_4752_);
lean_dec_ref(v_lbs_4751_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object* v_keywordTk_4764_, lean_object* v_config_4765_, lean_object* v_decl_4766_, uint8_t v_format_4767_){
_start:
{
lean_object* v___f_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v_signature_4774_; lean_object* v___y_4776_; 
v___f_4768_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0));
v___x_4769_ = lean_unsigned_to_nat(2u);
v___x_4770_ = lean_mk_empty_array_with_capacity(v___x_4769_);
lean_inc_ref(v___x_4770_);
v___x_4771_ = lean_array_push(v___x_4770_, v_keywordTk_4764_);
v___x_4772_ = lean_array_push(v___x_4771_, v_config_4765_);
v___x_4773_ = ((lean_object*)(l_Lean_Fmt_Layouts_letDecl___closed__0));
v_signature_4774_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4772_, v___x_4773_);
if (v_format_4767_ == 0)
{
lean_object* v___x_4788_; 
v___x_4788_ = l_Lean_Fmt_TaggedDoc_space;
v___y_4776_ = v___x_4788_;
goto v___jp_4775_;
}
else
{
lean_object* v___x_4789_; 
v___x_4789_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4776_ = v___x_4789_;
goto v___jp_4775_;
}
v___jp_4775_:
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4777_, 0, v_signature_4774_);
lean_inc_ref(v___y_4776_);
v___x_4778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___y_4776_);
lean_ctor_set(v___x_4778_, 1, v___f_4768_);
v___x_4779_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4777_, v___x_4778_);
v___x_4780_ = lean_box(0);
v___x_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4781_, 0, v_decl_4766_);
v___x_4782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4780_);
lean_ctor_set(v___x_4782_, 1, v___x_4781_);
lean_ctor_set(v___x_4782_, 2, v___x_4780_);
v___x_4783_ = lean_array_push(v___x_4770_, v___x_4779_);
v___x_4784_ = lean_array_push(v___x_4783_, v___x_4782_);
v___x_4785_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4784_);
lean_dec_ref(v___x_4784_);
v___x_4786_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4785_);
v___x_4787_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4786_);
return v___x_4787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl___boxed(lean_object* v_keywordTk_4790_, lean_object* v_config_4791_, lean_object* v_decl_4792_, lean_object* v_format_4793_){
_start:
{
uint8_t v_format_boxed_4794_; lean_object* v_res_4795_; 
v_format_boxed_4794_ = lean_unbox(v_format_4793_);
v_res_4795_ = l_Lean_Fmt_Layouts_letDecl(v_keywordTk_4790_, v_config_4791_, v_decl_4792_, v_format_boxed_4794_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(size_t v_sz_4796_, size_t v_i_4797_, lean_object* v_bs_4798_){
_start:
{
uint8_t v___x_4799_; 
v___x_4799_ = lean_usize_dec_lt(v_i_4797_, v_sz_4796_);
if (v___x_4799_ == 0)
{
return v_bs_4798_;
}
else
{
lean_object* v_v_4800_; lean_object* v_quantifier_4801_; lean_object* v_binderGroups_4802_; lean_object* v_typeAscriptionTk_x3f_4803_; lean_object* v_type_x3f_4804_; lean_object* v_separationTk_4805_; lean_object* v___x_4806_; lean_object* v_bs_x27_4807_; lean_object* v___x_4808_; lean_object* v_signature_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; lean_object* v___x_4816_; size_t v___x_4817_; size_t v___x_4818_; lean_object* v___x_4819_; 
v_v_4800_ = lean_array_uget_borrowed(v_bs_4798_, v_i_4797_);
v_quantifier_4801_ = lean_ctor_get(v_v_4800_, 0);
lean_inc_ref(v_quantifier_4801_);
v_binderGroups_4802_ = lean_ctor_get(v_v_4800_, 1);
lean_inc_ref(v_binderGroups_4802_);
v_typeAscriptionTk_x3f_4803_ = lean_ctor_get(v_v_4800_, 2);
lean_inc_ref(v_typeAscriptionTk_x3f_4803_);
v_type_x3f_4804_ = lean_ctor_get(v_v_4800_, 3);
lean_inc_ref(v_type_x3f_4804_);
v_separationTk_4805_ = lean_ctor_get(v_v_4800_, 4);
lean_inc_ref(v_separationTk_4805_);
v___x_4806_ = lean_unsigned_to_nat(0u);
v_bs_x27_4807_ = lean_array_uset(v_bs_4798_, v_i_4797_, v___x_4806_);
v___x_4808_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v_signature_4809_ = l_Lean_Fmt_Layouts_localSignature(v___x_4808_, v_binderGroups_4802_, v_typeAscriptionTk_x3f_4803_, v_type_x3f_4804_);
lean_dec_ref(v_binderGroups_4802_);
v___x_4810_ = lean_unsigned_to_nat(2u);
v___x_4811_ = lean_mk_empty_array_with_capacity(v___x_4810_);
v___x_4812_ = lean_array_push(v___x_4811_, v_signature_4809_);
v___x_4813_ = lean_array_push(v___x_4812_, v_separationTk_4805_);
v___x_4814_ = l_Lean_Fmt_Layouts_atomic(v___x_4813_);
lean_dec_ref(v___x_4813_);
v___x_4815_ = 2;
v___x_4816_ = l_Lean_Fmt_Layouts_prefixOperator(v_quantifier_4801_, v___x_4814_, v___x_4815_);
v___x_4817_ = ((size_t)1ULL);
v___x_4818_ = lean_usize_add(v_i_4797_, v___x_4817_);
v___x_4819_ = lean_array_uset(v_bs_x27_4807_, v_i_4797_, v___x_4816_);
v_i_4797_ = v___x_4818_;
v_bs_4798_ = v___x_4819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0___boxed(lean_object* v_sz_4821_, lean_object* v_i_4822_, lean_object* v_bs_4823_){
_start:
{
size_t v_sz_boxed_4824_; size_t v_i_boxed_4825_; lean_object* v_res_4826_; 
v_sz_boxed_4824_ = lean_unbox_usize(v_sz_4821_);
lean_dec(v_sz_4821_);
v_i_boxed_4825_ = lean_unbox_usize(v_i_4822_);
lean_dec(v_i_4822_);
v_res_4826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_boxed_4824_, v_i_boxed_4825_, v_bs_4823_);
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(size_t v_sz_4827_, size_t v_i_4828_, lean_object* v_bs_4829_){
_start:
{
uint8_t v___x_4830_; 
v___x_4830_ = lean_usize_dec_lt(v_i_4828_, v_sz_4827_);
if (v___x_4830_ == 0)
{
return v_bs_4829_;
}
else
{
lean_object* v_v_4831_; lean_object* v___x_4832_; lean_object* v_bs_x27_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; size_t v___x_4836_; size_t v___x_4837_; lean_object* v___x_4838_; 
v_v_4831_ = lean_array_uget(v_bs_4829_, v_i_4828_);
v___x_4832_ = lean_unsigned_to_nat(0u);
v_bs_x27_4833_ = lean_array_uset(v_bs_4829_, v_i_4828_, v___x_4832_);
v___x_4834_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4831_);
v___x_4835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4835_, 0, v___x_4834_);
lean_ctor_set_uint8(v___x_4835_, sizeof(void*)*1, v___x_4830_);
v___x_4836_ = ((size_t)1ULL);
v___x_4837_ = lean_usize_add(v_i_4828_, v___x_4836_);
v___x_4838_ = lean_array_uset(v_bs_x27_4833_, v_i_4828_, v___x_4835_);
v_i_4828_ = v___x_4837_;
v_bs_4829_ = v___x_4838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1___boxed(lean_object* v_sz_4840_, lean_object* v_i_4841_, lean_object* v_bs_4842_){
_start:
{
size_t v_sz_boxed_4843_; size_t v_i_boxed_4844_; lean_object* v_res_4845_; 
v_sz_boxed_4843_ = lean_unbox_usize(v_sz_4840_);
lean_dec(v_sz_4840_);
v_i_boxed_4844_ = lean_unbox_usize(v_i_4841_);
lean_dec(v_i_4841_);
v_res_4845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_boxed_4843_, v_i_boxed_4844_, v_bs_4842_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_quantified(lean_object* v_quantifierHeads_4846_, lean_object* v_body_4847_){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; uint8_t v___x_4850_; 
v___x_4848_ = lean_array_get_size(v_quantifierHeads_4846_);
v___x_4849_ = lean_unsigned_to_nat(0u);
v___x_4850_ = lean_nat_dec_eq(v___x_4848_, v___x_4849_);
if (v___x_4850_ == 0)
{
size_t v_sz_4851_; size_t v___x_4852_; lean_object* v_quantifierHeads_4853_; size_t v_sz_4854_; lean_object* v_quantifierHeads_4855_; lean_object* v___x_4856_; lean_object* v_components_4857_; lean_object* v___x_4858_; lean_object* v_quantifiers_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v_sz_4851_ = lean_array_size(v_quantifierHeads_4846_);
v___x_4852_ = ((size_t)0ULL);
v_quantifierHeads_4853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_4851_, v___x_4852_, v_quantifierHeads_4846_);
v_sz_4854_ = lean_array_size(v_quantifierHeads_4853_);
v_quantifierHeads_4855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_4854_, v___x_4852_, v_quantifierHeads_4853_);
v___x_4856_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4856_, 0, v_body_4847_);
lean_ctor_set_uint8(v___x_4856_, sizeof(void*)*1, v___x_4850_);
v_components_4857_ = lean_array_push(v_quantifierHeads_4855_, v___x_4856_);
v___x_4858_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v_quantifiers_4859_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(v_components_4857_, v___x_4858_);
v___x_4860_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_quantifiers_4859_);
v___x_4861_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4860_, v___x_4850_);
return v___x_4861_;
}
else
{
lean_dec_ref(v_quantifierHeads_4846_);
return v_body_4847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_subtype(lean_object* v_lbTk_4865_, lean_object* v_lhs_4866_, lean_object* v_sepTk_4867_, lean_object* v_rhs_4868_, lean_object* v_rbTk_4869_, lean_object* v_format_4870_){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v_body_4879_; lean_object* v___x_4880_; 
v___x_4871_ = lean_unsigned_to_nat(3u);
v___x_4872_ = lean_mk_empty_array_with_capacity(v___x_4871_);
v___x_4873_ = lean_array_push(v___x_4872_, v_lhs_4866_);
v___x_4874_ = lean_array_push(v___x_4873_, v_sepTk_4867_);
v___x_4875_ = lean_array_push(v___x_4874_, v_rhs_4868_);
v___x_4876_ = 0;
v___x_4877_ = ((lean_object*)(l_Lean_Fmt_Layouts_subtype___closed__0));
v___x_4878_ = l_Lean_Fmt_Layouts_infixOperator(v___x_4875_, v___x_4877_);
v_body_4879_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4878_, v___x_4876_);
v___x_4880_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_4865_, v_body_4879_, v_rbTk_4869_, v_format_4870_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(lean_object* v_tk_4881_, lean_object* v_block_4882_, uint8_t v_allowFlattening_4883_){
_start:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4885_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_tk_4881_, v___x_4884_, v_block_4882_, v_allowFlattening_4883_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken___boxed(lean_object* v_tk_4886_, lean_object* v_block_4887_, lean_object* v_allowFlattening_4888_){
_start:
{
uint8_t v_allowFlattening_boxed_4889_; lean_object* v_res_4890_; 
v_allowFlattening_boxed_4889_ = lean_unbox(v_allowFlattening_4888_);
v_res_4890_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_tk_4886_, v_block_4887_, v_allowFlattening_boxed_4889_);
return v_res_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(uint8_t v_allowFlattening_4891_, size_t v_sz_4892_, size_t v_i_4893_, lean_object* v_bs_4894_){
_start:
{
uint8_t v___x_4895_; 
v___x_4895_ = lean_usize_dec_lt(v_i_4893_, v_sz_4892_);
if (v___x_4895_ == 0)
{
return v_bs_4894_;
}
else
{
lean_object* v_v_4896_; lean_object* v_elseTk_4897_; lean_object* v_ifTk_4898_; lean_object* v_cond_4899_; lean_object* v_thenTk_4900_; lean_object* v_thenBlock_4901_; lean_object* v___x_4902_; lean_object* v_bs_x27_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v_tk_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; uint8_t v___x_4911_; lean_object* v___x_4912_; lean_object* v_head_4913_; lean_object* v_then_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v_trailingThen_4924_; size_t v___x_4925_; size_t v___x_4926_; lean_object* v___x_4927_; 
v_v_4896_ = lean_array_uget_borrowed(v_bs_4894_, v_i_4893_);
v_elseTk_4897_ = lean_ctor_get(v_v_4896_, 0);
lean_inc_ref(v_elseTk_4897_);
v_ifTk_4898_ = lean_ctor_get(v_v_4896_, 1);
lean_inc_ref(v_ifTk_4898_);
v_cond_4899_ = lean_ctor_get(v_v_4896_, 2);
lean_inc_ref(v_cond_4899_);
v_thenTk_4900_ = lean_ctor_get(v_v_4896_, 3);
lean_inc_ref(v_thenTk_4900_);
v_thenBlock_4901_ = lean_ctor_get(v_v_4896_, 4);
lean_inc_ref(v_thenBlock_4901_);
v___x_4902_ = lean_unsigned_to_nat(0u);
v_bs_x27_4903_ = lean_array_uset(v_bs_4894_, v_i_4893_, v___x_4902_);
v___x_4904_ = lean_unsigned_to_nat(2u);
v___x_4905_ = lean_mk_empty_array_with_capacity(v___x_4904_);
lean_inc_ref_n(v___x_4905_, 2);
v___x_4906_ = lean_array_push(v___x_4905_, v_elseTk_4897_);
v___x_4907_ = lean_array_push(v___x_4906_, v_ifTk_4898_);
v_tk_4908_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4907_);
lean_dec_ref(v___x_4907_);
v___x_4909_ = lean_array_push(v___x_4905_, v_tk_4908_);
v___x_4910_ = lean_array_push(v___x_4909_, v_cond_4899_);
v___x_4911_ = 0;
v___x_4912_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4912_, 0, v___x_4895_);
lean_ctor_set_uint8(v___x_4912_, 1, v___x_4911_);
lean_ctor_set_uint8(v___x_4912_, 2, v___x_4911_);
lean_ctor_set_uint8(v___x_4912_, 3, v___x_4911_);
v_head_4913_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4910_, v___x_4912_);
v_then_4914_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_thenTk_4900_, v_thenBlock_4901_, v_allowFlattening_4891_);
v___x_4915_ = l_Lean_Fmt_TaggedDoc_hardNested(v_head_4913_);
v___x_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4915_);
v___x_4917_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4918_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4916_, v___x_4917_);
v___x_4919_ = lean_box(0);
v___x_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4920_, 0, v_then_4914_);
v___x_4921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4919_);
lean_ctor_set(v___x_4921_, 1, v___x_4920_);
lean_ctor_set(v___x_4921_, 2, v___x_4919_);
v___x_4922_ = lean_array_push(v___x_4905_, v___x_4918_);
v___x_4923_ = lean_array_push(v___x_4922_, v___x_4921_);
v_trailingThen_4924_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4923_);
lean_dec_ref(v___x_4923_);
v___x_4925_ = ((size_t)1ULL);
v___x_4926_ = lean_usize_add(v_i_4893_, v___x_4925_);
v___x_4927_ = lean_array_uset(v_bs_x27_4903_, v_i_4893_, v_trailingThen_4924_);
v_i_4893_ = v___x_4926_;
v_bs_4894_ = v___x_4927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0___boxed(lean_object* v_allowFlattening_4929_, lean_object* v_sz_4930_, lean_object* v_i_4931_, lean_object* v_bs_4932_){
_start:
{
uint8_t v_allowFlattening_boxed_4933_; size_t v_sz_boxed_4934_; size_t v_i_boxed_4935_; lean_object* v_res_4936_; 
v_allowFlattening_boxed_4933_ = lean_unbox(v_allowFlattening_4929_);
v_sz_boxed_4934_ = lean_unbox_usize(v_sz_4930_);
lean_dec(v_sz_4930_);
v_i_boxed_4935_ = lean_unbox_usize(v_i_4931_);
lean_dec(v_i_4931_);
v_res_4936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_boxed_4933_, v_sz_boxed_4934_, v_i_boxed_4935_, v_bs_4932_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(lean_object* v_elseIfs_4937_, lean_object* v_elseTk_4938_, lean_object* v_elseBlock_4939_, uint8_t v_allowFlattening_4940_){
_start:
{
size_t v_sz_4941_; size_t v___x_4942_; lean_object* v_elseIfs_4943_; lean_object* v_else_4944_; lean_object* v_blocks_4945_; size_t v_sz_4946_; lean_object* v_blocks_4947_; lean_object* v_conditional_4948_; lean_object* v___x_4949_; 
v_sz_4941_ = lean_array_size(v_elseIfs_4937_);
v___x_4942_ = ((size_t)0ULL);
v_elseIfs_4943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_4940_, v_sz_4941_, v___x_4942_, v_elseIfs_4937_);
v_else_4944_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_elseTk_4938_, v_elseBlock_4939_, v_allowFlattening_4940_);
v_blocks_4945_ = lean_array_push(v_elseIfs_4943_, v_else_4944_);
v_sz_4946_ = lean_array_size(v_blocks_4945_);
v_blocks_4947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_4946_, v___x_4942_, v_blocks_4945_);
v_conditional_4948_ = l_Lean_Fmt_TaggedDoc_combine(v_blocks_4947_);
lean_dec_ref(v_blocks_4947_);
v___x_4949_ = l_Lean_Fmt_TaggedDoc_aligned(v_conditional_4948_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk___boxed(lean_object* v_elseIfs_4950_, lean_object* v_elseTk_4951_, lean_object* v_elseBlock_4952_, lean_object* v_allowFlattening_4953_){
_start:
{
uint8_t v_allowFlattening_boxed_4954_; lean_object* v_res_4955_; 
v_allowFlattening_boxed_4954_ = lean_unbox(v_allowFlattening_4953_);
v_res_4955_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4950_, v_elseTk_4951_, v_elseBlock_4952_, v_allowFlattening_boxed_4954_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(lean_object* v_as_4956_, size_t v_i_4957_, size_t v_stop_4958_, lean_object* v_b_4959_){
_start:
{
lean_object* v___y_4961_; uint8_t v___x_4965_; 
v___x_4965_ = lean_usize_dec_eq(v_i_4957_, v_stop_4958_);
if (v___x_4965_ == 0)
{
lean_object* v___x_4966_; lean_object* v_elseTk_4967_; lean_object* v_ifTk_4968_; lean_object* v_cond_4969_; lean_object* v_thenTk_4970_; lean_object* v_thenBlock_4971_; uint8_t v___x_4972_; 
v___x_4966_ = lean_array_uget_borrowed(v_as_4956_, v_i_4957_);
v_elseTk_4967_ = lean_ctor_get(v___x_4966_, 0);
v_ifTk_4968_ = lean_ctor_get(v___x_4966_, 1);
v_cond_4969_ = lean_ctor_get(v___x_4966_, 2);
v_thenTk_4970_ = lean_ctor_get(v___x_4966_, 3);
v_thenBlock_4971_ = lean_ctor_get(v___x_4966_, 4);
v___x_4972_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_elseTk_4967_);
if (v___x_4972_ == 0)
{
lean_object* v___x_4973_; 
lean_inc(v___x_4966_);
v___x_4973_ = lean_array_push(v_b_4959_, v___x_4966_);
v___y_4961_ = v___x_4973_;
goto v___jp_4960_;
}
else
{
uint8_t v___x_4974_; 
v___x_4974_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_ifTk_4968_);
if (v___x_4974_ == 0)
{
lean_object* v___x_4975_; 
lean_inc(v___x_4966_);
v___x_4975_ = lean_array_push(v_b_4959_, v___x_4966_);
v___y_4961_ = v___x_4975_;
goto v___jp_4960_;
}
else
{
uint8_t v___x_4976_; 
v___x_4976_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_cond_4969_);
if (v___x_4976_ == 0)
{
lean_object* v___x_4977_; 
lean_inc(v___x_4966_);
v___x_4977_ = lean_array_push(v_b_4959_, v___x_4966_);
v___y_4961_ = v___x_4977_;
goto v___jp_4960_;
}
else
{
uint8_t v___x_4978_; 
v___x_4978_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenTk_4970_);
if (v___x_4978_ == 0)
{
lean_object* v___x_4979_; 
lean_inc(v___x_4966_);
v___x_4979_ = lean_array_push(v_b_4959_, v___x_4966_);
v___y_4961_ = v___x_4979_;
goto v___jp_4960_;
}
else
{
uint8_t v___x_4980_; 
v___x_4980_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenBlock_4971_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; 
lean_inc(v___x_4966_);
v___x_4981_ = lean_array_push(v_b_4959_, v___x_4966_);
v___y_4961_ = v___x_4981_;
goto v___jp_4960_;
}
else
{
v___y_4961_ = v_b_4959_;
goto v___jp_4960_;
}
}
}
}
}
}
else
{
return v_b_4959_;
}
v___jp_4960_:
{
size_t v___x_4962_; size_t v___x_4963_; 
v___x_4962_ = ((size_t)1ULL);
v___x_4963_ = lean_usize_add(v_i_4957_, v___x_4962_);
v_i_4957_ = v___x_4963_;
v_b_4959_ = v___y_4961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0___boxed(lean_object* v_as_4982_, lean_object* v_i_4983_, lean_object* v_stop_4984_, lean_object* v_b_4985_){
_start:
{
size_t v_i_boxed_4986_; size_t v_stop_boxed_4987_; lean_object* v_res_4988_; 
v_i_boxed_4986_ = lean_unbox_usize(v_i_4983_);
lean_dec(v_i_4983_);
v_stop_boxed_4987_ = lean_unbox_usize(v_stop_4984_);
lean_dec(v_stop_4984_);
v_res_4988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_as_4982_, v_i_boxed_4986_, v_stop_boxed_4987_, v_b_4985_);
lean_dec_ref(v_as_4982_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional(lean_object* v_ifTk_4991_, lean_object* v_cond_4992_, lean_object* v_thenTk_4993_, lean_object* v_thenBlock_4994_, lean_object* v_elseIfs_4995_, lean_object* v_elseTk_4996_, lean_object* v_elseBlock_4997_, uint8_t v_allowFlattening_4998_){
_start:
{
lean_object* v___y_5000_; uint8_t v___y_5001_; lean_object* v___y_5020_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; uint8_t v___x_5027_; 
v___x_5024_ = lean_unsigned_to_nat(0u);
v___x_5025_ = lean_array_get_size(v_elseIfs_4995_);
v___x_5026_ = ((lean_object*)(l_Lean_Fmt_Layouts_conditional___closed__0));
v___x_5027_ = lean_nat_dec_lt(v___x_5024_, v___x_5025_);
if (v___x_5027_ == 0)
{
v___y_5020_ = v___x_5026_;
goto v___jp_5019_;
}
else
{
size_t v___x_5028_; size_t v___x_5029_; lean_object* v___x_5030_; 
v___x_5028_ = ((size_t)0ULL);
v___x_5029_ = lean_usize_of_nat(v___x_5025_);
v___x_5030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_4995_, v___x_5028_, v___x_5029_, v___x_5026_);
v___y_5020_ = v___x_5030_;
goto v___jp_5019_;
}
v___jp_4999_:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v_elseIfs_5007_; 
v___x_5002_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5003_, 0, v___x_5002_);
lean_ctor_set(v___x_5003_, 1, v_ifTk_4991_);
lean_ctor_set(v___x_5003_, 2, v_cond_4992_);
lean_ctor_set(v___x_5003_, 3, v_thenTk_4993_);
lean_ctor_set(v___x_5003_, 4, v_thenBlock_4994_);
v___x_5004_ = lean_unsigned_to_nat(1u);
v___x_5005_ = lean_mk_empty_array_with_capacity(v___x_5004_);
v___x_5006_ = lean_array_push(v___x_5005_, v___x_5003_);
v_elseIfs_5007_ = l_Array_append___redArg(v___x_5006_, v___y_5000_);
lean_dec_ref(v___y_5000_);
if (v___y_5001_ == 0)
{
lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5007_, v_elseTk_4996_, v_elseBlock_4997_, v___y_5001_);
v___x_5009_ = l_Lean_Fmt_TaggedDoc_unflattenable(v___x_5008_);
return v___x_5009_;
}
else
{
lean_object* v___x_5010_; lean_object* v___x_5011_; uint8_t v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
lean_inc_ref(v_elseBlock_4997_);
lean_inc_ref(v_elseTk_4996_);
lean_inc_ref(v_elseIfs_5007_);
v___x_5010_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5007_, v_elseTk_4996_, v_elseBlock_4997_, v___y_5001_);
v___x_5011_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_5010_);
v___x_5012_ = 0;
v___x_5013_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5007_, v_elseTk_4996_, v_elseBlock_4997_, v___x_5012_);
v___x_5014_ = lean_unsigned_to_nat(2u);
v___x_5015_ = lean_mk_empty_array_with_capacity(v___x_5014_);
v___x_5016_ = lean_array_push(v___x_5015_, v___x_5011_);
v___x_5017_ = lean_array_push(v___x_5016_, v___x_5013_);
v___x_5018_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_5017_);
return v___x_5018_;
}
}
v___jp_5019_:
{
if (v_allowFlattening_4998_ == 0)
{
v___y_5000_ = v___y_5020_;
v___y_5001_ = v_allowFlattening_4998_;
goto v___jp_4999_;
}
else
{
lean_object* v___x_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
v___x_5021_ = lean_array_get_size(v___y_5020_);
v___x_5022_ = lean_unsigned_to_nat(0u);
v___x_5023_ = lean_nat_dec_eq(v___x_5021_, v___x_5022_);
v___y_5000_ = v___y_5020_;
v___y_5001_ = v___x_5023_;
goto v___jp_4999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional___boxed(lean_object* v_ifTk_5031_, lean_object* v_cond_5032_, lean_object* v_thenTk_5033_, lean_object* v_thenBlock_5034_, lean_object* v_elseIfs_5035_, lean_object* v_elseTk_5036_, lean_object* v_elseBlock_5037_, lean_object* v_allowFlattening_5038_){
_start:
{
uint8_t v_allowFlattening_boxed_5039_; lean_object* v_res_5040_; 
v_allowFlattening_boxed_5039_ = lean_unbox(v_allowFlattening_5038_);
v_res_5040_ = l_Lean_Fmt_Layouts_conditional(v_ifTk_5031_, v_cond_5032_, v_thenTk_5033_, v_thenBlock_5034_, v_elseIfs_5035_, v_elseTk_5036_, v_elseBlock_5037_, v_allowFlattening_boxed_5039_);
lean_dec_ref(v_elseIfs_5035_);
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_strLit(lean_object* v_prefix_5041_, lean_object* v_str_5042_){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; uint8_t v___x_5048_; lean_object* v___x_5049_; 
v___x_5043_ = lean_unsigned_to_nat(2u);
v___x_5044_ = lean_mk_empty_array_with_capacity(v___x_5043_);
v___x_5045_ = lean_array_push(v___x_5044_, v_prefix_5041_);
v___x_5046_ = lean_array_push(v___x_5045_, v_str_5042_);
v___x_5047_ = l_Lean_Fmt_Layouts_atomic(v___x_5046_);
lean_dec_ref(v___x_5046_);
v___x_5048_ = 0;
v___x_5049_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_5047_, v___x_5048_);
return v___x_5049_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Primitives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default = _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default();
lean_mark_persistent(l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default);
l_Lean_Fmt_Layouts_Types_instInhabitedBlock = _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock();
lean_mark_persistent(l_Lean_Fmt_Layouts_Types_instInhabitedBlock);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Primitives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Layouts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Layouts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Layouts(builtin);
}
#ifdef __cplusplus
}
#endif
