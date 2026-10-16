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
uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object*);
lean_object* l_Array_popWhile___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3;
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
static const lean_closure_object l_Lean_Fmt_Layouts_infixOperator___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_nested, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_infixOperator___closed__2 = (const lean_object*)&l_Lean_Fmt_Layouts_infixOperator___closed__2_value;
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
static const lean_ctor_object l_Lean_Fmt_Layouts_parens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5;
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
lean_object* v_d_1368_; lean_object* v___x_1369_; 
v_d_1368_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_d_1368_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1369_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1368_, v_a_1362_);
return v___x_1369_;
}
case 4:
{
lean_object* v_d_1370_; lean_object* v___x_1371_; 
v_d_1370_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1370_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1371_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1370_, v_a_1362_);
return v___x_1371_;
}
case 5:
{
lean_object* v_d_1372_; lean_object* v___x_1373_; 
v_d_1372_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1372_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1373_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1372_, v_a_1362_);
return v___x_1373_;
}
case 6:
{
lean_object* v_d_1374_; lean_object* v___x_1375_; 
v_d_1374_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_d_1374_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1375_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1374_, v_a_1362_);
return v___x_1375_;
}
case 7:
{
uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec_ref_known(v_a_1361_, 2);
v___x_1376_ = 1;
v___x_1377_ = lean_box(v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v_a_1362_);
return v___x_1378_;
}
case 8:
{
lean_object* v_d_1379_; lean_object* v___x_1380_; 
v_d_1379_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1379_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1380_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1379_, v_a_1362_);
return v___x_1380_;
}
case 9:
{
lean_object* v_d_1381_; lean_object* v___x_1382_; 
v_d_1381_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1381_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1382_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1381_, v_a_1362_);
return v___x_1382_;
}
case 10:
{
lean_object* v_d_1383_; lean_object* v___x_1384_; 
v_d_1383_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1383_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1384_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1383_, v_a_1362_);
return v___x_1384_;
}
case 11:
{
lean_object* v_d_1385_; lean_object* v___x_1386_; 
v_d_1385_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_d_1385_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1386_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1385_, v_a_1362_);
return v___x_1386_;
}
case 12:
{
lean_object* v_d_1387_; lean_object* v___x_1388_; 
v_d_1387_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_d_1387_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1388_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1387_, v_a_1362_);
return v___x_1388_;
}
case 13:
{
lean_object* v_d_1389_; lean_object* v___x_1390_; 
v_d_1389_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_d_1389_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1390_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1389_, v_a_1362_);
return v___x_1390_;
}
case 14:
{
lean_object* v_a_1391_; lean_object* v_b_1392_; lean_object* v___x_1393_; lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_a_1391_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_a_1391_);
v_b_1392_ = lean_ctor_get(v_a_1361_, 2);
lean_inc(v_b_1392_);
lean_dec_ref_known(v_a_1361_, 3);
v___x_1393_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_a_1391_, v_a_1362_);
v_fst_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_fst_1394_);
v_snd_1395_ = lean_ctor_get(v___x_1393_, 1);
lean_inc(v_snd_1395_);
lean_dec_ref(v___x_1393_);
v___x_1396_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_b_1392_, v_snd_1395_);
v___x_1397_ = lean_unbox(v_fst_1394_);
if (v___x_1397_ == 0)
{
lean_object* v_snd_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_snd_1398_ = lean_ctor_get(v___x_1396_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v___x_1396_, 0);
lean_dec(v_unused_1406_);
v___x_1400_ = v___x_1396_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snd_1398_);
lean_dec(v___x_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v_fst_1394_);
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_fst_1394_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_snd_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
else
{
lean_dec(v_fst_1394_);
return v___x_1396_;
}
}
default: 
{
uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec(v_a_1361_);
v___x_1407_ = 0;
v___x_1408_ = lean_box(v___x_1407_);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v_a_1362_);
return v___x_1409_;
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(lean_object* v_v_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_cacheKey_1412_; lean_object* v___x_1413_; 
lean_inc(v_v_1410_);
v_cacheKey_1412_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1410_);
v___x_1413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_a_1411_, v_cacheKey_1412_);
if (lean_obj_tag(v___x_1413_) == 1)
{
lean_object* v_val_1414_; lean_object* v___x_1415_; 
lean_dec_ref(v_cacheKey_1412_);
lean_dec(v_v_1410_);
v_val_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_val_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_val_1414_);
lean_ctor_set(v___x_1415_, 1, v_a_1411_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; lean_object* v_fst_1417_; lean_object* v_snd_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v___x_1413_);
v___x_1416_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_v_1410_, v_a_1411_);
v_fst_1417_ = lean_ctor_get(v___x_1416_, 0);
v_snd_1418_ = lean_ctor_get(v___x_1416_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1420_ = v___x_1416_;
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_snd_1418_);
lean_inc(v_fst_1417_);
lean_dec(v___x_1416_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_inc(v_fst_1417_);
v___x_1422_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_snd_1418_, v_cacheKey_1412_, v_fst_1417_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v___x_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_fst_1417_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go(lean_object* v_00_u03c4_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_a_1428_, v_a_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized(lean_object* v_00_u03c4_1431_, lean_object* v_v_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1432_, v_a_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(lean_object* v_00_u03c4_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_m_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1437_, v_a_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___boxed(lean_object* v_00_u03c4_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_m_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(v_00_u03c4_1440_, v_00_u03b2_1441_, v_m_1442_, v_a_1443_);
lean_dec_ref(v_a_1443_);
lean_dec_ref(v_m_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1(lean_object* v_00_u03c4_1445_, lean_object* v_00_u03b2_1446_, lean_object* v_m_1447_, lean_object* v_a_1448_, lean_object* v_b_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_m_1447_, v_a_1448_, v_b_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(lean_object* v_00_u03c4_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_a_1453_, lean_object* v_x_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1453_, v_x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___boxed(lean_object* v_00_u03c4_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_a_1458_, lean_object* v_x_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(v_00_u03c4_1456_, v_00_u03b2_1457_, v_a_1458_, v_x_1459_);
lean_dec(v_x_1459_);
lean_dec_ref(v_a_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(lean_object* v_00_u03c4_1461_, lean_object* v_00_u03b2_1462_, lean_object* v_a_1463_, lean_object* v_x_1464_){
_start:
{
uint8_t v___x_1465_; 
v___x_1465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1463_, v_x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___boxed(lean_object* v_00_u03c4_1466_, lean_object* v_00_u03b2_1467_, lean_object* v_a_1468_, lean_object* v_x_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(v_00_u03c4_1466_, v_00_u03b2_1467_, v_a_1468_, v_x_1469_);
lean_dec(v_x_1469_);
lean_dec_ref(v_a_1468_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4(lean_object* v_00_u03c4_1472_, lean_object* v_00_u03b2_1473_, lean_object* v_data_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_data_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5(lean_object* v_00_u03c4_1476_, lean_object* v_00_u03b2_1477_, lean_object* v_a_1478_, lean_object* v_b_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1478_, v_b_1479_, v_x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5(lean_object* v_00_u03c4_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_i_1484_, lean_object* v_source_1485_, lean_object* v_target_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v_i_1484_, v_source_1485_, v_target_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03c4_1488_, lean_object* v_00_u03b2_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_x_1490_, v_x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_isAligned___redArg___closed__0(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_unsigned_to_nat(16u);
v___x_1495_ = lean_mk_array(v___x_1494_, v___x_1493_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_isAligned___redArg___closed__1(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = lean_obj_once(&l_Lean_Fmt_Layouts_isAligned___redArg___closed__0, &l_Lean_Fmt_Layouts_isAligned___redArg___closed__0_once, _init_l_Lean_Fmt_Layouts_isAligned___redArg___closed__0);
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v___x_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_isAligned___redArg(lean_object* v_v_1499_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_fst_1502_; 
v___x_1500_ = lean_obj_once(&l_Lean_Fmt_Layouts_isAligned___redArg___closed__1, &l_Lean_Fmt_Layouts_isAligned___redArg___closed__1_once, _init_l_Lean_Fmt_Layouts_isAligned___redArg___closed__1);
v___x_1501_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1499_, v___x_1500_);
v_fst_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_fst_1502_);
lean_dec_ref(v___x_1501_);
return v_fst_1502_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_isAligned(lean_object* v_00_u03c4_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_v_1506_){
_start:
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = l_Lean_Fmt_Layouts_isAligned___redArg(v_v_1506_);
v___x_1508_ = lean_unbox(v___x_1507_);
lean_dec(v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_isAligned___boxed(lean_object* v_00_u03c4_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_v_1512_){
_start:
{
uint8_t v_res_1513_; lean_object* v_r_1514_; 
v_res_1513_ = l_Lean_Fmt_Layouts_isAligned(v_00_u03c4_1509_, v_inst_1510_, v_inst_1511_, v_v_1512_);
lean_dec_ref(v_inst_1511_);
lean_dec_ref(v_inst_1510_);
v_r_1514_ = lean_box(v_res_1513_);
return v_r_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___impl(uint8_t v_x_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_box(v_x_1515_);
v___x_1517_ = lean_obj_tag_nat(v___x_1516_);
lean_dec(v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___impl___boxed(lean_object* v_x_1518_){
_start:
{
uint8_t v_x_4__boxed_1519_; lean_object* v_res_1520_; 
v_x_4__boxed_1519_ = lean_unbox(v_x_1518_);
v_res_1520_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___impl(v_x_4__boxed_1519_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(lean_object* v_k_1521_){
_start:
{
lean_inc(v_k_1521_);
return v_k_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(v_k_1522_);
lean_dec(v_k_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(lean_object* v_motive_1524_, lean_object* v_ctorIdx_1525_, uint8_t v_t_1526_, lean_object* v_h_1527_, lean_object* v_k_1528_){
_start:
{
lean_inc(v_k_1528_);
return v_k_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1529_, lean_object* v_ctorIdx_1530_, lean_object* v_t_1531_, lean_object* v_h_1532_, lean_object* v_k_1533_){
_start:
{
uint8_t v_t_boxed_1534_; lean_object* v_res_1535_; 
v_t_boxed_1534_ = lean_unbox(v_t_1531_);
v_res_1535_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(v_motive_1529_, v_ctorIdx_1530_, v_t_boxed_1534_, v_h_1532_, v_k_1533_);
lean_dec(v_k_1533_);
lean_dec(v_ctorIdx_1530_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1536_){
_start:
{
lean_inc(v_withoutSpacing_1536_);
return v_withoutSpacing_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1537_);
lean_dec(v_withoutSpacing_1537_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1539_, uint8_t v_t_1540_, lean_object* v_h_1541_, lean_object* v_withoutSpacing_1542_){
_start:
{
lean_inc(v_withoutSpacing_1542_);
return v_withoutSpacing_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1543_, lean_object* v_t_1544_, lean_object* v_h_1545_, lean_object* v_withoutSpacing_1546_){
_start:
{
uint8_t v_t_boxed_1547_; lean_object* v_res_1548_; 
v_t_boxed_1547_ = lean_unbox(v_t_1544_);
v_res_1548_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(v_motive_1543_, v_t_boxed_1547_, v_h_1545_, v_withoutSpacing_1546_);
lean_dec(v_withoutSpacing_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(lean_object* v_withoutSpacingIfAtomic_1549_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1549_);
return v_withoutSpacingIfAtomic_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg___boxed(lean_object* v_withoutSpacingIfAtomic_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(v_withoutSpacingIfAtomic_1550_);
lean_dec(v_withoutSpacingIfAtomic_1550_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(lean_object* v_motive_1552_, uint8_t v_t_1553_, lean_object* v_h_1554_, lean_object* v_withoutSpacingIfAtomic_1555_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1555_);
return v_withoutSpacingIfAtomic_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___boxed(lean_object* v_motive_1556_, lean_object* v_t_1557_, lean_object* v_h_1558_, lean_object* v_withoutSpacingIfAtomic_1559_){
_start:
{
uint8_t v_t_boxed_1560_; lean_object* v_res_1561_; 
v_t_boxed_1560_ = lean_unbox(v_t_1557_);
v_res_1561_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(v_motive_1556_, v_t_boxed_1560_, v_h_1558_, v_withoutSpacingIfAtomic_1559_);
lean_dec(v_withoutSpacingIfAtomic_1559_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1562_){
_start:
{
lean_inc(v_withSpacing_1562_);
return v_withSpacing_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1563_);
lean_dec(v_withSpacing_1563_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(lean_object* v_motive_1565_, uint8_t v_t_1566_, lean_object* v_h_1567_, lean_object* v_withSpacing_1568_){
_start:
{
lean_inc(v_withSpacing_1568_);
return v_withSpacing_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1569_, lean_object* v_t_1570_, lean_object* v_h_1571_, lean_object* v_withSpacing_1572_){
_start:
{
uint8_t v_t_boxed_1573_; lean_object* v_res_1574_; 
v_t_boxed_1573_ = lean_unbox(v_t_1570_);
v_res_1574_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(v_motive_1569_, v_t_boxed_1573_, v_h_1571_, v_withSpacing_1572_);
lean_dec(v_withSpacing_1572_);
return v_res_1574_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_unsigned_to_nat(16u);
v___x_1577_ = lean_mk_array(v___x_1576_, v___x_1575_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_obj_once(&l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0, &l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once, _init_l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v___x_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object* v_v_1581_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_fst_1584_; uint8_t v___x_1585_; 
v___x_1582_ = lean_obj_once(&l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1, &l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once, _init_l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1);
v___x_1583_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1581_, v___x_1582_);
v_fst_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_fst_1584_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = lean_unbox(v_fst_1584_);
lean_dec(v_fst_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object* v_v_1586_){
_start:
{
uint8_t v_res_1587_; lean_object* v_r_1588_; 
v_res_1587_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_v_1586_);
v_r_1588_ = lean_box(v_res_1587_);
return v_r_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object* v_prefixOperatorTk_1589_, lean_object* v_operand_1590_, uint8_t v_format_1591_){
_start:
{
uint8_t v___x_1592_; lean_object* v___y_1594_; 
v___x_1592_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_prefixOperatorTk_1589_);
if (v___x_1592_ == 0)
{
if (v_format_1591_ == 0)
{
goto v___jp_1598_;
}
else
{
if (v_format_1591_ == 1)
{
uint8_t v___x_1614_; 
v___x_1614_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_operand_1590_);
if (v___x_1614_ == 0)
{
uint8_t v___x_1615_; 
lean_inc_ref(v_operand_1590_);
v___x_1615_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_operand_1590_);
if (v___x_1615_ == 0)
{
goto v___jp_1605_;
}
else
{
goto v___jp_1612_;
}
}
else
{
goto v___jp_1612_;
}
}
else
{
goto v___jp_1605_;
}
}
}
else
{
lean_dec_ref(v_prefixOperatorTk_1589_);
return v_operand_1590_;
}
v___jp_1593_:
{
lean_object* v_doc_1595_; uint8_t v___x_1596_; 
v_doc_1595_ = lean_ctor_get(v_operand_1590_, 0);
lean_inc(v_doc_1595_);
lean_dec_ref(v_operand_1590_);
v___x_1596_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1595_);
if (v___x_1596_ == 0)
{
return v___y_1594_;
}
else
{
lean_object* v_doc_1597_; 
v_doc_1597_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___y_1594_, v___x_1592_);
return v_doc_1597_;
}
}
v___jp_1598_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = lean_unsigned_to_nat(2u);
v___x_1600_ = lean_mk_empty_array_with_capacity(v___x_1599_);
v___x_1601_ = lean_array_push(v___x_1600_, v_prefixOperatorTk_1589_);
lean_inc_ref(v_operand_1590_);
v___x_1602_ = lean_array_push(v___x_1601_, v_operand_1590_);
v___x_1603_ = l_Lean_Fmt_Layouts_atomic(v___x_1602_);
lean_dec_ref(v___x_1602_);
v___x_1604_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1603_);
v___y_1594_ = v___x_1604_;
goto v___jp_1593_;
}
v___jp_1605_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1606_ = lean_unsigned_to_nat(2u);
v___x_1607_ = lean_mk_empty_array_with_capacity(v___x_1606_);
v___x_1608_ = lean_array_push(v___x_1607_, v_prefixOperatorTk_1589_);
lean_inc_ref(v_operand_1590_);
v___x_1609_ = lean_array_push(v___x_1608_, v_operand_1590_);
v___x_1610_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1609_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1610_);
v___y_1594_ = v___x_1611_;
goto v___jp_1593_;
}
v___jp_1612_:
{
uint8_t v___x_1613_; 
lean_inc_ref(v_operand_1590_);
v___x_1613_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_operand_1590_);
if (v___x_1613_ == 0)
{
goto v___jp_1598_;
}
else
{
goto v___jp_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator___boxed(lean_object* v_prefixOperatorTk_1616_, lean_object* v_operand_1617_, lean_object* v_format_1618_){
_start:
{
uint8_t v_format_boxed_1619_; lean_object* v_res_1620_; 
v_format_boxed_1619_ = lean_unbox(v_format_1618_);
v_res_1620_ = l_Lean_Fmt_Layouts_prefixOperator(v_prefixOperatorTk_1616_, v_operand_1617_, v_format_boxed_1619_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___impl(uint8_t v_x_1621_){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_box(v_x_1621_);
v___x_1623_ = lean_obj_tag_nat(v___x_1622_);
lean_dec(v___x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___impl___boxed(lean_object* v_x_1624_){
_start:
{
uint8_t v_x_4__boxed_1625_; lean_object* v_res_1626_; 
v_x_4__boxed_1625_ = lean_unbox(v_x_1624_);
v_res_1626_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___impl(v_x_4__boxed_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(lean_object* v_k_1627_){
_start:
{
lean_inc(v_k_1627_);
return v_k_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(v_k_1628_);
lean_dec(v_k_1628_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(lean_object* v_motive_1630_, lean_object* v_ctorIdx_1631_, uint8_t v_t_1632_, lean_object* v_h_1633_, lean_object* v_k_1634_){
_start:
{
lean_inc(v_k_1634_);
return v_k_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1635_, lean_object* v_ctorIdx_1636_, lean_object* v_t_1637_, lean_object* v_h_1638_, lean_object* v_k_1639_){
_start:
{
uint8_t v_t_boxed_1640_; lean_object* v_res_1641_; 
v_t_boxed_1640_ = lean_unbox(v_t_1637_);
v_res_1641_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(v_motive_1635_, v_ctorIdx_1636_, v_t_boxed_1640_, v_h_1638_, v_k_1639_);
lean_dec(v_k_1639_);
lean_dec(v_ctorIdx_1636_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1642_){
_start:
{
lean_inc(v_withoutSpacing_1642_);
return v_withoutSpacing_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1643_);
lean_dec(v_withoutSpacing_1643_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1645_, uint8_t v_t_1646_, lean_object* v_h_1647_, lean_object* v_withoutSpacing_1648_){
_start:
{
lean_inc(v_withoutSpacing_1648_);
return v_withoutSpacing_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1649_, lean_object* v_t_1650_, lean_object* v_h_1651_, lean_object* v_withoutSpacing_1652_){
_start:
{
uint8_t v_t_boxed_1653_; lean_object* v_res_1654_; 
v_t_boxed_1653_ = lean_unbox(v_t_1650_);
v_res_1654_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(v_motive_1649_, v_t_boxed_1653_, v_h_1651_, v_withoutSpacing_1652_);
lean_dec(v_withoutSpacing_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1655_){
_start:
{
lean_inc(v_withSpacing_1655_);
return v_withSpacing_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1656_);
lean_dec(v_withSpacing_1656_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(lean_object* v_motive_1658_, uint8_t v_t_1659_, lean_object* v_h_1660_, lean_object* v_withSpacing_1661_){
_start:
{
lean_inc(v_withSpacing_1661_);
return v_withSpacing_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1662_, lean_object* v_t_1663_, lean_object* v_h_1664_, lean_object* v_withSpacing_1665_){
_start:
{
uint8_t v_t_boxed_1666_; lean_object* v_res_1667_; 
v_t_boxed_1666_ = lean_unbox(v_t_1663_);
v_res_1667_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(v_motive_1662_, v_t_boxed_1666_, v_h_1664_, v_withSpacing_1665_);
lean_dec(v_withSpacing_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object* v_operand_1668_, lean_object* v_postfixOperatorTk_1669_, uint8_t v_format_1670_){
_start:
{
uint8_t v___x_1671_; 
v___x_1671_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_postfixOperatorTk_1669_);
if (v___x_1671_ == 0)
{
if (v_format_1670_ == 1)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1672_ = lean_unsigned_to_nat(2u);
v___x_1673_ = lean_mk_empty_array_with_capacity(v___x_1672_);
v___x_1674_ = lean_array_push(v___x_1673_, v_operand_1668_);
v___x_1675_ = lean_array_push(v___x_1674_, v_postfixOperatorTk_1669_);
v___x_1676_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1675_);
lean_dec_ref(v___x_1675_);
v___x_1677_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1676_);
return v___x_1677_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1678_ = lean_unsigned_to_nat(2u);
v___x_1679_ = lean_mk_empty_array_with_capacity(v___x_1678_);
v___x_1680_ = lean_array_push(v___x_1679_, v_operand_1668_);
v___x_1681_ = lean_array_push(v___x_1680_, v_postfixOperatorTk_1669_);
v___x_1682_ = l_Lean_Fmt_Layouts_atomic(v___x_1681_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1682_);
return v___x_1683_;
}
}
else
{
lean_dec_ref(v_postfixOperatorTk_1669_);
return v_operand_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator___boxed(lean_object* v_operand_1684_, lean_object* v_postfixOperatorTk_1685_, lean_object* v_format_1686_){
_start:
{
uint8_t v_format_boxed_1687_; lean_object* v_res_1688_; 
v_format_boxed_1687_ = lean_unbox(v_format_1686_);
v_res_1688_ = l_Lean_Fmt_Layouts_postfixOperator(v_operand_1684_, v_postfixOperatorTk_1685_, v_format_boxed_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___impl(lean_object* v_x_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_obj_tag_nat(v_x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___impl___boxed(lean_object* v_x_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___impl(v_x_1691_);
lean_dec_ref(v_x_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(lean_object* v_t_1693_, lean_object* v_k_1694_){
_start:
{
if (lean_obj_tag(v_t_1693_) == 0)
{
uint8_t v_hardNestedFirstOperand_1695_; uint8_t v_trailingOperator_1696_; uint8_t v_spacing_1697_; uint8_t v_respectPseudoAlignment_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_hardNestedFirstOperand_1695_ = lean_ctor_get_uint8(v_t_1693_, 0);
v_trailingOperator_1696_ = lean_ctor_get_uint8(v_t_1693_, 1);
v_spacing_1697_ = lean_ctor_get_uint8(v_t_1693_, 2);
v_respectPseudoAlignment_1698_ = lean_ctor_get_uint8(v_t_1693_, 3);
v___x_1699_ = lean_box(v_hardNestedFirstOperand_1695_);
v___x_1700_ = lean_box(v_trailingOperator_1696_);
v___x_1701_ = lean_box(v_spacing_1697_);
v___x_1702_ = lean_box(v_respectPseudoAlignment_1698_);
v___x_1703_ = lean_apply_4(v_k_1694_, v___x_1699_, v___x_1700_, v___x_1701_, v___x_1702_);
return v___x_1703_;
}
else
{
uint8_t v_hardNestedFirstOperand_1704_; uint8_t v_trailingOperator_1705_; uint8_t v_spacing_1706_; uint8_t v_alignedOperators_1707_; uint8_t v_separateFinalOperand_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_hardNestedFirstOperand_1704_ = lean_ctor_get_uint8(v_t_1693_, 0);
v_trailingOperator_1705_ = lean_ctor_get_uint8(v_t_1693_, 1);
v_spacing_1706_ = lean_ctor_get_uint8(v_t_1693_, 2);
v_alignedOperators_1707_ = lean_ctor_get_uint8(v_t_1693_, 3);
v_separateFinalOperand_1708_ = lean_ctor_get_uint8(v_t_1693_, 4);
v___x_1709_ = lean_box(v_hardNestedFirstOperand_1704_);
v___x_1710_ = lean_box(v_trailingOperator_1705_);
v___x_1711_ = lean_box(v_spacing_1706_);
v___x_1712_ = lean_box(v_alignedOperators_1707_);
v___x_1713_ = lean_box(v_separateFinalOperand_1708_);
v___x_1714_ = lean_apply_5(v_k_1694_, v___x_1709_, v___x_1710_, v___x_1711_, v___x_1712_, v___x_1713_);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_t_1715_, lean_object* v_k_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1715_, v_k_1716_);
lean_dec_ref(v_t_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(lean_object* v_motive_1718_, lean_object* v_ctorIdx_1719_, lean_object* v_t_1720_, lean_object* v_h_1721_, lean_object* v_k_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1720_, v_k_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1724_, lean_object* v_ctorIdx_1725_, lean_object* v_t_1726_, lean_object* v_h_1727_, lean_object* v_k_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(v_motive_1724_, v_ctorIdx_1725_, v_t_1726_, v_h_1727_, v_k_1728_);
lean_dec_ref(v_t_1726_);
lean_dec(v_ctorIdx_1725_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(lean_object* v_t_1730_, lean_object* v_dense_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1730_, v_dense_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg___boxed(lean_object* v_t_1733_, lean_object* v_dense_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(v_t_1733_, v_dense_1734_);
lean_dec_ref(v_t_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(lean_object* v_motive_1736_, lean_object* v_t_1737_, lean_object* v_h_1738_, lean_object* v_dense_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1737_, v_dense_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___boxed(lean_object* v_motive_1741_, lean_object* v_t_1742_, lean_object* v_h_1743_, lean_object* v_dense_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(v_motive_1741_, v_t_1742_, v_h_1743_, v_dense_1744_);
lean_dec_ref(v_t_1742_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(lean_object* v_t_1746_, lean_object* v_sparse_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1746_, v_sparse_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg___boxed(lean_object* v_t_1749_, lean_object* v_sparse_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(v_t_1749_, v_sparse_1750_);
lean_dec_ref(v_t_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(lean_object* v_motive_1752_, lean_object* v_t_1753_, lean_object* v_h_1754_, lean_object* v_sparse_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1753_, v_sparse_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___boxed(lean_object* v_motive_1757_, lean_object* v_t_1758_, lean_object* v_h_1759_, lean_object* v_sparse_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(v_motive_1757_, v_t_1758_, v_h_1759_, v_sparse_1760_);
lean_dec_ref(v_t_1758_);
return v_res_1761_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(lean_object* v_x_1762_){
_start:
{
uint8_t v_hardNestedFirstOperand_1763_; 
v_hardNestedFirstOperand_1763_ = lean_ctor_get_uint8(v_x_1762_, 0);
return v_hardNestedFirstOperand_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand___boxed(lean_object* v_x_1764_){
_start:
{
uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_res_1765_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(v_x_1764_);
lean_dec_ref(v_x_1764_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(lean_object* v_x_1767_){
_start:
{
uint8_t v_trailingOperator_1768_; 
v_trailingOperator_1768_ = lean_ctor_get_uint8(v_x_1767_, 1);
return v_trailingOperator_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator___boxed(lean_object* v_x_1769_){
_start:
{
uint8_t v_res_1770_; lean_object* v_r_1771_; 
v_res_1770_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(v_x_1769_);
lean_dec_ref(v_x_1769_);
v_r_1771_ = lean_box(v_res_1770_);
return v_r_1771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(lean_object* v_x_1772_){
_start:
{
uint8_t v_spacing_1773_; 
v_spacing_1773_ = lean_ctor_get_uint8(v_x_1772_, 2);
return v_spacing_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing___boxed(lean_object* v_x_1774_){
_start:
{
uint8_t v_res_1775_; lean_object* v_r_1776_; 
v_res_1775_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(v_x_1774_);
lean_dec_ref(v_x_1774_);
v_r_1776_ = lean_box(v_res_1775_);
return v_r_1776_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(lean_object* v_x_1777_){
_start:
{
if (lean_obj_tag(v_x_1777_) == 0)
{
uint8_t v___x_1778_; 
v___x_1778_ = 0;
return v___x_1778_;
}
else
{
uint8_t v_trailingOperator_1779_; 
v_trailingOperator_1779_ = lean_ctor_get_uint8(v_x_1777_, 1);
if (v_trailingOperator_1779_ == 0)
{
uint8_t v_alignedOperators_1780_; 
v_alignedOperators_1780_ = lean_ctor_get_uint8(v_x_1777_, 3);
return v_alignedOperators_1780_;
}
else
{
uint8_t v___x_1781_; 
v___x_1781_ = 0;
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators___boxed(lean_object* v_x_1782_){
_start:
{
uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_res_1783_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_x_1782_);
lean_dec_ref(v_x_1782_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(lean_object* v_x_1785_){
_start:
{
if (lean_obj_tag(v_x_1785_) == 0)
{
uint8_t v___x_1786_; 
v___x_1786_ = 0;
return v___x_1786_;
}
else
{
uint8_t v_trailingOperator_1787_; 
v_trailingOperator_1787_ = lean_ctor_get_uint8(v_x_1785_, 1);
if (v_trailingOperator_1787_ == 0)
{
uint8_t v_separateFinalOperand_1788_; 
v_separateFinalOperand_1788_ = lean_ctor_get_uint8(v_x_1785_, 4);
return v_separateFinalOperand_1788_;
}
else
{
uint8_t v___x_1789_; 
v___x_1789_ = 0;
return v___x_1789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand___boxed(lean_object* v_x_1790_){
_start:
{
uint8_t v_res_1791_; lean_object* v_r_1792_; 
v_res_1791_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_x_1790_);
lean_dec_ref(v_x_1790_);
v_r_1792_ = lean_box(v_res_1791_);
return v_r_1792_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(lean_object* v_x_1793_){
_start:
{
if (lean_obj_tag(v_x_1793_) == 0)
{
uint8_t v_respectPseudoAlignment_1794_; 
v_respectPseudoAlignment_1794_ = lean_ctor_get_uint8(v_x_1793_, 3);
return v_respectPseudoAlignment_1794_;
}
else
{
uint8_t v___x_1795_; 
v___x_1795_ = 1;
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment___boxed(lean_object* v_x_1796_){
_start:
{
uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_res_1797_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(v_x_1796_);
lean_dec_ref(v_x_1796_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_permitDenseLayout(lean_object* v_doc_1799_, uint8_t v_respectPseudoAlignment_1800_){
_start:
{
lean_object* v_pseudoAligned_x3f_1805_; 
lean_inc_ref(v_doc_1799_);
v_pseudoAligned_x3f_1805_ = l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(v_doc_1799_);
if (v_respectPseudoAlignment_1800_ == 0)
{
if (lean_obj_tag(v_pseudoAligned_x3f_1805_) == 0)
{
goto v___jp_1801_;
}
else
{
lean_object* v_val_1806_; uint8_t v___x_1807_; 
v_val_1806_ = lean_ctor_get(v_pseudoAligned_x3f_1805_, 0);
lean_inc(v_val_1806_);
lean_dec_ref_known(v_pseudoAligned_x3f_1805_, 1);
v___x_1807_ = lean_unbox(v_val_1806_);
lean_dec(v_val_1806_);
if (v___x_1807_ == 0)
{
goto v___jp_1801_;
}
else
{
lean_dec_ref(v_doc_1799_);
return v_respectPseudoAlignment_1800_;
}
}
}
else
{
if (lean_obj_tag(v_pseudoAligned_x3f_1805_) == 0)
{
lean_object* v_doc_1808_; uint8_t v___x_1809_; 
v_doc_1808_ = lean_ctor_get(v_doc_1799_, 0);
lean_inc(v_doc_1808_);
lean_dec_ref(v_doc_1799_);
v___x_1809_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1808_);
if (v___x_1809_ == 0)
{
return v_respectPseudoAlignment_1800_;
}
else
{
uint8_t v___x_1810_; 
v___x_1810_ = 0;
return v___x_1810_;
}
}
else
{
uint8_t v___x_1811_; 
lean_dec_ref_known(v_pseudoAligned_x3f_1805_, 1);
lean_dec_ref(v_doc_1799_);
v___x_1811_ = 0;
return v___x_1811_;
}
}
v___jp_1801_:
{
lean_object* v_doc_1802_; uint8_t v___x_1803_; 
v_doc_1802_ = lean_ctor_get(v_doc_1799_, 0);
lean_inc(v_doc_1802_);
lean_dec_ref(v_doc_1799_);
v___x_1803_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1802_);
if (v___x_1803_ == 0)
{
uint8_t v___x_1804_; 
v___x_1804_ = 1;
return v___x_1804_;
}
else
{
return v_respectPseudoAlignment_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_permitDenseLayout___boxed(lean_object* v_doc_1812_, lean_object* v_respectPseudoAlignment_1813_){
_start:
{
uint8_t v_respectPseudoAlignment_boxed_1814_; uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_respectPseudoAlignment_boxed_1814_ = lean_unbox(v_respectPseudoAlignment_1813_);
v_res_1815_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_doc_1812_, v_respectPseudoAlignment_boxed_1814_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object* v_format_1817_, lean_object* v_docs_1818_){
_start:
{
uint8_t v___y_1820_; uint8_t v_spacing_1823_; 
v_spacing_1823_ = lean_ctor_get_uint8(v_format_1817_, 2);
v___y_1820_ = v_spacing_1823_;
goto v___jp_1819_;
v___jp_1819_:
{
if (v___y_1820_ == 0)
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Fmt_Layouts_atomic(v_docs_1818_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_Fmt_Layouts_spacedAtomic(v_docs_1818_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object* v_format_1824_, lean_object* v_docs_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1824_, v_docs_1825_);
lean_dec_ref(v_docs_1825_);
lean_dec_ref(v_format_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object* v_msg_1827_){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_1829_ = lean_panic_fn_borrowed(v___x_1828_, v_msg_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t v_a_1830_, lean_object* v_as_1831_, size_t v_i_1832_, size_t v_stop_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_usize_dec_eq(v_i_1832_, v_stop_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; uint8_t v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_array_uget_borrowed(v_as_1831_, v_i_1832_);
v___x_1836_ = lean_unbox(v___x_1835_);
v___x_1837_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_a_1830_, v___x_1836_);
if (v___x_1837_ == 0)
{
size_t v___x_1838_; size_t v___x_1839_; 
v___x_1838_ = ((size_t)1ULL);
v___x_1839_ = lean_usize_add(v_i_1832_, v___x_1838_);
v_i_1832_ = v___x_1839_;
goto _start;
}
else
{
return v___x_1837_;
}
}
else
{
uint8_t v___x_1841_; 
v___x_1841_ = 0;
return v___x_1841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object* v_a_1842_, lean_object* v_as_1843_, lean_object* v_i_1844_, lean_object* v_stop_1845_){
_start:
{
uint8_t v_a_boxed_1846_; size_t v_i_boxed_1847_; size_t v_stop_boxed_1848_; uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_a_boxed_1846_ = lean_unbox(v_a_1842_);
v_i_boxed_1847_ = lean_unbox_usize(v_i_1844_);
lean_dec(v_i_1844_);
v_stop_boxed_1848_ = lean_unbox_usize(v_stop_1845_);
lean_dec(v_stop_1845_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_boxed_1846_, v_as_1843_, v_i_boxed_1847_, v_stop_boxed_1848_);
lean_dec_ref(v_as_1843_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object* v_as_1851_, uint8_t v_a_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = lean_array_get_size(v_as_1851_);
v___x_1855_ = lean_nat_dec_lt(v___x_1853_, v___x_1854_);
if (v___x_1855_ == 0)
{
return v___x_1855_;
}
else
{
size_t v___x_1856_; size_t v___x_1857_; uint8_t v___x_1858_; 
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = lean_usize_of_nat(v___x_1854_);
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_1852_, v_as_1851_, v___x_1856_, v___x_1857_);
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object* v_as_1859_, lean_object* v_a_1860_){
_start:
{
uint8_t v_a_boxed_1861_; uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_a_boxed_1861_ = lean_unbox(v_a_1860_);
v_res_1862_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_as_1859_, v_a_boxed_1861_);
lean_dec_ref(v_as_1859_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1867_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2));
v___x_1868_ = lean_unsigned_to_nat(14u);
v___x_1869_ = lean_unsigned_to_nat(22u);
v___x_1870_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1));
v___x_1871_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_1872_ = l_mkPanicMessageWithDecl(v___x_1871_, v___x_1870_, v___x_1869_, v___x_1868_, v___x_1867_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(lean_object* v_format_1873_, lean_object* v_doc_1874_, lean_object* v_lastOperand_1875_, uint8_t v_isTailless_1876_, lean_object* v_combinedChain_1877_, lean_object* v_eligibleKinds_1878_){
_start:
{
lean_object* v___x_1879_; uint8_t v___y_1881_; lean_object* v___y_1882_; uint8_t v___y_1903_; uint8_t v_trailingOperator_1916_; 
v___x_1879_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_1916_ = lean_ctor_get_uint8(v_format_1873_, 1);
v___y_1903_ = v_trailingOperator_1916_;
goto v___jp_1902_;
v___jp_1880_:
{
lean_object* v_stickyVariant_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_stickyVariant_1883_ = lean_ctor_get(v___y_1882_, 0);
v___x_1884_ = lean_array_get_size(v_combinedChain_1877_);
v___x_1885_ = lean_unsigned_to_nat(1u);
v___x_1886_ = lean_nat_sub(v___x_1884_, v___x_1885_);
lean_inc_ref(v_stickyVariant_1883_);
v___x_1887_ = lean_array_set(v_combinedChain_1877_, v___x_1886_, v_stickyVariant_1883_);
lean_dec(v___x_1886_);
lean_inc_ref(v___x_1887_);
v___x_1888_ = lean_array_pop(v___x_1887_);
v___x_1889_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1873_, v___x_1888_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1889_);
v___x_1891_ = lean_array_get_size(v___x_1887_);
v___x_1892_ = lean_nat_sub(v___x_1891_, v___x_1885_);
v___x_1893_ = lean_array_get(v___x_1879_, v___x_1887_, v___x_1892_);
lean_dec(v___x_1892_);
lean_dec_ref(v___x_1887_);
v___x_1894_ = lean_unsigned_to_nat(2u);
v___x_1895_ = lean_mk_empty_array_with_capacity(v___x_1894_);
v___x_1896_ = lean_array_push(v___x_1895_, v___x_1890_);
v___x_1897_ = lean_array_push(v___x_1896_, v___x_1893_);
v___x_1898_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1873_, v___x_1897_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_1882_, v___y_1881_);
lean_dec_ref(v___y_1882_);
v___x_1900_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1874_, v___x_1898_, v___x_1899_);
lean_dec(v___x_1899_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
v___jp_1902_:
{
if (v___y_1903_ == 0)
{
lean_object* v___x_1904_; 
lean_dec_ref(v_combinedChain_1877_);
lean_dec_ref(v_lastOperand_1875_);
lean_dec_ref(v_doc_1874_);
v___x_1904_ = lean_box(0);
return v___x_1904_;
}
else
{
if (v_isTailless_1876_ == 0)
{
lean_object* v___x_1905_; 
lean_inc_ref(v_lastOperand_1875_);
v___x_1905_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v_lastOperand_1875_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v___x_1906_; 
lean_dec_ref(v_combinedChain_1877_);
lean_dec_ref(v_lastOperand_1875_);
lean_dec_ref(v_doc_1874_);
v___x_1906_ = lean_box(0);
return v___x_1906_;
}
else
{
lean_object* v_val_1907_; uint8_t v___x_1908_; uint8_t v___x_1909_; 
v_val_1907_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_val_1907_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1908_ = lean_unbox(v_val_1907_);
lean_dec(v_val_1907_);
v___x_1909_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_1878_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; 
lean_dec_ref(v_combinedChain_1877_);
lean_dec_ref(v_lastOperand_1875_);
lean_dec_ref(v_doc_1874_);
v___x_1910_ = lean_box(0);
return v___x_1910_;
}
else
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_lastOperand_1875_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_1913_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_1912_);
v___y_1881_ = v___x_1909_;
v___y_1882_ = v___x_1913_;
goto v___jp_1880_;
}
else
{
lean_object* v_val_1914_; 
v_val_1914_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_val_1914_);
lean_dec_ref_known(v___x_1911_, 1);
v___y_1881_ = v___x_1909_;
v___y_1882_ = v_val_1914_;
goto v___jp_1880_;
}
}
}
}
else
{
lean_object* v___x_1915_; 
lean_dec_ref(v_combinedChain_1877_);
lean_dec_ref(v_lastOperand_1875_);
lean_dec_ref(v_doc_1874_);
v___x_1915_ = lean_box(0);
return v___x_1915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___boxed(lean_object* v_format_1917_, lean_object* v_doc_1918_, lean_object* v_lastOperand_1919_, lean_object* v_isTailless_1920_, lean_object* v_combinedChain_1921_, lean_object* v_eligibleKinds_1922_){
_start:
{
uint8_t v_isTailless_boxed_1923_; lean_object* v_res_1924_; 
v_isTailless_boxed_1923_ = lean_unbox(v_isTailless_1920_);
v_res_1924_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_1917_, v_doc_1918_, v_lastOperand_1919_, v_isTailless_boxed_1923_, v_combinedChain_1921_, v_eligibleKinds_1922_);
lean_dec_ref(v_eligibleKinds_1922_);
lean_dec_ref(v_format_1917_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(lean_object* v_format_1925_, lean_object* v_doc_1926_, lean_object* v_lastOperand_1927_, uint8_t v_isTailless_1928_, lean_object* v_combinedChain_1929_){
_start:
{
if (lean_obj_tag(v_format_1925_) == 0)
{
if (v_isTailless_1928_ == 0)
{
uint8_t v_trailingOperator_1930_; lean_object* v___x_1931_; 
v_trailingOperator_1930_ = lean_ctor_get_uint8(v_format_1925_, 1);
v___x_1931_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (v_trailingOperator_1930_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = lean_array_get_size(v_combinedChain_1929_);
v___x_1951_ = lean_unsigned_to_nat(2u);
v___x_1952_ = lean_nat_dec_eq(v___x_1950_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; 
lean_dec_ref(v_combinedChain_1929_);
lean_dec_ref(v_lastOperand_1927_);
lean_dec_ref(v_doc_1926_);
v___x_1953_ = lean_box(0);
return v___x_1953_;
}
else
{
goto v___jp_1932_;
}
}
else
{
goto v___jp_1932_;
}
v___jp_1932_:
{
uint8_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(v_format_1925_);
v___x_1934_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_lastOperand_1927_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec_ref(v_combinedChain_1929_);
lean_dec_ref(v_doc_1926_);
v___x_1935_ = lean_box(0);
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_inc_ref(v_combinedChain_1929_);
v___x_1936_ = lean_array_pop(v_combinedChain_1929_);
v___x_1937_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1925_, v___x_1936_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1937_);
v___x_1939_ = lean_array_get_size(v_combinedChain_1929_);
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = lean_nat_sub(v___x_1939_, v___x_1940_);
v___x_1942_ = lean_array_get(v___x_1931_, v_combinedChain_1929_, v___x_1941_);
lean_dec(v___x_1941_);
lean_dec_ref(v_combinedChain_1929_);
v___x_1943_ = lean_unsigned_to_nat(2u);
v___x_1944_ = lean_mk_empty_array_with_capacity(v___x_1943_);
v___x_1945_ = lean_array_push(v___x_1944_, v___x_1938_);
v___x_1946_ = lean_array_push(v___x_1945_, v___x_1942_);
v___x_1947_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1925_, v___x_1946_);
lean_dec_ref(v___x_1946_);
v___x_1948_ = l_Lean_Fmt_TaggedDoc_fallbackOnHeight(v_doc_1926_, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
}
}
else
{
lean_object* v___x_1954_; 
lean_dec_ref(v_combinedChain_1929_);
lean_dec_ref(v_lastOperand_1927_);
lean_dec_ref(v_doc_1926_);
v___x_1954_ = lean_box(0);
return v___x_1954_;
}
}
else
{
lean_object* v___x_1955_; 
lean_dec_ref(v_combinedChain_1929_);
lean_dec_ref(v_lastOperand_1927_);
lean_dec_ref(v_doc_1926_);
v___x_1955_ = lean_box(0);
return v___x_1955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f___boxed(lean_object* v_format_1956_, lean_object* v_doc_1957_, lean_object* v_lastOperand_1958_, lean_object* v_isTailless_1959_, lean_object* v_combinedChain_1960_){
_start:
{
uint8_t v_isTailless_boxed_1961_; lean_object* v_res_1962_; 
v_isTailless_boxed_1961_ = lean_unbox(v_isTailless_1959_);
v_res_1962_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_1956_, v_doc_1957_, v_lastOperand_1958_, v_isTailless_boxed_1961_, v_combinedChain_1960_);
lean_dec_ref(v_format_1956_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(lean_object* v_snd_1963_, lean_object* v___x_1964_, lean_object* v_____r_1965_, lean_object* v_normalized_1966_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = lean_nat_add(v_snd_1963_, v___x_1964_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_normalized_1966_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0___boxed(lean_object* v_snd_1970_, lean_object* v___x_1971_, lean_object* v_____r_1972_, lean_object* v_normalized_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1970_, v___x_1971_, v_____r_1972_, v_normalized_1973_);
lean_dec(v___x_1971_);
lean_dec(v_snd_1970_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object* v___x_1975_, lean_object* v_chain_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___y_1979_; lean_object* v_fst_1983_; lean_object* v_snd_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2011_; 
v_fst_1983_ = lean_ctor_get(v_a_1977_, 0);
v_snd_1984_ = lean_ctor_get(v_a_1977_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1986_ = v_a_1977_;
v_isShared_1987_ = v_isSharedCheck_2011_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_snd_1984_);
lean_inc(v_fst_1983_);
lean_dec(v_a_1977_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2011_;
goto v_resetjp_1985_;
}
v___jp_1978_:
{
if (lean_obj_tag(v___y_1979_) == 0)
{
lean_object* v_a_1980_; 
v_a_1980_ = lean_ctor_get(v___y_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___y_1979_, 1);
return v_a_1980_;
}
else
{
lean_object* v_a_1981_; 
v_a_1981_ = lean_ctor_get(v___y_1979_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___y_1979_, 1);
v_a_1977_ = v_a_1981_;
goto _start;
}
}
v_resetjp_1985_:
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_nat_dec_lt(v_snd_1984_, v___x_1975_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1990_; 
if (v_isShared_1987_ == 0)
{
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_fst_1983_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_snd_1984_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1992_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1993_ = lean_array_get_borrowed(v___x_1992_, v_chain_1976_, v_snd_1984_);
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = lean_nat_add(v_snd_1984_, v___x_1994_);
v___x_1996_ = lean_array_get_size(v_chain_1976_);
v___x_1997_ = lean_nat_dec_lt(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_dec(v___x_1995_);
lean_inc(v___x_1993_);
v___x_1998_ = lean_array_push(v_fst_1983_, v___x_1993_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1998_);
v___x_2000_ = v___x_1986_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_snd_1984_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
lean_del_object(v___x_1986_);
v___x_2002_ = lean_unsigned_to_nat(2u);
v___x_2003_ = lean_array_fget_borrowed(v_chain_1976_, v___x_1995_);
lean_dec(v___x_1995_);
v___x_2004_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_inc(v___x_1993_);
v___x_2005_ = lean_array_push(v_fst_1983_, v___x_1993_);
lean_inc(v___x_2003_);
v___x_2006_ = lean_array_push(v___x_2005_, v___x_2003_);
v___x_2007_ = lean_box(0);
v___x_2008_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1984_, v___x_2002_, v___x_2007_, v___x_2006_);
lean_dec(v_snd_1984_);
v___y_1979_ = v___x_2008_;
goto v___jp_1978_;
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1984_, v___x_2002_, v___x_2009_, v_fst_1983_);
lean_dec(v_snd_1984_);
v___y_1979_ = v___x_2010_;
goto v___jp_1978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object* v___x_2012_, lean_object* v_chain_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2012_, v_chain_2013_, v_a_2014_);
lean_dec_ref(v_chain_2013_);
lean_dec(v___x_2012_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(lean_object* v___x_2016_, lean_object* v_chain_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___y_2020_; lean_object* v_fst_2024_; lean_object* v_snd_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2052_; 
v_fst_2024_ = lean_ctor_get(v_a_2018_, 0);
v_snd_2025_ = lean_ctor_get(v_a_2018_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_a_2018_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2027_ = v_a_2018_;
v_isShared_2028_ = v_isSharedCheck_2052_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_snd_2025_);
lean_inc(v_fst_2024_);
lean_dec(v_a_2018_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2052_;
goto v_resetjp_2026_;
}
v___jp_2019_:
{
if (lean_obj_tag(v___y_2020_) == 0)
{
lean_object* v_a_2021_; 
v_a_2021_ = lean_ctor_get(v___y_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___y_2020_, 1);
return v_a_2021_;
}
else
{
lean_object* v_a_2022_; 
v_a_2022_ = lean_ctor_get(v___y_2020_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___y_2020_, 1);
v_a_2018_ = v_a_2022_;
goto _start;
}
}
v_resetjp_2026_:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_nat_dec_lt(v_snd_2025_, v___x_2016_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2031_; 
if (v_isShared_2028_ == 0)
{
v___x_2031_ = v___x_2027_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_fst_2024_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_snd_2025_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2033_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2034_ = lean_array_get_borrowed(v___x_2033_, v_chain_2017_, v_snd_2025_);
v___x_2035_ = lean_unsigned_to_nat(1u);
v___x_2036_ = lean_nat_add(v_snd_2025_, v___x_2035_);
v___x_2037_ = lean_array_get_size(v_chain_2017_);
v___x_2038_ = lean_nat_dec_lt(v___x_2036_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
lean_dec(v___x_2036_);
lean_inc(v___x_2034_);
v___x_2039_ = lean_array_push(v_fst_2024_, v___x_2034_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2039_);
v___x_2041_ = v___x_2027_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_snd_2025_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
else
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
lean_del_object(v___x_2027_);
v___x_2043_ = lean_unsigned_to_nat(2u);
v___x_2044_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2034_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2045_ = lean_array_fget_borrowed(v_chain_2017_, v___x_2036_);
lean_dec(v___x_2036_);
lean_inc(v___x_2034_);
v___x_2046_ = lean_array_push(v_fst_2024_, v___x_2034_);
lean_inc(v___x_2045_);
v___x_2047_ = lean_array_push(v___x_2046_, v___x_2045_);
v___x_2048_ = lean_box(0);
v___x_2049_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2025_, v___x_2043_, v___x_2048_, v___x_2047_);
lean_dec(v_snd_2025_);
v___y_2020_ = v___x_2049_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec(v___x_2036_);
v___x_2050_ = lean_box(0);
v___x_2051_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2025_, v___x_2043_, v___x_2050_, v_fst_2024_);
lean_dec(v_snd_2025_);
v___y_2020_ = v___x_2051_;
goto v___jp_2019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___boxed(lean_object* v___x_2053_, lean_object* v_chain_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2053_, v_chain_2054_, v_a_2055_);
lean_dec_ref(v_chain_2054_);
lean_dec(v___x_2053_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(lean_object* v_format_2065_, lean_object* v_chain_2066_){
_start:
{
lean_object* v___y_2068_; lean_object* v___y_2069_; uint8_t v___y_2070_; lean_object* v___y_2071_; uint8_t v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2089_; lean_object* v___y_2090_; uint8_t v___y_2091_; lean_object* v___y_2092_; uint8_t v___y_2093_; lean_object* v___y_2094_; lean_object* v___f_2109_; lean_object* v___x_2110_; lean_object* v_chainSizeBeforeSuffixTrim_2111_; lean_object* v_chain_2112_; lean_object* v_chainSizeBeforePrefixTrim_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___y_2119_; uint8_t v___y_2120_; lean_object* v___y_2121_; uint8_t v___y_2122_; uint8_t v___y_2123_; lean_object* v___y_2135_; uint8_t v___y_2136_; lean_object* v___y_2137_; uint8_t v___y_2138_; uint8_t v___y_2143_; uint8_t v___x_2153_; 
v___f_2109_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0));
v___x_2110_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_chainSizeBeforeSuffixTrim_2111_ = lean_array_get_size(v_chain_2066_);
v_chain_2112_ = l_Array_popWhile___redArg(v___f_2109_, v_chain_2066_);
v_chainSizeBeforePrefixTrim_2113_ = lean_array_get_size(v_chain_2112_);
v___x_2114_ = lean_nat_sub(v_chainSizeBeforeSuffixTrim_2111_, v_chainSizeBeforePrefixTrim_2113_);
v___x_2115_ = lean_unsigned_to_nat(2u);
v___x_2116_ = lean_nat_mod(v___x_2114_, v___x_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2153_ = lean_nat_dec_eq(v___x_2116_, v___x_2117_);
lean_dec(v___x_2116_);
if (v___x_2153_ == 0)
{
uint8_t v___x_2154_; 
v___x_2154_ = 1;
v___y_2143_ = v___x_2154_;
goto v___jp_2142_;
}
else
{
uint8_t v___x_2155_; 
v___x_2155_ = 0;
v___y_2143_ = v___x_2155_;
goto v___jp_2142_;
}
v___jp_2067_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_fst_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2086_; 
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___y_2069_);
lean_ctor_set(v___x_2074_, 1, v___y_2073_);
v___x_2075_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___y_2068_, v___y_2071_, v___x_2074_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2068_);
v_fst_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v___x_2075_, 1);
lean_dec(v_unused_2087_);
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_fst_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2080_ = lean_box(v___y_2072_);
v___x_2081_ = lean_box(v___y_2070_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 1, v___x_2081_);
lean_ctor_set(v___x_2078_, 0, v___x_2080_);
v___x_2083_ = v___x_2078_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v_fst_2076_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
return v___x_2084_;
}
}
}
v___jp_2088_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v_fst_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2107_; 
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___y_2090_);
lean_ctor_set(v___x_2095_, 1, v___y_2094_);
v___x_2096_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___y_2089_, v___y_2092_, v___x_2095_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2089_);
v_fst_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v___x_2096_, 1);
lean_dec(v_unused_2108_);
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2107_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_fst_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2107_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2101_ = lean_box(v___y_2093_);
v___x_2102_ = lean_box(v___y_2091_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___x_2102_);
lean_ctor_set(v___x_2099_, 0, v___x_2101_);
v___x_2104_ = v___x_2099_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_fst_2097_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
return v___x_2105_;
}
}
}
v___jp_2118_:
{
if (v___y_2123_ == 0)
{
if (v___y_2122_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = lean_array_get_borrowed(v___x_2110_, v___y_2121_, v___x_2117_);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_mk_empty_array_with_capacity(v___x_2125_);
lean_inc(v___x_2124_);
v___x_2127_ = lean_array_push(v___x_2126_, v___x_2124_);
v___y_2089_ = v___y_2119_;
v___y_2090_ = v___x_2127_;
v___y_2091_ = v___y_2120_;
v___y_2092_ = v___y_2121_;
v___y_2093_ = v___y_2122_;
v___y_2094_ = v___x_2125_;
goto v___jp_2088_;
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2089_ = v___y_2119_;
v___y_2090_ = v___x_2128_;
v___y_2091_ = v___y_2120_;
v___y_2092_ = v___y_2121_;
v___y_2093_ = v___y_2122_;
v___y_2094_ = v___x_2117_;
goto v___jp_2088_;
}
}
else
{
if (v___y_2122_ == 0)
{
lean_object* v___x_2129_; 
v___x_2129_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2068_ = v___y_2119_;
v___y_2069_ = v___x_2129_;
v___y_2070_ = v___y_2120_;
v___y_2071_ = v___y_2121_;
v___y_2072_ = v___y_2122_;
v___y_2073_ = v___x_2117_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_array_get_borrowed(v___x_2110_, v___y_2121_, v___x_2117_);
v___x_2131_ = lean_unsigned_to_nat(1u);
v___x_2132_ = lean_mk_empty_array_with_capacity(v___x_2131_);
lean_inc(v___x_2130_);
v___x_2133_ = lean_array_push(v___x_2132_, v___x_2130_);
v___y_2068_ = v___y_2119_;
v___y_2069_ = v___x_2133_;
v___y_2070_ = v___y_2120_;
v___y_2071_ = v___y_2121_;
v___y_2072_ = v___y_2122_;
v___y_2073_ = v___x_2131_;
goto v___jp_2067_;
}
}
}
v___jp_2134_:
{
uint8_t v___x_2139_; 
v___x_2139_ = lean_nat_dec_eq(v___y_2135_, v___x_2117_);
if (v___x_2139_ == 0)
{
uint8_t v_trailingOperator_2140_; 
v_trailingOperator_2140_ = lean_ctor_get_uint8(v_format_2065_, 1);
v___y_2119_ = v___y_2135_;
v___y_2120_ = v___y_2136_;
v___y_2121_ = v___y_2137_;
v___y_2122_ = v___y_2138_;
v___y_2123_ = v_trailingOperator_2140_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2141_; 
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2135_);
v___x_2141_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2));
return v___x_2141_;
}
}
v___jp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v_chain_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2144_ = l_Array_reverse___redArg(v_chain_2112_);
v___x_2145_ = l_Array_popWhile___redArg(v___f_2109_, v___x_2144_);
v_chain_2146_ = l_Array_reverse___redArg(v___x_2145_);
v___x_2147_ = lean_array_get_size(v_chain_2146_);
v___x_2148_ = lean_nat_sub(v_chainSizeBeforePrefixTrim_2113_, v___x_2147_);
v___x_2149_ = lean_nat_mod(v___x_2148_, v___x_2115_);
lean_dec(v___x_2148_);
v___x_2150_ = lean_nat_dec_eq(v___x_2149_, v___x_2117_);
lean_dec(v___x_2149_);
if (v___x_2150_ == 0)
{
uint8_t v___x_2151_; 
v___x_2151_ = 1;
v___y_2135_ = v___x_2147_;
v___y_2136_ = v___y_2143_;
v___y_2137_ = v_chain_2146_;
v___y_2138_ = v___x_2151_;
goto v___jp_2134_;
}
else
{
uint8_t v___x_2152_; 
v___x_2152_ = 0;
v___y_2135_ = v___x_2147_;
v___y_2136_ = v___y_2143_;
v___y_2137_ = v_chain_2146_;
v___y_2138_ = v___x_2152_;
goto v___jp_2134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___boxed(lean_object* v_format_2156_, lean_object* v_chain_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2156_, v_chain_2157_);
lean_dec_ref(v_format_2156_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(lean_object* v___x_2159_, lean_object* v_chain_2160_, lean_object* v_inst_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2159_, v_chain_2160_, v_a_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___boxed(lean_object* v___x_2164_, lean_object* v_chain_2165_, lean_object* v_inst_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(v___x_2164_, v_chain_2165_, v_inst_2166_, v_a_2167_);
lean_dec_ref(v_chain_2165_);
lean_dec(v___x_2164_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object* v___x_2169_, lean_object* v_chain_2170_, lean_object* v_inst_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2169_, v_chain_2170_, v_a_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object* v___x_2174_, lean_object* v_chain_2175_, lean_object* v_inst_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(v___x_2174_, v_chain_2175_, v_inst_2176_, v_a_2177_);
lean_dec_ref(v_chain_2175_);
lean_dec(v___x_2174_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(lean_object* v_chain_2179_, lean_object* v_format_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_fst_2182_; lean_object* v_snd_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2213_; 
v_fst_2182_ = lean_ctor_get(v_a_2181_, 0);
v_snd_2183_ = lean_ctor_get(v_a_2181_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_a_2181_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2185_ = v_a_2181_;
v_isShared_2186_ = v_isSharedCheck_2213_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_snd_2183_);
lean_inc(v_fst_2182_);
lean_dec(v_a_2181_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2213_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2187_ = lean_array_get_size(v_chain_2179_);
v___x_2188_ = lean_nat_dec_lt(v_snd_2183_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2190_; 
if (v_isShared_2186_ == 0)
{
v___x_2190_ = v___x_2185_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_fst_2182_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_snd_2183_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___y_2195_; lean_object* v___x_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2192_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2193_ = lean_array_get_borrowed(v___x_2192_, v_chain_2179_, v_snd_2183_);
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = lean_nat_add(v_snd_2183_, v___x_2208_);
v___x_2210_ = lean_nat_dec_lt(v___x_2209_, v___x_2187_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; 
lean_dec(v___x_2209_);
v___x_2211_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2195_ = v___x_2211_;
goto v___jp_2194_;
}
else
{
lean_object* v___x_2212_; 
v___x_2212_ = lean_array_fget_borrowed(v_chain_2179_, v___x_2209_);
lean_dec(v___x_2209_);
lean_inc(v___x_2212_);
v___y_2195_ = v___x_2212_;
goto v___jp_2194_;
}
v___jp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2196_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2195_);
v___x_2197_ = lean_unsigned_to_nat(2u);
v___x_2198_ = lean_mk_empty_array_with_capacity(v___x_2197_);
lean_inc(v___x_2193_);
v___x_2199_ = lean_array_push(v___x_2198_, v___x_2193_);
v___x_2200_ = lean_array_push(v___x_2199_, v___x_2196_);
v___x_2201_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2180_, v___x_2200_);
lean_dec_ref(v___x_2200_);
v___x_2202_ = lean_array_push(v_fst_2182_, v___x_2201_);
v___x_2203_ = lean_nat_add(v_snd_2183_, v___x_2197_);
lean_dec(v_snd_2183_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 1, v___x_2203_);
lean_ctor_set(v___x_2185_, 0, v___x_2202_);
v___x_2205_ = v___x_2185_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
v_a_2181_ = v___x_2205_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg___boxed(lean_object* v_chain_2214_, lean_object* v_format_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2214_, v_format_2215_, v_a_2216_);
lean_dec_ref(v_format_2215_);
lean_dec_ref(v_chain_2214_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(lean_object* v_chain_2218_, lean_object* v_format_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_fst_2221_; lean_object* v_snd_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2252_; 
v_fst_2221_ = lean_ctor_get(v_a_2220_, 0);
v_snd_2222_ = lean_ctor_get(v_a_2220_, 1);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_a_2220_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2224_ = v_a_2220_;
v_isShared_2225_ = v_isSharedCheck_2252_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_snd_2222_);
lean_inc(v_fst_2221_);
lean_dec(v_a_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2252_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = lean_array_get_size(v_chain_2218_);
v___x_2227_ = lean_nat_dec_lt(v_snd_2222_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2229_; 
if (v_isShared_2225_ == 0)
{
v___x_2229_ = v___x_2224_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_fst_2221_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_snd_2222_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___y_2234_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2231_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2232_ = lean_array_get_borrowed(v___x_2231_, v_chain_2218_, v_snd_2222_);
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = lean_nat_add(v_snd_2222_, v___x_2247_);
v___x_2249_ = lean_nat_dec_lt(v___x_2248_, v___x_2226_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; 
lean_dec(v___x_2248_);
v___x_2250_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2234_ = v___x_2250_;
goto v___jp_2233_;
}
else
{
lean_object* v___x_2251_; 
v___x_2251_ = lean_array_fget_borrowed(v_chain_2218_, v___x_2248_);
lean_dec(v___x_2248_);
lean_inc(v___x_2251_);
v___y_2234_ = v___x_2251_;
goto v___jp_2233_;
}
v___jp_2233_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
lean_inc(v___x_2232_);
v___x_2235_ = l_Lean_Fmt_TaggedDoc_nested(v___x_2232_);
v___x_2236_ = lean_unsigned_to_nat(2u);
v___x_2237_ = lean_mk_empty_array_with_capacity(v___x_2236_);
v___x_2238_ = lean_array_push(v___x_2237_, v___x_2235_);
v___x_2239_ = lean_array_push(v___x_2238_, v___y_2234_);
v___x_2240_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2219_, v___x_2239_);
lean_dec_ref(v___x_2239_);
v___x_2241_ = lean_array_push(v_fst_2221_, v___x_2240_);
v___x_2242_ = lean_nat_add(v_snd_2222_, v___x_2236_);
lean_dec(v_snd_2222_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 1, v___x_2242_);
lean_ctor_set(v___x_2224_, 0, v___x_2241_);
v___x_2244_ = v___x_2224_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
v_a_2220_ = v___x_2244_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg___boxed(lean_object* v_chain_2253_, lean_object* v_format_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2253_, v_format_2254_, v_a_2255_);
lean_dec_ref(v_format_2254_);
lean_dec_ref(v_chain_2253_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(lean_object* v_format_2257_, lean_object* v_chain_2258_, uint8_t v_isHeadless_2259_){
_start:
{
lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2267_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2277_; lean_object* v___x_2280_; uint8_t v___y_2282_; uint8_t v_trailingOperator_2295_; 
v___x_2280_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_2295_ = lean_ctor_get_uint8(v_format_2257_, 1);
v___y_2282_ = v_trailingOperator_2295_;
goto v___jp_2281_;
v___jp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_fst_2265_; 
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___y_2261_);
lean_ctor_set(v___x_2263_, 1, v___y_2262_);
v___x_2264_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2258_, v_format_2257_, v___x_2263_);
v_fst_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_fst_2265_);
lean_dec_ref(v___x_2264_);
return v_fst_2265_;
}
v___jp_2266_:
{
if (v_isHeadless_2259_ == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_unsigned_to_nat(0u);
v___y_2261_ = v___y_2267_;
v___y_2262_ = v___x_2268_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_unsigned_to_nat(1u);
v___y_2261_ = v___y_2267_;
v___y_2262_ = v___x_2269_;
goto v___jp_2260_;
}
}
v___jp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v_fst_2275_; 
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___y_2271_);
lean_ctor_set(v___x_2273_, 1, v___y_2272_);
v___x_2274_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2258_, v_format_2257_, v___x_2273_);
v_fst_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_fst_2275_);
lean_dec_ref(v___x_2274_);
return v_fst_2275_;
}
v___jp_2276_:
{
if (v_isHeadless_2259_ == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_unsigned_to_nat(1u);
v___y_2271_ = v___y_2277_;
v___y_2272_ = v___x_2278_;
goto v___jp_2270_;
}
else
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_unsigned_to_nat(0u);
v___y_2271_ = v___y_2277_;
v___y_2272_ = v___x_2279_;
goto v___jp_2270_;
}
}
v___jp_2281_:
{
if (v___y_2282_ == 0)
{
if (v_isHeadless_2259_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2284_ = lean_array_get_borrowed(v___x_2280_, v_chain_2258_, v___x_2283_);
v___x_2285_ = lean_unsigned_to_nat(1u);
v___x_2286_ = lean_mk_empty_array_with_capacity(v___x_2285_);
lean_inc(v___x_2284_);
v___x_2287_ = lean_array_push(v___x_2286_, v___x_2284_);
v___y_2277_ = v___x_2287_;
goto v___jp_2276_;
}
else
{
lean_object* v___x_2288_; 
v___x_2288_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2277_ = v___x_2288_;
goto v___jp_2276_;
}
}
else
{
if (v_isHeadless_2259_ == 0)
{
lean_object* v___x_2289_; 
v___x_2289_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2267_ = v___x_2289_;
goto v___jp_2266_;
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = lean_array_get_borrowed(v___x_2280_, v_chain_2258_, v___x_2290_);
v___x_2292_ = lean_unsigned_to_nat(1u);
v___x_2293_ = lean_mk_empty_array_with_capacity(v___x_2292_);
lean_inc(v___x_2291_);
v___x_2294_ = lean_array_push(v___x_2293_, v___x_2291_);
v___y_2267_ = v___x_2294_;
goto v___jp_2266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain___boxed(lean_object* v_format_2296_, lean_object* v_chain_2297_, lean_object* v_isHeadless_2298_){
_start:
{
uint8_t v_isHeadless_boxed_2299_; lean_object* v_res_2300_; 
v_isHeadless_boxed_2299_ = lean_unbox(v_isHeadless_2298_);
v_res_2300_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2296_, v_chain_2297_, v_isHeadless_boxed_2299_);
lean_dec_ref(v_chain_2297_);
lean_dec_ref(v_format_2296_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(lean_object* v_chain_2301_, lean_object* v_format_2302_, lean_object* v_inst_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2301_, v_format_2302_, v_a_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___boxed(lean_object* v_chain_2306_, lean_object* v_format_2307_, lean_object* v_inst_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(v_chain_2306_, v_format_2307_, v_inst_2308_, v_a_2309_);
lean_dec_ref(v_format_2307_);
lean_dec_ref(v_chain_2306_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(lean_object* v_chain_2311_, lean_object* v_format_2312_, lean_object* v_inst_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2311_, v_format_2312_, v_a_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___boxed(lean_object* v_chain_2316_, lean_object* v_format_2317_, lean_object* v_inst_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(v_chain_2316_, v_format_2317_, v_inst_2318_, v_a_2319_);
lean_dec_ref(v_format_2317_);
lean_dec_ref(v_chain_2316_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(lean_object* v_format_2321_, lean_object* v_docs_2322_){
_start:
{
uint8_t v___y_2324_; uint8_t v___x_2327_; 
v___x_2327_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_format_2321_);
if (v___x_2327_ == 0)
{
uint8_t v___x_2328_; 
v___x_2328_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_format_2321_);
if (v___x_2328_ == 0)
{
uint8_t v_spacing_2329_; 
v_spacing_2329_ = lean_ctor_get_uint8(v_format_2321_, 2);
v___y_2324_ = v_spacing_2329_;
goto v___jp_2323_;
}
else
{
lean_object* v___x_2330_; uint8_t v___y_2332_; uint8_t v_spacing_2359_; 
v___x_2330_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_spacing_2359_ = lean_ctor_get_uint8(v_format_2321_, 2);
v___y_2332_ = v_spacing_2359_;
goto v___jp_2331_;
v___jp_2331_:
{
if (v___y_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2333_ = lean_unsigned_to_nat(0u);
v___x_2334_ = lean_array_get_size(v_docs_2322_);
v___x_2335_ = lean_unsigned_to_nat(1u);
v___x_2336_ = lean_nat_sub(v___x_2334_, v___x_2335_);
lean_inc(v___x_2336_);
lean_inc_ref(v_docs_2322_);
v___x_2337_ = l_Array_toSubarray___redArg(v_docs_2322_, v___x_2333_, v___x_2336_);
v___x_2338_ = l_Subarray_copy___redArg(v___x_2337_);
v___x_2339_ = l_Lean_Fmt_TaggedDoc_fill(v___x_2338_);
v___x_2340_ = lean_array_get(v___x_2330_, v_docs_2322_, v___x_2336_);
lean_dec(v___x_2336_);
lean_dec_ref(v_docs_2322_);
v___x_2341_ = lean_unsigned_to_nat(2u);
v___x_2342_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_2343_ = lean_array_push(v___x_2342_, v___x_2339_);
v___x_2344_ = lean_array_push(v___x_2343_, v___x_2340_);
v___x_2345_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2344_, v___y_2332_);
lean_dec_ref(v___x_2344_);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_array_get_size(v_docs_2322_);
v___x_2348_ = lean_unsigned_to_nat(1u);
v___x_2349_ = lean_nat_sub(v___x_2347_, v___x_2348_);
lean_inc(v___x_2349_);
lean_inc_ref(v_docs_2322_);
v___x_2350_ = l_Array_toSubarray___redArg(v_docs_2322_, v___x_2346_, v___x_2349_);
v___x_2351_ = l_Subarray_copy___redArg(v___x_2350_);
v___x_2352_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_2351_);
v___x_2353_ = lean_array_get(v___x_2330_, v_docs_2322_, v___x_2349_);
lean_dec(v___x_2349_);
lean_dec_ref(v_docs_2322_);
v___x_2354_ = lean_unsigned_to_nat(2u);
v___x_2355_ = lean_mk_empty_array_with_capacity(v___x_2354_);
v___x_2356_ = lean_array_push(v___x_2355_, v___x_2352_);
v___x_2357_ = lean_array_push(v___x_2356_, v___x_2353_);
v___x_2358_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2357_, v___x_2328_);
lean_dec_ref(v___x_2357_);
return v___x_2358_;
}
}
}
}
else
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_Fmt_Layouts_lines(v_docs_2322_);
lean_dec_ref(v_docs_2322_);
return v___x_2360_;
}
v___jp_2323_:
{
if (v___y_2324_ == 0)
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_Fmt_TaggedDoc_fill(v_docs_2322_);
return v___x_2325_;
}
else
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v_docs_2322_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill___boxed(lean_object* v_format_2361_, lean_object* v_docs_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2361_, v_docs_2362_);
lean_dec_ref(v_format_2361_);
return v_res_2363_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(lean_object* v_columnPos_2364_, lean_object* v_indentation_2365_, lean_object* v_nonCumulativeIndentation_2366_){
_start:
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = lean_nat_add(v_indentation_2365_, v_nonCumulativeIndentation_2366_);
v___x_2368_ = lean_nat_dec_le(v_columnPos_2364_, v___x_2367_);
lean_dec(v___x_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed(lean_object* v_columnPos_2369_, lean_object* v_indentation_2370_, lean_object* v_nonCumulativeIndentation_2371_){
_start:
{
uint8_t v_res_2372_; lean_object* v_r_2373_; 
v_res_2372_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(v_columnPos_2369_, v_indentation_2370_, v_nonCumulativeIndentation_2371_);
lean_dec(v_nonCumulativeIndentation_2371_);
lean_dec(v_indentation_2370_);
lean_dec(v_columnPos_2369_);
v_r_2373_ = lean_box(v_res_2372_);
return v_r_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(lean_object* v_format_2390_, lean_object* v_combinedChain_2391_){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v_firstOperand_2394_; lean_object* v___y_2396_; uint8_t v___y_2416_; uint8_t v_hardNestedFirstOperand_2423_; 
v___x_2392_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2393_ = lean_unsigned_to_nat(0u);
v_firstOperand_2394_ = lean_array_get_borrowed(v___x_2392_, v_combinedChain_2391_, v___x_2393_);
v_hardNestedFirstOperand_2423_ = lean_ctor_get_uint8(v_format_2390_, 0);
v___y_2416_ = v_hardNestedFirstOperand_2423_;
goto v___jp_2415_;
v___jp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v_compactFirstOperation_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v_compactedChain_2410_; lean_object* v___x_2411_; 
v___x_2397_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion));
v___x_2398_ = l_Lean_Fmt_TaggedDoc_guarded(v___x_2397_, v___y_2396_);
v___x_2399_ = lean_unsigned_to_nat(2u);
v___x_2400_ = lean_mk_empty_array_with_capacity(v___x_2399_);
lean_inc(v_firstOperand_2394_);
v___x_2401_ = lean_array_push(v___x_2400_, v_firstOperand_2394_);
v___x_2402_ = lean_array_push(v___x_2401_, v___x_2398_);
v_compactFirstOperation_2403_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2390_, v___x_2402_);
lean_dec_ref(v___x_2402_);
v___x_2404_ = lean_unsigned_to_nat(1u);
v___x_2405_ = lean_mk_empty_array_with_capacity(v___x_2404_);
v___x_2406_ = lean_array_push(v___x_2405_, v_compactFirstOperation_2403_);
v___x_2407_ = lean_array_get_size(v_combinedChain_2391_);
v___x_2408_ = l_Array_toSubarray___redArg(v_combinedChain_2391_, v___x_2399_, v___x_2407_);
v___x_2409_ = l_Subarray_copy___redArg(v___x_2408_);
v_compactedChain_2410_ = l_Array_append___redArg(v___x_2406_, v___x_2409_);
lean_dec_ref(v___x_2409_);
v___x_2411_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2390_, v_compactedChain_2410_);
return v___x_2411_;
}
v___jp_2412_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_array_get_borrowed(v___x_2392_, v_combinedChain_2391_, v___x_2413_);
lean_inc(v___x_2414_);
v___y_2396_ = v___x_2414_;
goto v___jp_2395_;
}
v___jp_2415_:
{
if (v___y_2416_ == 0)
{
goto v___jp_2412_;
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2417_ = lean_unsigned_to_nat(2u);
v___x_2418_ = lean_array_get_size(v_combinedChain_2391_);
v___x_2419_ = lean_nat_dec_lt(v___x_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
goto v___jp_2412_;
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = lean_unsigned_to_nat(1u);
v___x_2421_ = lean_array_get_borrowed(v___x_2392_, v_combinedChain_2391_, v___x_2420_);
lean_inc(v___x_2421_);
v___x_2422_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_2421_);
v___y_2396_ = v___x_2422_;
goto v___jp_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation___boxed(lean_object* v_format_2424_, lean_object* v_combinedChain_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2424_, v_combinedChain_2425_);
lean_dec_ref(v_format_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(lean_object* v_format_2427_, lean_object* v_docs_2428_, lean_object* v_wrap_2429_){
_start:
{
uint8_t v___y_2431_; uint8_t v_spacing_2434_; 
v_spacing_2434_ = lean_ctor_get_uint8(v_format_2427_, 2);
v___y_2431_ = v_spacing_2434_;
goto v___jp_2430_;
v___jp_2430_:
{
if (v___y_2431_ == 0)
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_Fmt_TaggedDoc_fillWrapping(v_docs_2428_, v_wrap_2429_);
return v___x_2432_;
}
else
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(v_docs_2428_, v_wrap_2429_);
return v___x_2433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping___boxed(lean_object* v_format_2435_, lean_object* v_docs_2436_, lean_object* v_wrap_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2435_, v_docs_2436_, v_wrap_2437_);
lean_dec_ref(v_format_2435_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(lean_object* v___x_2439_, size_t v_sz_2440_, size_t v_i_2441_, lean_object* v_bs_2442_){
_start:
{
uint8_t v___x_2443_; 
v___x_2443_ = lean_usize_dec_lt(v_i_2441_, v_sz_2440_);
if (v___x_2443_ == 0)
{
return v_bs_2442_;
}
else
{
lean_object* v___x_2444_; lean_object* v_v_2445_; lean_object* v___x_2446_; lean_object* v_bs_x27_2447_; lean_object* v___y_2449_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2444_ = lean_unsigned_to_nat(1u);
v_v_2445_ = lean_array_uget(v_bs_2442_, v_i_2441_);
v___x_2446_ = lean_unsigned_to_nat(0u);
v_bs_x27_2447_ = lean_array_uset(v_bs_2442_, v_i_2441_, v___x_2446_);
v___x_2454_ = lean_usize_to_nat(v_i_2441_);
v___x_2455_ = lean_nat_sub(v___x_2439_, v___x_2444_);
v___x_2456_ = lean_nat_dec_lt(v___x_2454_, v___x_2455_);
lean_dec(v___x_2455_);
lean_dec(v___x_2454_);
if (v___x_2456_ == 0)
{
v___y_2449_ = v_v_2445_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2445_);
v___y_2449_ = v___x_2457_;
goto v___jp_2448_;
}
v___jp_2448_:
{
size_t v___x_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_add(v_i_2441_, v___x_2450_);
v___x_2452_ = lean_array_uset(v_bs_x27_2447_, v_i_2441_, v___y_2449_);
v_i_2441_ = v___x_2451_;
v_bs_2442_ = v___x_2452_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg___boxed(lean_object* v___x_2458_, lean_object* v_sz_2459_, lean_object* v_i_2460_, lean_object* v_bs_2461_){
_start:
{
size_t v_sz_boxed_2462_; size_t v_i_boxed_2463_; lean_object* v_res_2464_; 
v_sz_boxed_2462_ = lean_unbox_usize(v_sz_2459_);
lean_dec(v_sz_2459_);
v_i_boxed_2463_ = lean_unbox_usize(v_i_2460_);
lean_dec(v_i_2460_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2458_, v_sz_boxed_2462_, v_i_boxed_2463_, v_bs_2461_);
lean_dec(v___x_2458_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object* v_chain_2479_, lean_object* v_format_2480_){
_start:
{
lean_object* v___x_2481_; lean_object* v_snd_2482_; lean_object* v_fst_2483_; lean_object* v_fst_2484_; lean_object* v_snd_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2481_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2480_, v_chain_2479_);
v_snd_2482_ = lean_ctor_get(v___x_2481_, 1);
lean_inc(v_snd_2482_);
v_fst_2483_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_fst_2483_);
lean_dec_ref(v___x_2481_);
v_fst_2484_ = lean_ctor_get(v_snd_2482_, 0);
lean_inc(v_fst_2484_);
v_snd_2485_ = lean_ctor_get(v_snd_2482_, 1);
lean_inc(v_snd_2485_);
lean_dec(v_snd_2482_);
v___x_2486_ = lean_array_get_size(v_fst_2483_);
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = lean_nat_dec_eq(v___x_2486_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; uint8_t v___y_2491_; lean_object* v_doc_2492_; uint8_t v___x_2499_; lean_object* v_combinedChain_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___y_2504_; uint8_t v___y_2505_; lean_object* v_doc_2506_; lean_object* v___y_2521_; uint8_t v___y_2522_; lean_object* v___y_2523_; uint8_t v___x_2531_; lean_object* v___y_2533_; uint8_t v___y_2534_; lean_object* v_combinedChain_2540_; uint8_t v___y_2543_; uint8_t v___y_2550_; uint8_t v___y_2551_; uint8_t v___y_2559_; 
v___x_2489_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2499_ = lean_unbox(v_fst_2484_);
v_combinedChain_2500_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2480_, v_fst_2483_, v___x_2499_);
v___x_2501_ = lean_array_get_size(v_combinedChain_2500_);
v___x_2502_ = lean_unsigned_to_nat(1u);
v___x_2531_ = lean_nat_dec_eq(v___x_2501_, v___x_2502_);
if (v___x_2531_ == 0)
{
uint8_t v_trailingOperator_2561_; 
v_trailingOperator_2561_ = lean_ctor_get_uint8(v_format_2480_, 1);
v___y_2559_ = v_trailingOperator_2561_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2562_; 
lean_dec(v_snd_2485_);
lean_dec(v_fst_2484_);
lean_dec(v_fst_2483_);
v___x_2562_ = lean_array_get(v___x_2489_, v_combinedChain_2500_, v___x_2487_);
lean_dec_ref(v_combinedChain_2500_);
return v___x_2562_;
}
v___jp_2490_:
{
if (v___y_2491_ == 0)
{
lean_object* v___x_2493_; 
lean_dec(v_fst_2483_);
v___x_2493_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2492_);
return v___x_2493_;
}
else
{
lean_object* v___x_2494_; lean_object* v_doc_2495_; uint8_t v___x_2496_; lean_object* v_doc_2497_; lean_object* v___x_2498_; 
v___x_2494_ = lean_array_get(v___x_2489_, v_fst_2483_, v___x_2487_);
lean_dec(v_fst_2483_);
v_doc_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_doc_2495_);
lean_dec(v___x_2494_);
v___x_2496_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2495_);
v_doc_2497_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2492_, v___x_2496_);
v___x_2498_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2497_);
return v___x_2498_;
}
}
v___jp_2503_:
{
lean_object* v___x_2507_; lean_object* v_lastOperand_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2507_ = lean_nat_sub(v___x_2486_, v___x_2502_);
v_lastOperand_2508_ = lean_array_get_borrowed(v___x_2489_, v_fst_2483_, v___x_2507_);
lean_dec(v___x_2507_);
v___x_2509_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
v___x_2510_ = lean_unbox(v_snd_2485_);
lean_inc_ref(v___y_2504_);
lean_inc(v_lastOperand_2508_);
lean_inc_ref(v_doc_2506_);
v___x_2511_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2480_, v_doc_2506_, v_lastOperand_2508_, v___x_2510_, v___y_2504_, v___x_2509_);
if (lean_obj_tag(v___x_2511_) == 1)
{
lean_object* v_val_2512_; 
lean_dec_ref(v_doc_2506_);
lean_dec_ref(v___y_2504_);
lean_dec(v_snd_2485_);
v_val_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_val_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v___y_2491_ = v___y_2505_;
v_doc_2492_ = v_val_2512_;
goto v___jp_2490_;
}
else
{
uint8_t v___x_2513_; lean_object* v___x_2514_; 
lean_dec(v___x_2511_);
v___x_2513_ = lean_unbox(v_snd_2485_);
lean_inc_ref(v___y_2504_);
lean_inc(v_lastOperand_2508_);
lean_inc_ref(v_doc_2506_);
v___x_2514_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2480_, v_doc_2506_, v_lastOperand_2508_, v___x_2513_, v___y_2504_);
if (lean_obj_tag(v___x_2514_) == 1)
{
lean_object* v_val_2515_; 
lean_dec_ref(v_doc_2506_);
lean_dec_ref(v___y_2504_);
lean_dec(v_snd_2485_);
v_val_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_val_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___y_2491_ = v___y_2505_;
v_doc_2492_ = v_val_2515_;
goto v___jp_2490_;
}
else
{
lean_object* v___x_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; 
lean_dec(v___x_2514_);
v___x_2516_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
v___x_2517_ = lean_unbox(v_snd_2485_);
lean_dec(v_snd_2485_);
lean_inc(v_lastOperand_2508_);
lean_inc_ref(v_doc_2506_);
v___x_2518_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2480_, v_doc_2506_, v_lastOperand_2508_, v___x_2517_, v___y_2504_, v___x_2516_);
if (lean_obj_tag(v___x_2518_) == 1)
{
lean_object* v_val_2519_; 
lean_dec_ref(v_doc_2506_);
v_val_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_val_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v___y_2491_ = v___y_2505_;
v_doc_2492_ = v_val_2519_;
goto v___jp_2490_;
}
else
{
lean_dec(v___x_2518_);
v___y_2491_ = v___y_2505_;
v_doc_2492_ = v_doc_2506_;
goto v___jp_2490_;
}
}
}
}
v___jp_2520_:
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_unbox(v_fst_2484_);
lean_dec(v_fst_2484_);
if (v___x_2524_ == 0)
{
if (v___y_2522_ == 0)
{
v___y_2504_ = v___y_2521_;
v___y_2505_ = v___y_2522_;
v_doc_2506_ = v___y_2523_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_doc_2530_; 
lean_inc_ref(v___y_2521_);
v___x_2525_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2480_, v___y_2521_);
v___x_2526_ = lean_unsigned_to_nat(2u);
v___x_2527_ = lean_mk_empty_array_with_capacity(v___x_2526_);
v___x_2528_ = lean_array_push(v___x_2527_, v___x_2525_);
v___x_2529_ = lean_array_push(v___x_2528_, v___y_2523_);
v_doc_2530_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2529_);
v___y_2504_ = v___y_2521_;
v___y_2505_ = v___y_2522_;
v_doc_2506_ = v_doc_2530_;
goto v___jp_2503_;
}
}
else
{
v___y_2504_ = v___y_2521_;
v___y_2505_ = v___y_2522_;
v_doc_2506_ = v___y_2523_;
goto v___jp_2503_;
}
}
v___jp_2532_:
{
if (v___y_2534_ == 0)
{
uint8_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = 1;
lean_inc_ref(v___y_2533_);
v___x_2536_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2480_, v___y_2533_);
v___y_2521_ = v___y_2533_;
v___y_2522_ = v___x_2535_;
v___y_2523_ = v___x_2536_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
lean_inc_ref(v___y_2533_);
v___x_2538_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2480_, v___y_2533_, v___x_2537_);
v___y_2521_ = v___y_2533_;
v___y_2522_ = v___x_2531_;
v___y_2523_ = v___x_2538_;
goto v___jp_2520_;
}
}
v___jp_2539_:
{
uint8_t v_trailingOperator_2541_; 
v_trailingOperator_2541_ = lean_ctor_get_uint8(v_format_2480_, 1);
v___y_2533_ = v_combinedChain_2540_;
v___y_2534_ = v_trailingOperator_2541_;
goto v___jp_2532_;
}
v___jp_2542_:
{
if (v___y_2543_ == 0)
{
v_combinedChain_2540_ = v_combinedChain_2500_;
goto v___jp_2539_;
}
else
{
size_t v_sz_2544_; size_t v___x_2545_; lean_object* v_combinedChain_2546_; 
v_sz_2544_ = lean_array_size(v_combinedChain_2500_);
v___x_2545_ = ((size_t)0ULL);
v_combinedChain_2546_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2501_, v_sz_2544_, v___x_2545_, v_combinedChain_2500_);
v_combinedChain_2540_ = v_combinedChain_2546_;
goto v___jp_2539_;
}
}
v___jp_2547_:
{
uint8_t v_hardNestedFirstOperand_2548_; 
v_hardNestedFirstOperand_2548_ = lean_ctor_get_uint8(v_format_2480_, 0);
v___y_2543_ = v_hardNestedFirstOperand_2548_;
goto v___jp_2542_;
}
v___jp_2549_:
{
if (v___y_2551_ == 0)
{
if (v___y_2550_ == 0)
{
v_combinedChain_2540_ = v_combinedChain_2500_;
goto v___jp_2539_;
}
else
{
goto v___jp_2547_;
}
}
else
{
uint8_t v___x_2552_; 
v___x_2552_ = lean_nat_dec_lt(v___x_2487_, v___x_2501_);
if (v___x_2552_ == 0)
{
v_combinedChain_2540_ = v_combinedChain_2500_;
goto v___jp_2539_;
}
else
{
lean_object* v_v_2553_; lean_object* v___x_2554_; lean_object* v_xs_x27_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_v_2553_ = lean_array_fget(v_combinedChain_2500_, v___x_2487_);
v___x_2554_ = lean_box(0);
v_xs_x27_2555_ = lean_array_fset(v_combinedChain_2500_, v___x_2487_, v___x_2554_);
v___x_2556_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2553_);
v___x_2557_ = lean_array_fset(v_xs_x27_2555_, v___x_2487_, v___x_2556_);
v_combinedChain_2540_ = v___x_2557_;
goto v___jp_2539_;
}
}
}
v___jp_2558_:
{
if (v___y_2559_ == 0)
{
uint8_t v_hardNestedFirstOperand_2560_; 
v_hardNestedFirstOperand_2560_ = lean_ctor_get_uint8(v_format_2480_, 0);
v___y_2550_ = v___y_2559_;
v___y_2551_ = v_hardNestedFirstOperand_2560_;
goto v___jp_2549_;
}
else
{
goto v___jp_2547_;
}
}
}
else
{
lean_object* v___x_2563_; 
lean_dec(v_snd_2485_);
lean_dec(v_fst_2484_);
lean_dec(v_fst_2483_);
v___x_2563_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator___boxed(lean_object* v_chain_2564_, lean_object* v_format_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_2564_, v_format_2565_);
lean_dec_ref(v_format_2565_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(lean_object* v___x_2567_, lean_object* v_as_2568_, size_t v_sz_2569_, size_t v_i_2570_, lean_object* v_bs_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2567_, v_sz_2569_, v_i_2570_, v_bs_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___boxed(lean_object* v___x_2573_, lean_object* v_as_2574_, lean_object* v_sz_2575_, lean_object* v_i_2576_, lean_object* v_bs_2577_){
_start:
{
size_t v_sz_boxed_2578_; size_t v_i_boxed_2579_; lean_object* v_res_2580_; 
v_sz_boxed_2578_ = lean_unbox_usize(v_sz_2575_);
lean_dec(v_sz_2575_);
v_i_boxed_2579_ = lean_unbox_usize(v_i_2576_);
lean_dec(v_i_2576_);
v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(v___x_2573_, v_as_2574_, v_sz_boxed_2578_, v_i_boxed_2579_, v_bs_2577_);
lean_dec_ref(v_as_2574_);
lean_dec(v___x_2573_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object* v_lhs_2581_, lean_object* v_typeAscriptionTk_2582_, lean_object* v_rhs_2583_, lean_object* v_format_2584_){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2585_ = lean_unsigned_to_nat(3u);
v___x_2586_ = lean_mk_empty_array_with_capacity(v___x_2585_);
v___x_2587_ = lean_array_push(v___x_2586_, v_lhs_2581_);
v___x_2588_ = lean_array_push(v___x_2587_, v_typeAscriptionTk_2582_);
v___x_2589_ = lean_array_push(v___x_2588_, v_rhs_2583_);
v___x_2590_ = l_Lean_Fmt_Layouts_infixOperator(v___x_2589_, v_format_2584_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription___boxed(lean_object* v_lhs_2591_, lean_object* v_typeAscriptionTk_2592_, lean_object* v_rhs_2593_, lean_object* v_format_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_Fmt_Layouts_typeAscription(v_lhs_2591_, v_typeAscriptionTk_2592_, v_rhs_2593_, v_format_2594_);
lean_dec_ref(v_format_2594_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl(lean_object* v_x_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_obj_tag_nat(v_x_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl___boxed(lean_object* v_x_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl(v_x_2598_);
lean_dec_ref(v_x_2598_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(lean_object* v_t_2600_, lean_object* v_k_2601_){
_start:
{
if (lean_obj_tag(v_t_2600_) == 0)
{
uint8_t v_spacing_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_spacing_2602_ = lean_ctor_get_uint8(v_t_2600_, 0);
lean_dec_ref_known(v_t_2600_, 0);
v___x_2603_ = lean_box(v_spacing_2602_);
v___x_2604_ = lean_apply_1(v_k_2601_, v___x_2603_);
return v___x_2604_;
}
else
{
lean_object* v_sep_2605_; uint8_t v_unindentedRb_2606_; uint8_t v_stickynessKind_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_sep_2605_ = lean_ctor_get(v_t_2600_, 0);
lean_inc_ref(v_sep_2605_);
v_unindentedRb_2606_ = lean_ctor_get_uint8(v_t_2600_, sizeof(void*)*1);
v_stickynessKind_2607_ = lean_ctor_get_uint8(v_t_2600_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_2600_, 1);
v___x_2608_ = lean_box(v_unindentedRb_2606_);
v___x_2609_ = lean_box(v_stickynessKind_2607_);
v___x_2610_ = lean_apply_3(v_k_2601_, v_sep_2605_, v___x_2608_, v___x_2609_);
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(lean_object* v_motive_2611_, lean_object* v_ctorIdx_2612_, lean_object* v_t_2613_, lean_object* v_h_2614_, lean_object* v_k_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2613_, v_k_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___boxed(lean_object* v_motive_2617_, lean_object* v_ctorIdx_2618_, lean_object* v_t_2619_, lean_object* v_h_2620_, lean_object* v_k_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(v_motive_2617_, v_ctorIdx_2618_, v_t_2619_, v_h_2620_, v_k_2621_);
lean_dec(v_ctorIdx_2618_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim___redArg(lean_object* v_t_2623_, lean_object* v_dense_2624_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2623_, v_dense_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim(lean_object* v_motive_2626_, lean_object* v_t_2627_, lean_object* v_h_2628_, lean_object* v_dense_2629_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2627_, v_dense_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim___redArg(lean_object* v_t_2631_, lean_object* v_sparse_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2631_, v_sparse_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim(lean_object* v_motive_2634_, lean_object* v_t_2635_, lean_object* v_h_2636_, lean_object* v_sparse_2637_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2635_, v_sparse_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object* v_lb_2639_, lean_object* v_rb_2640_, uint8_t v_isBodyAligned_2641_, lean_object* v_bodyPseudoAligned_x3f_2642_, uint8_t v___x_2643_, lean_object* v_body_2644_){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v_doc_2651_; 
v___x_2645_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2644_);
v___x_2646_ = lean_unsigned_to_nat(3u);
v___x_2647_ = lean_mk_empty_array_with_capacity(v___x_2646_);
v___x_2648_ = lean_array_push(v___x_2647_, v_lb_2639_);
v___x_2649_ = lean_array_push(v___x_2648_, v___x_2645_);
v___x_2650_ = lean_array_push(v___x_2649_, v_rb_2640_);
v_doc_2651_ = l_Lean_Fmt_Layouts_atomic(v___x_2650_);
lean_dec_ref(v___x_2650_);
if (v_isBodyAligned_2641_ == 0)
{
if (lean_obj_tag(v_bodyPseudoAligned_x3f_2642_) == 1)
{
lean_object* v_val_2652_; uint8_t v___x_2653_; lean_object* v_doc_2654_; lean_object* v___x_2655_; 
v_val_2652_ = lean_ctor_get(v_bodyPseudoAligned_x3f_2642_, 0);
v___x_2653_ = lean_unbox(v_val_2652_);
v_doc_2654_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2651_, v___x_2653_);
v___x_2655_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2654_, v___x_2643_);
return v___x_2655_;
}
else
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2651_, v___x_2643_);
return v___x_2656_;
}
}
else
{
lean_object* v_doc_2657_; lean_object* v___x_2658_; 
v_doc_2657_ = l_Lean_Fmt_TaggedDoc_aligned(v_doc_2651_);
v___x_2658_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2657_, v___x_2643_);
return v___x_2658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0___boxed(lean_object* v_lb_2659_, lean_object* v_rb_2660_, lean_object* v_isBodyAligned_2661_, lean_object* v_bodyPseudoAligned_x3f_2662_, lean_object* v___x_2663_, lean_object* v_body_2664_){
_start:
{
uint8_t v_isBodyAligned_boxed_2665_; uint8_t v___x_608__boxed_2666_; lean_object* v_res_2667_; 
v_isBodyAligned_boxed_2665_ = lean_unbox(v_isBodyAligned_2661_);
v___x_608__boxed_2666_ = lean_unbox(v___x_2663_);
v_res_2667_ = l_Lean_Fmt_Layouts_bracketed___lam__0(v_lb_2659_, v_rb_2660_, v_isBodyAligned_boxed_2665_, v_bodyPseudoAligned_x3f_2662_, v___x_608__boxed_2666_, v_body_2664_);
lean_dec(v_bodyPseudoAligned_x3f_2662_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object* v_lb_2671_, lean_object* v_body_2672_, lean_object* v_rb_2673_, lean_object* v_format_2674_){
_start:
{
uint8_t v___x_2675_; 
v___x_2675_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2672_);
if (v___x_2675_ == 0)
{
lean_object* v_doc_2676_; uint8_t v___x_2677_; 
v_doc_2676_ = lean_ctor_get(v_body_2672_, 0);
v___x_2677_ = 1;
if (lean_obj_tag(v_format_2674_) == 0)
{
uint8_t v_spacing_2678_; 
v_spacing_2678_ = lean_ctor_get_uint8(v_format_2674_, 0);
lean_dec_ref_known(v_format_2674_, 0);
if (v_spacing_2678_ == 0)
{
uint8_t v_isBodyAligned_2679_; lean_object* v_bodyPseudoAligned_x3f_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v_f_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
lean_inc(v_doc_2676_);
v_isBodyAligned_2679_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2676_);
lean_inc_ref(v_body_2672_);
v_bodyPseudoAligned_x3f_2680_ = l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(v_body_2672_);
v___x_2681_ = lean_box(v_isBodyAligned_2679_);
v___x_2682_ = lean_box(v___x_2677_);
v_f_2683_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_bracketed___lam__0___boxed), 6, 5);
lean_closure_set(v_f_2683_, 0, v_lb_2671_);
lean_closure_set(v_f_2683_, 1, v_rb_2673_);
lean_closure_set(v_f_2683_, 2, v___x_2681_);
lean_closure_set(v_f_2683_, 3, v_bodyPseudoAligned_x3f_2680_);
lean_closure_set(v_f_2683_, 4, v___x_2682_);
v___x_2684_ = ((lean_object*)(l_Lean_Fmt_Layouts_bracketed___closed__0));
v___x_2685_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_body_2672_, v_f_2683_, v___x_2684_);
return v___x_2685_;
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2686_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2672_);
v___x_2687_ = lean_unsigned_to_nat(3u);
v___x_2688_ = lean_mk_empty_array_with_capacity(v___x_2687_);
v___x_2689_ = lean_array_push(v___x_2688_, v_lb_2671_);
v___x_2690_ = lean_array_push(v___x_2689_, v___x_2686_);
v___x_2691_ = lean_array_push(v___x_2690_, v_rb_2673_);
v___x_2692_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2691_);
lean_dec_ref(v___x_2691_);
return v___x_2692_;
}
}
else
{
lean_object* v_sep_2693_; uint8_t v_unindentedRb_2694_; uint8_t v_stickynessKind_2695_; lean_object* v_sparse_2697_; lean_object* v___y_2708_; lean_object* v___y_2711_; lean_object* v___y_2723_; lean_object* v___y_2735_; lean_object* v_body_2747_; uint8_t v___x_2748_; 
v_sep_2693_ = lean_ctor_get(v_format_2674_, 0);
lean_inc_ref(v_sep_2693_);
v_unindentedRb_2694_ = lean_ctor_get_uint8(v_format_2674_, sizeof(void*)*1);
v_stickynessKind_2695_ = lean_ctor_get_uint8(v_format_2674_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_format_2674_, 1);
v_body_2747_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_2672_);
v___x_2748_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2693_);
if (v___x_2748_ == 0)
{
uint8_t v___x_2749_; 
v___x_2749_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2747_);
if (v___x_2749_ == 0)
{
lean_object* v_doc_2750_; lean_object* v_doc_2751_; uint8_t v___x_2752_; 
v_doc_2750_ = lean_ctor_get(v_sep_2693_, 0);
v_doc_2751_ = lean_ctor_get(v_body_2747_, 0);
lean_inc(v_doc_2751_);
lean_dec_ref(v_body_2747_);
v___x_2752_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2750_);
if (v___x_2752_ == 0)
{
uint8_t v___x_2753_; 
v___x_2753_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2751_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_inc(v_doc_2750_);
v___x_2754_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2750_, v_doc_2751_);
v___x_2755_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2754_);
v___y_2735_ = v___x_2755_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2756_; 
lean_dec(v_doc_2751_);
lean_inc(v_doc_2750_);
v___x_2756_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2750_);
v___y_2735_ = v___x_2756_;
goto v___jp_2734_;
}
}
else
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2751_);
v___y_2735_ = v___x_2757_;
goto v___jp_2734_;
}
}
else
{
lean_dec_ref(v_body_2747_);
lean_inc_ref(v_sep_2693_);
v___y_2735_ = v_sep_2693_;
goto v___jp_2734_;
}
}
else
{
v___y_2735_ = v_body_2747_;
goto v___jp_2734_;
}
v___jp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v_stickyVariant_2704_; lean_object* v_nonStickyVariant_2705_; lean_object* v___x_2706_; 
lean_inc_ref(v_sparse_2697_);
v___x_2698_ = l_Lean_Fmt_TaggedDoc_aligned(v_sparse_2697_);
v___x_2699_ = lean_unsigned_to_nat(2u);
v___x_2700_ = lean_mk_empty_array_with_capacity(v___x_2699_);
v___x_2701_ = lean_array_push(v___x_2700_, v_sparse_2697_);
v___x_2702_ = lean_array_push(v___x_2701_, v___x_2698_);
v___x_2703_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2702_);
v_stickyVariant_2704_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_2703_, v___x_2677_);
lean_inc_ref(v_stickyVariant_2704_);
v_nonStickyVariant_2705_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_stickyVariant_2704_);
v___x_2706_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_2705_, v_stickyVariant_2704_, v_stickynessKind_2695_);
return v___x_2706_;
}
v___jp_2707_:
{
if (v_unindentedRb_2694_ == 0)
{
v_sparse_2697_ = v___y_2708_;
goto v___jp_2696_;
}
else
{
lean_object* v_sparse_2709_; 
v_sparse_2709_ = l_Lean_Fmt_TaggedDoc_unindented(v___y_2708_, v___x_2677_);
v_sparse_2697_ = v_sparse_2709_;
goto v___jp_2696_;
}
}
v___jp_2710_:
{
uint8_t v___x_2712_; 
v___x_2712_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_2711_);
if (v___x_2712_ == 0)
{
uint8_t v___x_2713_; 
v___x_2713_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rb_2673_);
if (v___x_2713_ == 0)
{
lean_object* v_doc_2714_; lean_object* v_doc_2715_; uint8_t v___x_2716_; 
v_doc_2714_ = lean_ctor_get(v___y_2711_, 0);
lean_inc(v_doc_2714_);
lean_dec_ref(v___y_2711_);
v_doc_2715_ = lean_ctor_get(v_rb_2673_, 0);
lean_inc(v_doc_2715_);
lean_dec_ref(v_rb_2673_);
v___x_2716_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2714_);
if (v___x_2716_ == 0)
{
uint8_t v___x_2717_; 
v___x_2717_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2715_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2714_, v_doc_2715_);
v___x_2719_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2718_);
v___y_2708_ = v___x_2719_;
goto v___jp_2707_;
}
else
{
lean_object* v___x_2720_; 
lean_dec(v_doc_2715_);
v___x_2720_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2714_);
v___y_2708_ = v___x_2720_;
goto v___jp_2707_;
}
}
else
{
lean_object* v___x_2721_; 
lean_dec(v_doc_2714_);
v___x_2721_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2715_);
v___y_2708_ = v___x_2721_;
goto v___jp_2707_;
}
}
else
{
lean_dec_ref(v_rb_2673_);
v___y_2708_ = v___y_2711_;
goto v___jp_2707_;
}
}
else
{
lean_dec_ref(v___y_2711_);
v___y_2708_ = v_rb_2673_;
goto v___jp_2707_;
}
}
v___jp_2722_:
{
uint8_t v___x_2724_; 
v___x_2724_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_2723_);
if (v___x_2724_ == 0)
{
uint8_t v___x_2725_; 
v___x_2725_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2693_);
if (v___x_2725_ == 0)
{
lean_object* v_doc_2726_; lean_object* v_doc_2727_; uint8_t v___x_2728_; 
v_doc_2726_ = lean_ctor_get(v___y_2723_, 0);
lean_inc(v_doc_2726_);
lean_dec_ref(v___y_2723_);
v_doc_2727_ = lean_ctor_get(v_sep_2693_, 0);
lean_inc(v_doc_2727_);
lean_dec_ref(v_sep_2693_);
v___x_2728_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2726_);
if (v___x_2728_ == 0)
{
uint8_t v___x_2729_; 
v___x_2729_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2727_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2726_, v_doc_2727_);
v___x_2731_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2730_);
v___y_2711_ = v___x_2731_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2732_; 
lean_dec(v_doc_2727_);
v___x_2732_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2726_);
v___y_2711_ = v___x_2732_;
goto v___jp_2710_;
}
}
else
{
lean_object* v___x_2733_; 
lean_dec(v_doc_2726_);
v___x_2733_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2727_);
v___y_2711_ = v___x_2733_;
goto v___jp_2710_;
}
}
else
{
lean_dec_ref(v_sep_2693_);
v___y_2711_ = v___y_2723_;
goto v___jp_2710_;
}
}
else
{
lean_dec_ref(v___y_2723_);
v___y_2711_ = v_sep_2693_;
goto v___jp_2710_;
}
}
v___jp_2734_:
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = l_Lean_Fmt_TaggedDoc_hardNested(v___y_2735_);
v___x_2737_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_lb_2671_);
if (v___x_2737_ == 0)
{
uint8_t v___x_2738_; 
v___x_2738_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2736_);
if (v___x_2738_ == 0)
{
lean_object* v_doc_2739_; lean_object* v_doc_2740_; uint8_t v___x_2741_; 
v_doc_2739_ = lean_ctor_get(v_lb_2671_, 0);
lean_inc(v_doc_2739_);
lean_dec_ref(v_lb_2671_);
v_doc_2740_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_doc_2740_);
lean_dec_ref(v___x_2736_);
v___x_2741_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2739_);
if (v___x_2741_ == 0)
{
uint8_t v___x_2742_; 
v___x_2742_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2740_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2739_, v_doc_2740_);
v___x_2744_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2743_);
v___y_2723_ = v___x_2744_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2745_; 
lean_dec(v_doc_2740_);
v___x_2745_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2739_);
v___y_2723_ = v___x_2745_;
goto v___jp_2722_;
}
}
else
{
lean_object* v___x_2746_; 
lean_dec(v_doc_2739_);
v___x_2746_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2740_);
v___y_2723_ = v___x_2746_;
goto v___jp_2722_;
}
}
else
{
lean_dec_ref(v___x_2736_);
v___y_2723_ = v_lb_2671_;
goto v___jp_2722_;
}
}
else
{
lean_dec_ref(v_lb_2671_);
v___y_2723_ = v___x_2736_;
goto v___jp_2722_;
}
}
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec_ref(v_format_2674_);
lean_dec_ref(v_body_2672_);
v___x_2758_ = lean_unsigned_to_nat(2u);
v___x_2759_ = lean_mk_empty_array_with_capacity(v___x_2758_);
v___x_2760_ = lean_array_push(v___x_2759_, v_lb_2671_);
v___x_2761_ = lean_array_push(v___x_2760_, v_rb_2673_);
v___x_2762_ = l_Lean_Fmt_Layouts_atomic(v___x_2761_);
lean_dec_ref(v___x_2761_);
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object* v_lbTk_2765_, lean_object* v_body_2766_, lean_object* v_rbTk_2767_){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_2769_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2765_, v_body_2766_, v_rbTk_2767_, v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0(void){
_start:
{
uint8_t v___x_2770_; uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2770_ = 1;
v___x_2771_ = 1;
v___x_2772_ = l_Lean_Fmt_TaggedDoc_break;
v___x_2773_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*1, v___x_2771_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*1 + 1, v___x_2770_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object* v_lbTk_2774_, lean_object* v_seq_2775_, lean_object* v_rbTk_2776_){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_obj_once(&l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0, &l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0);
v___x_2778_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2774_, v_seq_2775_, v_rbTk_2776_, v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(uint8_t v_isComplex_2779_, lean_object* v_subAlts_2780_){
_start:
{
if (v_isComplex_2779_ == 0)
{
uint8_t v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = 1;
v___x_2782_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_subAlts_2780_, v___x_2781_);
return v___x_2782_;
}
else
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_Fmt_Layouts_lines(v_subAlts_2780_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts___boxed(lean_object* v_isComplex_2784_, lean_object* v_subAlts_2785_){
_start:
{
uint8_t v_isComplex_boxed_2786_; lean_object* v_res_2787_; 
v_isComplex_boxed_2786_ = lean_unbox(v_isComplex_2784_);
v_res_2787_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_boxed_2786_, v_subAlts_2785_);
lean_dec_ref(v_subAlts_2785_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t v_sz_2788_, size_t v_i_2789_, lean_object* v_bs_2790_){
_start:
{
uint8_t v___x_2791_; 
v___x_2791_ = lean_usize_dec_lt(v_i_2789_, v_sz_2788_);
if (v___x_2791_ == 0)
{
return v_bs_2790_;
}
else
{
lean_object* v_v_2792_; lean_object* v___x_2793_; lean_object* v_bs_x27_2794_; lean_object* v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; lean_object* v___x_2798_; 
v_v_2792_ = lean_array_uget(v_bs_2790_, v_i_2789_);
v___x_2793_ = lean_unsigned_to_nat(0u);
v_bs_x27_2794_ = lean_array_uset(v_bs_2790_, v_i_2789_, v___x_2793_);
v___x_2795_ = l_Lean_Fmt_TaggedDoc_nested(v_v_2792_);
v___x_2796_ = ((size_t)1ULL);
v___x_2797_ = lean_usize_add(v_i_2789_, v___x_2796_);
v___x_2798_ = lean_array_uset(v_bs_x27_2794_, v_i_2789_, v___x_2795_);
v_i_2789_ = v___x_2797_;
v_bs_2790_ = v___x_2798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object* v_sz_2800_, lean_object* v_i_2801_, lean_object* v_bs_2802_){
_start:
{
size_t v_sz_boxed_2803_; size_t v_i_boxed_2804_; lean_object* v_res_2805_; 
v_sz_boxed_2803_ = lean_unbox_usize(v_sz_2800_);
lean_dec(v_sz_2800_);
v_i_boxed_2804_ = lean_unbox_usize(v_i_2801_);
lean_dec(v_i_2801_);
v_res_2805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_boxed_2803_, v_i_boxed_2804_, v_bs_2802_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object* v_subAlts_2806_, lean_object* v_arrowTk_2807_, lean_object* v_rhs_2808_, uint8_t v_isComplex_2809_){
_start:
{
uint8_t v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; uint8_t v___y_2853_; uint8_t v___x_2867_; 
v___x_2867_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_arrowTk_2807_);
if (v___x_2867_ == 0)
{
v___y_2853_ = v___x_2867_;
goto v___jp_2852_;
}
else
{
uint8_t v___x_2868_; 
v___x_2868_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_2808_);
if (v___x_2868_ == 0)
{
v___y_2853_ = v___x_2868_;
goto v___jp_2852_;
}
else
{
lean_object* v_subAlts_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec_ref(v_rhs_2808_);
lean_dec_ref(v_arrowTk_2807_);
v_subAlts_2869_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_2809_, v_subAlts_2806_);
lean_dec_ref(v_subAlts_2806_);
lean_inc_ref(v_subAlts_2869_);
v___x_2870_ = l_Lean_Fmt_TaggedDoc_flattened(v_subAlts_2869_);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v_subAlts_2869_);
return v___x_2871_;
}
}
v___jp_2810_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v_lhs_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v_nonStickyDoc_2829_; lean_object* v_flat_2830_; lean_object* v___x_2831_; 
v___x_2814_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_2809_, v___y_2813_);
lean_dec_ref(v___y_2813_);
v___x_2815_ = lean_unsigned_to_nat(2u);
v___x_2816_ = lean_mk_empty_array_with_capacity(v___x_2815_);
lean_inc_ref_n(v___x_2816_, 2);
v___x_2817_ = lean_array_push(v___x_2816_, v___x_2814_);
v___x_2818_ = lean_array_push(v___x_2817_, v_arrowTk_2807_);
v_lhs_2819_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2818_);
lean_dec_ref(v___x_2818_);
v___x_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2820_, 0, v_lhs_2819_);
v___x_2821_ = l_Lean_Fmt_TaggedDoc_nl;
lean_inc_ref(v___y_2812_);
v___x_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
lean_ctor_set(v___x_2822_, 1, v___y_2812_);
lean_inc_ref(v___x_2820_);
v___x_2823_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2820_, v___x_2822_);
v___x_2824_ = lean_box(0);
lean_inc_ref(v_rhs_2808_);
v___x_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2825_, 0, v_rhs_2808_);
v___x_2826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
lean_ctor_set(v___x_2826_, 2, v___x_2824_);
v___x_2827_ = lean_array_push(v___x_2816_, v___x_2823_);
v___x_2828_ = lean_array_push(v___x_2827_, v___x_2826_);
v_nonStickyDoc_2829_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2828_);
lean_dec_ref(v___x_2828_);
lean_inc_ref(v_nonStickyDoc_2829_);
v_flat_2830_ = l_Lean_Fmt_TaggedDoc_flattened(v_nonStickyDoc_2829_);
v___x_2831_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_2808_);
if (lean_obj_tag(v___x_2831_) == 1)
{
lean_object* v_val_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2850_; 
v_val_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2850_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_val_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2850_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v_stickyVariant_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v_stickyVariant_2836_ = lean_ctor_get(v_val_2832_, 0);
v___x_2837_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v___y_2812_);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v___y_2812_);
v___x_2839_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2820_, v___x_2838_);
lean_inc_ref(v_stickyVariant_2836_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v_stickyVariant_2836_);
v___x_2841_ = v___x_2834_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_stickyVariant_2836_);
v___x_2841_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v_stickyDoc_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2824_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
lean_ctor_set(v___x_2842_, 2, v___x_2824_);
v___x_2843_ = lean_array_push(v___x_2816_, v___x_2839_);
v___x_2844_ = lean_array_push(v___x_2843_, v___x_2842_);
v_stickyDoc_2845_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2844_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_2832_, v___y_2811_);
lean_dec(v_val_2832_);
v___x_2847_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_2829_, v_stickyDoc_2845_, v___x_2846_);
lean_dec(v___x_2846_);
v___x_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2848_, 0, v_flat_2830_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
return v___x_2848_;
}
}
}
else
{
lean_object* v___x_2851_; 
lean_dec(v___x_2831_);
lean_dec_ref_known(v___x_2820_, 1);
lean_dec_ref(v___x_2816_);
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_flat_2830_);
lean_ctor_set(v___x_2851_, 1, v_nonStickyDoc_2829_);
return v___x_2851_;
}
}
v___jp_2852_:
{
lean_object* v___x_2854_; size_t v_sz_2855_; size_t v___x_2856_; lean_object* v_subAlts_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2854_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_sz_2855_ = lean_array_size(v_subAlts_2806_);
v___x_2856_ = ((size_t)0ULL);
v_subAlts_2857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_2855_, v___x_2856_, v_subAlts_2806_);
v___x_2858_ = lean_array_get_size(v_subAlts_2857_);
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = lean_nat_sub(v___x_2858_, v___x_2859_);
v___x_2861_ = lean_nat_dec_lt(v___x_2860_, v___x_2858_);
if (v___x_2861_ == 0)
{
lean_dec(v___x_2860_);
v___y_2811_ = v___y_2853_;
v___y_2812_ = v___x_2854_;
v___y_2813_ = v_subAlts_2857_;
goto v___jp_2810_;
}
else
{
lean_object* v_v_2862_; lean_object* v___x_2863_; lean_object* v_xs_x27_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_v_2862_ = lean_array_fget(v_subAlts_2857_, v___x_2860_);
v___x_2863_ = lean_box(0);
v_xs_x27_2864_ = lean_array_fset(v_subAlts_2857_, v___x_2860_, v___x_2863_);
v___x_2865_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2862_);
v___x_2866_ = lean_array_fset(v_xs_x27_2864_, v___x_2860_, v___x_2865_);
lean_dec(v___x_2860_);
v___y_2811_ = v___y_2853_;
v___y_2812_ = v___x_2854_;
v___y_2813_ = v___x_2866_;
goto v___jp_2810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt___boxed(lean_object* v_subAlts_2872_, lean_object* v_arrowTk_2873_, lean_object* v_rhs_2874_, lean_object* v_isComplex_2875_){
_start:
{
uint8_t v_isComplex_boxed_2876_; lean_object* v_res_2877_; 
v_isComplex_boxed_2876_ = lean_unbox(v_isComplex_2875_);
v_res_2877_ = l_Lean_Fmt_Layouts_alt(v_subAlts_2872_, v_arrowTk_2873_, v_rhs_2874_, v_isComplex_boxed_2876_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t v_sz_2878_, size_t v_i_2879_, lean_object* v_bs_2880_){
_start:
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_usize_dec_lt(v_i_2879_, v_sz_2878_);
if (v___x_2881_ == 0)
{
return v_bs_2880_;
}
else
{
lean_object* v_v_2882_; lean_object* v_nonFlat_2883_; lean_object* v___x_2884_; lean_object* v_bs_x27_2885_; size_t v___x_2886_; size_t v___x_2887_; lean_object* v___x_2888_; 
v_v_2882_ = lean_array_uget_borrowed(v_bs_2880_, v_i_2879_);
v_nonFlat_2883_ = lean_ctor_get(v_v_2882_, 1);
lean_inc_ref(v_nonFlat_2883_);
v___x_2884_ = lean_unsigned_to_nat(0u);
v_bs_x27_2885_ = lean_array_uset(v_bs_2880_, v_i_2879_, v___x_2884_);
v___x_2886_ = ((size_t)1ULL);
v___x_2887_ = lean_usize_add(v_i_2879_, v___x_2886_);
v___x_2888_ = lean_array_uset(v_bs_x27_2885_, v_i_2879_, v_nonFlat_2883_);
v_i_2879_ = v___x_2887_;
v_bs_2880_ = v___x_2888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object* v_sz_2890_, lean_object* v_i_2891_, lean_object* v_bs_2892_){
_start:
{
size_t v_sz_boxed_2893_; size_t v_i_boxed_2894_; lean_object* v_res_2895_; 
v_sz_boxed_2893_ = lean_unbox_usize(v_sz_2890_);
lean_dec(v_sz_2890_);
v_i_boxed_2894_ = lean_unbox_usize(v_i_2891_);
lean_dec(v_i_2891_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_boxed_2893_, v_i_boxed_2894_, v_bs_2892_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1(lean_object* v_as_2896_, size_t v_sz_2897_, size_t v_i_2898_, lean_object* v_b_2899_){
_start:
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_usize_dec_lt(v_i_2898_, v_sz_2897_);
if (v___x_2900_ == 0)
{
return v_b_2899_;
}
else
{
lean_object* v_snd_2901_; lean_object* v_fst_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2947_; 
v_snd_2901_ = lean_ctor_get(v_b_2899_, 1);
v_fst_2902_ = lean_ctor_get(v_b_2899_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_b_2899_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2904_ = v_b_2899_;
v_isShared_2905_ = v_isSharedCheck_2947_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_snd_2901_);
lean_inc(v_fst_2902_);
lean_dec(v_b_2899_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2947_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v_fst_2906_; lean_object* v_snd_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2946_; 
v_fst_2906_ = lean_ctor_get(v_snd_2901_, 0);
v_snd_2907_ = lean_ctor_get(v_snd_2901_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_snd_2901_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2909_ = v_snd_2901_;
v_isShared_2910_ = v_isSharedCheck_2946_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_snd_2907_);
lean_inc(v_fst_2906_);
lean_dec(v_snd_2901_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2946_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_a_2911_; lean_object* v___y_2913_; 
v_a_2911_ = lean_array_uget_borrowed(v_as_2896_, v_i_2898_);
if (lean_obj_tag(v_fst_2906_) == 0)
{
lean_object* v_flatSuffix_2939_; 
v_flatSuffix_2939_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2913_ = v_flatSuffix_2939_;
goto v___jp_2912_;
}
else
{
lean_object* v_val_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_val_2940_ = lean_ctor_get(v_fst_2906_, 0);
lean_inc(v_val_2940_);
lean_dec_ref_known(v_fst_2906_, 1);
v___x_2941_ = lean_unsigned_to_nat(2u);
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2941_);
v___x_2943_ = lean_array_push(v___x_2942_, v_val_2940_);
lean_inc(v_fst_2902_);
v___x_2944_ = lean_array_push(v___x_2943_, v_fst_2902_);
v___x_2945_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2944_);
v___y_2913_ = v___x_2945_;
goto v___jp_2912_;
}
v___jp_2912_:
{
lean_object* v_flat_2914_; lean_object* v_nonFlat_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2931_; 
v_flat_2914_ = lean_ctor_get(v_a_2911_, 0);
v_nonFlat_2915_ = lean_ctor_get(v_a_2911_, 1);
v___x_2916_ = lean_unsigned_to_nat(2u);
v___x_2917_ = lean_mk_empty_array_with_capacity(v___x_2916_);
lean_inc_ref(v_nonFlat_2915_);
lean_inc_ref_n(v___x_2917_, 2);
v___x_2918_ = lean_array_push(v___x_2917_, v_nonFlat_2915_);
v___x_2919_ = lean_array_push(v___x_2918_, v___y_2913_);
v___x_2920_ = l_Lean_Fmt_Layouts_lines(v___x_2919_);
lean_dec_ref(v___x_2919_);
lean_inc_ref(v_flat_2914_);
v___x_2921_ = lean_array_push(v___x_2917_, v_flat_2914_);
lean_inc_ref(v___x_2921_);
v___x_2922_ = lean_array_push(v___x_2921_, v_snd_2907_);
v___x_2923_ = l_Lean_Fmt_Layouts_lines(v___x_2922_);
lean_dec_ref(v___x_2922_);
v___x_2924_ = lean_array_push(v___x_2917_, v___x_2923_);
lean_inc_ref(v___x_2920_);
v___x_2925_ = lean_array_push(v___x_2924_, v___x_2920_);
v___x_2926_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2925_);
v___x_2927_ = lean_array_push(v___x_2921_, v_fst_2902_);
v___x_2928_ = l_Lean_Fmt_Layouts_lines(v___x_2927_);
lean_dec_ref(v___x_2927_);
v___x_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2920_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v___x_2926_);
lean_ctor_set(v___x_2909_, 0, v___x_2929_);
v___x_2931_ = v___x_2909_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2929_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v___x_2926_);
v___x_2931_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
lean_object* v___x_2933_; 
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 1, v___x_2931_);
lean_ctor_set(v___x_2904_, 0, v___x_2928_);
v___x_2933_ = v___x_2904_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2928_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
size_t v___x_2934_; size_t v___x_2935_; 
v___x_2934_ = ((size_t)1ULL);
v___x_2935_ = lean_usize_add(v_i_2898_, v___x_2934_);
v_i_2898_ = v___x_2935_;
v_b_2899_ = v___x_2933_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object* v_as_2948_, lean_object* v_sz_2949_, lean_object* v_i_2950_, lean_object* v_b_2951_){
_start:
{
size_t v_sz_boxed_2952_; size_t v_i_boxed_2953_; lean_object* v_res_2954_; 
v_sz_boxed_2952_ = lean_unbox_usize(v_sz_2949_);
lean_dec(v_sz_2949_);
v_i_boxed_2953_ = lean_unbox_usize(v_i_2950_);
lean_dec(v_i_2950_);
v_res_2954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1(v_as_2948_, v_sz_boxed_2952_, v_i_boxed_2953_, v_b_2951_);
lean_dec_ref(v_as_2948_);
return v_res_2954_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_alts___closed__0(void){
_start:
{
lean_object* v_flatSuffix_2955_; lean_object* v_middle_x3f_2956_; lean_object* v___x_2957_; 
v_flatSuffix_2955_ = l_Lean_Fmt_TaggedDoc_empty;
v_middle_x3f_2956_ = lean_box(0);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v_middle_x3f_2956_);
lean_ctor_set(v___x_2957_, 1, v_flatSuffix_2955_);
return v___x_2957_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_alts___closed__1(void){
_start:
{
lean_object* v___x_2958_; lean_object* v_flatSuffix_2959_; lean_object* v___x_2960_; 
v___x_2958_ = lean_obj_once(&l_Lean_Fmt_Layouts_alts___closed__0, &l_Lean_Fmt_Layouts_alts___closed__0_once, _init_l_Lean_Fmt_Layouts_alts___closed__0);
v_flatSuffix_2959_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v_flatSuffix_2959_);
lean_ctor_set(v___x_2960_, 1, v___x_2958_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts(lean_object* v_alts_2961_, uint8_t v_allowFlattenedAlts_2962_){
_start:
{
if (v_allowFlattenedAlts_2962_ == 0)
{
size_t v_sz_2963_; size_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_sz_2963_ = lean_array_size(v_alts_2961_);
v___x_2964_ = ((size_t)0ULL);
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_2963_, v___x_2964_, v_alts_2961_);
v___x_2966_ = l_Lean_Fmt_Layouts_lines(v___x_2965_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_2966_);
return v___x_2967_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; size_t v_sz_2970_; size_t v___x_2971_; lean_object* v___x_2972_; lean_object* v_snd_2973_; lean_object* v_snd_2974_; lean_object* v___x_2975_; 
v___x_2968_ = l_Array_reverse___redArg(v_alts_2961_);
v___x_2969_ = lean_obj_once(&l_Lean_Fmt_Layouts_alts___closed__1, &l_Lean_Fmt_Layouts_alts___closed__1_once, _init_l_Lean_Fmt_Layouts_alts___closed__1);
v_sz_2970_ = lean_array_size(v___x_2968_);
v___x_2971_ = ((size_t)0ULL);
v___x_2972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Layouts_alts_spec__1(v___x_2968_, v_sz_2970_, v___x_2971_, v___x_2969_);
lean_dec_ref(v___x_2968_);
v_snd_2973_ = lean_ctor_get(v___x_2972_, 1);
lean_inc(v_snd_2973_);
lean_dec_ref(v___x_2972_);
v_snd_2974_ = lean_ctor_get(v_snd_2973_, 1);
lean_inc(v_snd_2974_);
lean_dec(v_snd_2973_);
v___x_2975_ = l_Lean_Fmt_TaggedDoc_withPosition(v_snd_2974_);
return v___x_2975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts___boxed(lean_object* v_alts_2976_, lean_object* v_allowFlattenedAlts_2977_){
_start:
{
uint8_t v_allowFlattenedAlts_boxed_2978_; lean_object* v_res_2979_; 
v_allowFlattenedAlts_boxed_2978_ = lean_unbox(v_allowFlattenedAlts_2977_);
v_res_2979_ = l_Lean_Fmt_Layouts_alts(v_alts_2976_, v_allowFlattenedAlts_boxed_2978_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl(uint8_t v_x_2980_){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = lean_box(v_x_2980_);
v___x_2982_ = lean_obj_tag_nat(v___x_2981_);
lean_dec(v___x_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl___boxed(lean_object* v_x_2983_){
_start:
{
uint8_t v_x_4__boxed_2984_; lean_object* v_res_2985_; 
v_x_4__boxed_2984_ = lean_unbox(v_x_2983_);
v_res_2985_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl(v_x_4__boxed_2984_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(lean_object* v_k_2986_){
_start:
{
lean_inc(v_k_2986_);
return v_k_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg___boxed(lean_object* v_k_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(v_k_2987_);
lean_dec(v_k_2987_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(lean_object* v_motive_2989_, lean_object* v_ctorIdx_2990_, uint8_t v_t_2991_, lean_object* v_h_2992_, lean_object* v_k_2993_){
_start:
{
lean_inc(v_k_2993_);
return v_k_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___boxed(lean_object* v_motive_2994_, lean_object* v_ctorIdx_2995_, lean_object* v_t_2996_, lean_object* v_h_2997_, lean_object* v_k_2998_){
_start:
{
uint8_t v_t_boxed_2999_; lean_object* v_res_3000_; 
v_t_boxed_2999_ = lean_unbox(v_t_2996_);
v_res_3000_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(v_motive_2994_, v_ctorIdx_2995_, v_t_boxed_2999_, v_h_2997_, v_k_2998_);
lean_dec(v_k_2998_);
lean_dec(v_ctorIdx_2995_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(lean_object* v_sticky_3001_){
_start:
{
lean_inc(v_sticky_3001_);
return v_sticky_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(v_sticky_3002_);
lean_dec(v_sticky_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(lean_object* v_motive_3004_, uint8_t v_t_3005_, lean_object* v_h_3006_, lean_object* v_sticky_3007_){
_start:
{
lean_inc(v_sticky_3007_);
return v_sticky_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___boxed(lean_object* v_motive_3008_, lean_object* v_t_3009_, lean_object* v_h_3010_, lean_object* v_sticky_3011_){
_start:
{
uint8_t v_t_boxed_3012_; lean_object* v_res_3013_; 
v_t_boxed_3012_ = lean_unbox(v_t_3009_);
v_res_3013_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(v_motive_3008_, v_t_boxed_3012_, v_h_3010_, v_sticky_3011_);
lean_dec(v_sticky_3011_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3014_){
_start:
{
lean_inc(v_nonSticky_3014_);
return v_nonSticky_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(v_nonSticky_3015_);
lean_dec(v_nonSticky_3015_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(lean_object* v_motive_3017_, uint8_t v_t_3018_, lean_object* v_h_3019_, lean_object* v_nonSticky_3020_){
_start:
{
lean_inc(v_nonSticky_3020_);
return v_nonSticky_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___boxed(lean_object* v_motive_3021_, lean_object* v_t_3022_, lean_object* v_h_3023_, lean_object* v_nonSticky_3024_){
_start:
{
uint8_t v_t_boxed_3025_; lean_object* v_res_3026_; 
v_t_boxed_3025_ = lean_unbox(v_t_3022_);
v_res_3026_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(v_motive_3021_, v_t_boxed_3025_, v_h_3023_, v_nonSticky_3024_);
lean_dec(v_nonSticky_3024_);
return v_res_3026_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3028_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object* v_keywordTk_3030_, lean_object* v_seq_3031_, uint8_t v_format_3032_){
_start:
{
lean_object* v___x_3033_; uint8_t v___x_3034_; lean_object* v_doc_3035_; 
v___x_3033_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3034_ = 1;
v_doc_3035_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_keywordTk_3030_, v___x_3033_, v_seq_3031_, v___x_3034_);
if (v_format_3032_ == 0)
{
lean_object* v___x_3036_; uint8_t v___x_3037_; lean_object* v___x_3038_; 
lean_inc_ref(v_doc_3035_);
v___x_3036_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3035_);
v___x_3037_ = 1;
v___x_3038_ = l_Lean_Fmt_TaggedDoc_sticky(v___x_3036_, v_doc_3035_, v___x_3037_);
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3035_);
return v___x_3039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___boxed(lean_object* v_keywordTk_3040_, lean_object* v_seq_3041_, lean_object* v_format_3042_){
_start:
{
uint8_t v_format_boxed_3043_; lean_object* v_res_3044_; 
v_format_boxed_3043_ = lean_unbox(v_format_3042_);
v_res_3044_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_keywordTk_3040_, v_seq_3041_, v_format_boxed_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl(uint8_t v_x_3045_){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_box(v_x_3045_);
v___x_3047_ = lean_obj_tag_nat(v___x_3046_);
lean_dec(v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl___boxed(lean_object* v_x_3048_){
_start:
{
uint8_t v_x_4__boxed_3049_; lean_object* v_res_3050_; 
v_x_4__boxed_3049_ = lean_unbox(v_x_3048_);
v_res_3050_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl(v_x_4__boxed_3049_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(lean_object* v_k_3051_){
_start:
{
lean_inc(v_k_3051_);
return v_k_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg___boxed(lean_object* v_k_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(v_k_3052_);
lean_dec(v_k_3052_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(lean_object* v_motive_3054_, lean_object* v_ctorIdx_3055_, uint8_t v_t_3056_, lean_object* v_h_3057_, lean_object* v_k_3058_){
_start:
{
lean_inc(v_k_3058_);
return v_k_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___boxed(lean_object* v_motive_3059_, lean_object* v_ctorIdx_3060_, lean_object* v_t_3061_, lean_object* v_h_3062_, lean_object* v_k_3063_){
_start:
{
uint8_t v_t_boxed_3064_; lean_object* v_res_3065_; 
v_t_boxed_3064_ = lean_unbox(v_t_3061_);
v_res_3065_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(v_motive_3059_, v_ctorIdx_3060_, v_t_boxed_3064_, v_h_3062_, v_k_3063_);
lean_dec(v_k_3063_);
lean_dec(v_ctorIdx_3060_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(lean_object* v_sticky_3066_){
_start:
{
lean_inc(v_sticky_3066_);
return v_sticky_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(v_sticky_3067_);
lean_dec(v_sticky_3067_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(lean_object* v_motive_3069_, uint8_t v_t_3070_, lean_object* v_h_3071_, lean_object* v_sticky_3072_){
_start:
{
lean_inc(v_sticky_3072_);
return v_sticky_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___boxed(lean_object* v_motive_3073_, lean_object* v_t_3074_, lean_object* v_h_3075_, lean_object* v_sticky_3076_){
_start:
{
uint8_t v_t_boxed_3077_; lean_object* v_res_3078_; 
v_t_boxed_3077_ = lean_unbox(v_t_3074_);
v_res_3078_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(v_motive_3073_, v_t_boxed_3077_, v_h_3075_, v_sticky_3076_);
lean_dec(v_sticky_3076_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3079_){
_start:
{
lean_inc(v_nonSticky_3079_);
return v_nonSticky_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(v_nonSticky_3080_);
lean_dec(v_nonSticky_3080_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(lean_object* v_motive_3082_, uint8_t v_t_3083_, lean_object* v_h_3084_, lean_object* v_nonSticky_3085_){
_start:
{
lean_inc(v_nonSticky_3085_);
return v_nonSticky_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___boxed(lean_object* v_motive_3086_, lean_object* v_t_3087_, lean_object* v_h_3088_, lean_object* v_nonSticky_3089_){
_start:
{
uint8_t v_t_boxed_3090_; lean_object* v_res_3091_; 
v_t_boxed_3090_ = lean_unbox(v_t_3087_);
v_res_3091_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(v_motive_3086_, v_t_boxed_3090_, v_h_3088_, v_nonSticky_3089_);
lean_dec(v_nonSticky_3089_);
return v_res_3091_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3093_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v___x_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object* v_keyword_3095_, lean_object* v_term_3096_, uint8_t v_format_3097_){
_start:
{
uint8_t v___x_3098_; 
v___x_3098_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_term_3096_);
if (v___x_3098_ == 0)
{
uint8_t v___x_3099_; lean_object* v___y_3101_; uint8_t v___x_3133_; 
v___x_3099_ = 1;
lean_inc_ref(v_term_3096_);
v___x_3133_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_term_3096_, v___x_3098_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_inc_ref(v_keyword_3095_);
v___x_3134_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3095_);
v___x_3135_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_term_3096_);
v___x_3136_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3134_, v___x_3135_, v_term_3096_, v___x_3099_);
v___x_3137_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3136_);
v___y_3101_ = v___x_3137_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_inc_ref(v_keyword_3095_);
v___x_3138_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3095_);
v___x_3139_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v_term_3096_);
v___x_3140_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3138_, v___x_3139_, v_term_3096_, v___x_3099_);
v___y_3101_ = v___x_3140_;
goto v___jp_3100_;
}
v___jp_3100_:
{
if (v_format_3097_ == 0)
{
lean_object* v___x_3102_; 
lean_inc_ref(v_term_3096_);
v___x_3102_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_term_3096_);
if (lean_obj_tag(v___x_3102_) == 1)
{
lean_object* v_val_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3127_; 
v_val_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3127_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_val_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3127_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
uint8_t v_kind_3107_; 
v_kind_3107_ = lean_ctor_get_uint8(v_val_3103_, sizeof(void*)*1);
lean_dec(v_val_3103_);
if (v_kind_3107_ == 1)
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3108_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3095_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3108_);
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3111_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3112_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3110_, v___x_3111_);
v___x_3113_ = lean_box(0);
v___x_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3114_, 0, v_term_3096_);
v___x_3115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
lean_ctor_set(v___x_3115_, 2, v___x_3113_);
v___x_3116_ = lean_unsigned_to_nat(2u);
v___x_3117_ = lean_mk_empty_array_with_capacity(v___x_3116_);
v___x_3118_ = lean_array_push(v___x_3117_, v___x_3112_);
v___x_3119_ = lean_array_push(v___x_3118_, v___x_3115_);
v___x_3120_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3119_);
lean_dec_ref(v___x_3119_);
v___x_3121_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3101_, v___x_3120_, v_kind_3107_);
return v___x_3121_;
}
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_del_object(v___x_3105_);
v___x_3123_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3095_);
v___x_3124_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3125_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3123_, v___x_3124_, v_term_3096_, v___x_3099_);
v___x_3126_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3101_, v___x_3125_, v_kind_3107_);
return v___x_3126_;
}
}
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; 
lean_dec(v___x_3102_);
v___x_3128_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3095_);
v___x_3129_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3130_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3128_, v___x_3129_, v_term_3096_, v___x_3099_);
v___x_3131_ = 0;
v___x_3132_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3101_, v___x_3130_, v___x_3131_);
return v___x_3132_;
}
}
else
{
lean_dec_ref(v_term_3096_);
lean_dec_ref(v_keyword_3095_);
return v___y_3101_;
}
}
}
else
{
uint8_t v___x_3141_; 
lean_dec_ref(v_term_3096_);
v___x_3141_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keyword_3095_);
if (v___x_3141_ == 0)
{
if (v_format_3097_ == 0)
{
lean_object* v___x_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; 
lean_inc_ref(v_keyword_3095_);
v___x_3142_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3095_);
v___x_3143_ = 0;
v___x_3144_ = l_Lean_Fmt_TaggedDoc_sticky(v_keyword_3095_, v___x_3142_, v___x_3143_);
return v___x_3144_;
}
else
{
return v_keyword_3095_;
}
}
else
{
lean_object* v___x_3145_; 
lean_dec_ref(v_keyword_3095_);
v___x_3145_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___boxed(lean_object* v_keyword_3146_, lean_object* v_term_3147_, lean_object* v_format_3148_){
_start:
{
uint8_t v_format_boxed_3149_; lean_object* v_res_3150_; 
v_format_boxed_3149_ = lean_unbox(v_format_3148_);
v_res_3150_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3146_, v_term_3147_, v_format_boxed_3149_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl(uint8_t v_x_3151_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = lean_box(v_x_3151_);
v___x_3153_ = lean_obj_tag_nat(v___x_3152_);
lean_dec(v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl___boxed(lean_object* v_x_3154_){
_start:
{
uint8_t v_x_4__boxed_3155_; lean_object* v_res_3156_; 
v_x_4__boxed_3155_ = lean_unbox(v_x_3154_);
v_res_3156_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl(v_x_4__boxed_3155_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(lean_object* v_k_3157_){
_start:
{
lean_inc(v_k_3157_);
return v_k_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg___boxed(lean_object* v_k_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(v_k_3158_);
lean_dec(v_k_3158_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(lean_object* v_motive_3160_, lean_object* v_ctorIdx_3161_, uint8_t v_t_3162_, lean_object* v_h_3163_, lean_object* v_k_3164_){
_start:
{
lean_inc(v_k_3164_);
return v_k_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___boxed(lean_object* v_motive_3165_, lean_object* v_ctorIdx_3166_, lean_object* v_t_3167_, lean_object* v_h_3168_, lean_object* v_k_3169_){
_start:
{
uint8_t v_t_boxed_3170_; lean_object* v_res_3171_; 
v_t_boxed_3170_ = lean_unbox(v_t_3167_);
v_res_3171_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(v_motive_3165_, v_ctorIdx_3166_, v_t_boxed_3170_, v_h_3168_, v_k_3169_);
lean_dec(v_k_3169_);
lean_dec(v_ctorIdx_3166_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(lean_object* v_sticky_3172_){
_start:
{
lean_inc(v_sticky_3172_);
return v_sticky_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(v_sticky_3173_);
lean_dec(v_sticky_3173_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(lean_object* v_motive_3175_, uint8_t v_t_3176_, lean_object* v_h_3177_, lean_object* v_sticky_3178_){
_start:
{
lean_inc(v_sticky_3178_);
return v_sticky_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___boxed(lean_object* v_motive_3179_, lean_object* v_t_3180_, lean_object* v_h_3181_, lean_object* v_sticky_3182_){
_start:
{
uint8_t v_t_boxed_3183_; lean_object* v_res_3184_; 
v_t_boxed_3183_ = lean_unbox(v_t_3180_);
v_res_3184_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(v_motive_3179_, v_t_boxed_3183_, v_h_3181_, v_sticky_3182_);
lean_dec(v_sticky_3182_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3185_){
_start:
{
lean_inc(v_nonSticky_3185_);
return v_nonSticky_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(v_nonSticky_3186_);
lean_dec(v_nonSticky_3186_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(lean_object* v_motive_3188_, uint8_t v_t_3189_, lean_object* v_h_3190_, lean_object* v_nonSticky_3191_){
_start:
{
lean_inc(v_nonSticky_3191_);
return v_nonSticky_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___boxed(lean_object* v_motive_3192_, lean_object* v_t_3193_, lean_object* v_h_3194_, lean_object* v_nonSticky_3195_){
_start:
{
uint8_t v_t_boxed_3196_; lean_object* v_res_3197_; 
v_t_boxed_3196_ = lean_unbox(v_t_3193_);
v_res_3197_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(v_motive_3192_, v_t_boxed_3196_, v_h_3194_, v_nonSticky_3195_);
lean_dec(v_nonSticky_3195_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object* v_keyword_3198_, lean_object* v_alts_3199_, uint8_t v_format_3200_){
_start:
{
uint8_t v___x_3201_; lean_object* v_alts_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v_nonStickyDoc_3207_; 
v___x_3201_ = 1;
v_alts_3202_ = l_Lean_Fmt_Layouts_alts(v_alts_3199_, v___x_3201_);
v___x_3203_ = lean_unsigned_to_nat(2u);
v___x_3204_ = lean_mk_empty_array_with_capacity(v___x_3203_);
lean_inc_ref(v_keyword_3198_);
lean_inc_ref(v___x_3204_);
v___x_3205_ = lean_array_push(v___x_3204_, v_keyword_3198_);
lean_inc_ref(v_alts_3202_);
v___x_3206_ = lean_array_push(v___x_3205_, v_alts_3202_);
v_nonStickyDoc_3207_ = l_Lean_Fmt_Layouts_lines(v___x_3206_);
lean_dec_ref(v___x_3206_);
if (v_format_3200_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v_stickyDoc_3211_; uint8_t v___x_3212_; lean_object* v___x_3213_; 
v___x_3208_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3198_);
v___x_3209_ = lean_array_push(v___x_3204_, v___x_3208_);
v___x_3210_ = lean_array_push(v___x_3209_, v_alts_3202_);
v_stickyDoc_3211_ = l_Lean_Fmt_Layouts_lines(v___x_3210_);
lean_dec_ref(v___x_3210_);
v___x_3212_ = 0;
v___x_3213_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3207_, v_stickyDoc_3211_, v___x_3212_);
return v___x_3213_;
}
else
{
lean_dec_ref(v___x_3204_);
lean_dec_ref(v_alts_3202_);
lean_dec_ref(v_keyword_3198_);
return v_nonStickyDoc_3207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts___boxed(lean_object* v_keyword_3214_, lean_object* v_alts_3215_, lean_object* v_format_3216_){
_start:
{
uint8_t v_format_boxed_3217_; lean_object* v_res_3218_; 
v_format_boxed_3217_ = lean_unbox(v_format_3216_);
v_res_3218_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v_keyword_3214_, v_alts_3215_, v_format_boxed_3217_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl(lean_object* v_x_3219_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_obj_tag_nat(v_x_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl___boxed(lean_object* v_x_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl(v_x_3221_);
lean_dec_ref(v_x_3221_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(lean_object* v_t_3223_, lean_object* v_k_3224_){
_start:
{
lean_object* v_sepArrayFormat_3225_; lean_object* v___x_3226_; 
v_sepArrayFormat_3225_ = lean_ctor_get(v_t_3223_, 0);
lean_inc_ref(v_sepArrayFormat_3225_);
lean_dec_ref(v_t_3223_);
v___x_3226_ = lean_apply_1(v_k_3224_, v_sepArrayFormat_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(lean_object* v_motive_3227_, lean_object* v_ctorIdx_3228_, lean_object* v_t_3229_, lean_object* v_h_3230_, lean_object* v_k_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3229_, v_k_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___boxed(lean_object* v_motive_3233_, lean_object* v_ctorIdx_3234_, lean_object* v_t_3235_, lean_object* v_h_3236_, lean_object* v_k_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(v_motive_3233_, v_ctorIdx_3234_, v_t_3235_, v_h_3236_, v_k_3237_);
lean_dec(v_ctorIdx_3234_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim___redArg(lean_object* v_t_3239_, lean_object* v_sticky_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3239_, v_sticky_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim(lean_object* v_motive_3242_, lean_object* v_t_3243_, lean_object* v_h_3244_, lean_object* v_sticky_3245_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3243_, v_sticky_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim___redArg(lean_object* v_t_3247_, lean_object* v_nonSticky_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3247_, v_nonSticky_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim(lean_object* v_motive_3250_, lean_object* v_t_3251_, lean_object* v_h_3252_, lean_object* v_nonSticky_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3251_, v_nonSticky_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(lean_object* v_x_3255_){
_start:
{
if (lean_obj_tag(v_x_3255_) == 0)
{
uint8_t v___x_3256_; 
v___x_3256_ = 1;
return v___x_3256_;
}
else
{
uint8_t v___x_3257_; 
v___x_3257_ = 0;
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky___boxed(lean_object* v_x_3258_){
_start:
{
uint8_t v_res_3259_; lean_object* v_r_3260_; 
v_res_3259_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_x_3258_);
lean_dec_ref(v_x_3258_);
v_r_3260_ = lean_box(v_res_3259_);
return v_r_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(lean_object* v_x_3261_){
_start:
{
lean_object* v_sepArrayFormat_3262_; 
v_sepArrayFormat_3262_ = lean_ctor_get(v_x_3261_, 0);
lean_inc_ref(v_sepArrayFormat_3262_);
return v_sepArrayFormat_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat___boxed(lean_object* v_x_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(v_x_3263_);
lean_dec_ref(v_x_3263_);
return v_res_3264_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3266_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v___x_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray(lean_object* v_sep_3268_, lean_object* v_keyword_3269_, lean_object* v_sepArray_3270_, lean_object* v_format_3271_){
_start:
{
lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___x_3310_; lean_object* v___y_3312_; uint8_t v___y_3313_; lean_object* v___y_3318_; uint8_t v___y_3319_; lean_object* v___y_3335_; lean_object* v_sepArrayFormat_3339_; 
v___x_3310_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_sepArrayFormat_3339_ = lean_ctor_get(v_format_3271_, 0);
lean_inc_ref(v_sepArrayFormat_3339_);
v___y_3335_ = v_sepArrayFormat_3339_;
goto v___jp_3334_;
v___jp_3272_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v_nonStickyDoc_3299_; uint8_t v___x_3300_; 
lean_inc_ref(v_keyword_3269_);
v___x_3276_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3269_);
v___x_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
v___x_3278_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v___x_3277_);
v___x_3279_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3277_, v___x_3278_);
v___x_3280_ = lean_box(0);
lean_inc_ref(v___y_3274_);
lean_inc_ref(v_sep_3268_);
v___x_3281_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3268_, v___y_3275_, v___y_3274_);
lean_dec_ref(v___y_3275_);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
v___x_3283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3280_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
lean_ctor_set(v___x_3283_, 2, v___x_3280_);
v___x_3284_ = lean_unsigned_to_nat(2u);
v___x_3285_ = lean_mk_empty_array_with_capacity(v___x_3284_);
lean_inc_ref_n(v___x_3285_, 3);
v___x_3286_ = lean_array_push(v___x_3285_, v___x_3279_);
v___x_3287_ = lean_array_push(v___x_3286_, v___x_3283_);
v___x_3288_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3287_);
lean_dec_ref(v___x_3287_);
v___x_3289_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_3290_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3277_, v___x_3289_);
v___x_3291_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3268_, v___y_3273_, v___y_3274_);
lean_dec_ref(v___y_3273_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3280_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
lean_ctor_set(v___x_3293_, 2, v___x_3280_);
v___x_3294_ = lean_array_push(v___x_3285_, v___x_3290_);
lean_inc_ref(v___x_3293_);
v___x_3295_ = lean_array_push(v___x_3294_, v___x_3293_);
v___x_3296_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3295_);
lean_dec_ref(v___x_3295_);
v___x_3297_ = lean_array_push(v___x_3285_, v___x_3288_);
v___x_3298_ = lean_array_push(v___x_3297_, v___x_3296_);
v_nonStickyDoc_3299_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3298_);
v___x_3300_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3271_);
lean_dec_ref(v_format_3271_);
if (v___x_3300_ == 0)
{
lean_dec_ref_known(v___x_3293_, 3);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_keyword_3269_);
return v_nonStickyDoc_3299_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v_stickyDoc_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; 
v___x_3301_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3269_);
v___x_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
v___x_3303_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3304_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3302_, v___x_3303_);
v___x_3305_ = lean_array_push(v___x_3285_, v___x_3304_);
v___x_3306_ = lean_array_push(v___x_3305_, v___x_3293_);
v_stickyDoc_3307_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3306_);
lean_dec_ref(v___x_3306_);
v___x_3308_ = 0;
v___x_3309_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3299_, v_stickyDoc_3307_, v___x_3308_);
return v___x_3309_;
}
}
v___jp_3311_:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = lean_unsigned_to_nat(0u);
v___x_3315_ = lean_array_get(v___x_3310_, v___y_3312_, v___x_3314_);
lean_dec_ref(v___y_3312_);
v___x_3316_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3269_, v___x_3315_, v___y_3313_);
return v___x_3316_;
}
v___jp_3317_:
{
lean_object* v_sepArray_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; 
lean_inc_ref(v_sep_3268_);
v_sepArray_3320_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_3268_, v_sepArray_3270_, v___y_3319_);
v___x_3321_ = lean_array_get_size(v_sepArray_3320_);
v___x_3322_ = lean_unsigned_to_nat(1u);
v___x_3323_ = lean_nat_dec_eq(v___x_3321_, v___x_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = lean_nat_dec_lt(v___x_3324_, v___x_3321_);
if (v___x_3325_ == 0)
{
lean_inc_ref(v_sepArray_3320_);
v___y_3273_ = v_sepArray_3320_;
v___y_3274_ = v___y_3318_;
v___y_3275_ = v_sepArray_3320_;
goto v___jp_3272_;
}
else
{
lean_object* v_v_3326_; lean_object* v___x_3327_; lean_object* v_xs_x27_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_v_3326_ = lean_array_fget_borrowed(v_sepArray_3320_, v___x_3324_);
v___x_3327_ = lean_box(0);
lean_inc_ref(v_sepArray_3320_);
v_xs_x27_3328_ = lean_array_fset(v_sepArray_3320_, v___x_3324_, v___x_3327_);
lean_inc(v_v_3326_);
v___x_3329_ = l_Lean_Fmt_TaggedDoc_flattened(v_v_3326_);
v___x_3330_ = lean_array_fset(v_xs_x27_3328_, v___x_3324_, v___x_3329_);
v___y_3273_ = v_sepArray_3320_;
v___y_3274_ = v___y_3318_;
v___y_3275_ = v___x_3330_;
goto v___jp_3272_;
}
}
else
{
uint8_t v___x_3331_; 
lean_dec_ref(v___y_3318_);
lean_dec_ref(v_sep_3268_);
v___x_3331_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3271_);
lean_dec_ref(v_format_3271_);
if (v___x_3331_ == 0)
{
uint8_t v___x_3332_; 
v___x_3332_ = 1;
v___y_3312_ = v_sepArray_3320_;
v___y_3313_ = v___x_3332_;
goto v___jp_3311_;
}
else
{
uint8_t v___x_3333_; 
v___x_3333_ = 0;
v___y_3312_ = v_sepArray_3320_;
v___y_3313_ = v___x_3333_;
goto v___jp_3311_;
}
}
}
v___jp_3334_:
{
switch(lean_obj_tag(v___y_3335_))
{
case 1:
{
uint8_t v_trailingSep_3336_; 
v_trailingSep_3336_ = lean_ctor_get_uint8(v___y_3335_, sizeof(void*)*1 + 1);
v___y_3318_ = v___y_3335_;
v___y_3319_ = v_trailingSep_3336_;
goto v___jp_3317_;
}
case 3:
{
uint8_t v_trailingSep_3337_; 
v_trailingSep_3337_ = lean_ctor_get_uint8(v___y_3335_, sizeof(void*)*1);
v___y_3318_ = v___y_3335_;
v___y_3319_ = v_trailingSep_3337_;
goto v___jp_3317_;
}
default: 
{
uint8_t v_trailingSep_3338_; 
v_trailingSep_3338_ = lean_ctor_get_uint8(v___y_3335_, sizeof(void*)*2);
v___y_3318_ = v___y_3335_;
v___y_3319_ = v_trailingSep_3338_;
goto v___jp_3317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___boxed(lean_object* v_sep_3340_, lean_object* v_keyword_3341_, lean_object* v_sepArray_3342_, lean_object* v_format_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3340_, v_keyword_3341_, v_sepArray_3342_, v_format_3343_);
lean_dec_ref(v_sepArray_3342_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl(uint8_t v_x_3345_){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_box(v_x_3345_);
v___x_3347_ = lean_obj_tag_nat(v___x_3346_);
lean_dec(v___x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl___boxed(lean_object* v_x_3348_){
_start:
{
uint8_t v_x_4__boxed_3349_; lean_object* v_res_3350_; 
v_x_4__boxed_3349_ = lean_unbox(v_x_3348_);
v_res_3350_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl(v_x_4__boxed_3349_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(lean_object* v_k_3351_){
_start:
{
lean_inc(v_k_3351_);
return v_k_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg___boxed(lean_object* v_k_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(v_k_3352_);
lean_dec(v_k_3352_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(lean_object* v_motive_3354_, lean_object* v_ctorIdx_3355_, uint8_t v_t_3356_, lean_object* v_h_3357_, lean_object* v_k_3358_){
_start:
{
lean_inc(v_k_3358_);
return v_k_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___boxed(lean_object* v_motive_3359_, lean_object* v_ctorIdx_3360_, lean_object* v_t_3361_, lean_object* v_h_3362_, lean_object* v_k_3363_){
_start:
{
uint8_t v_t_boxed_3364_; lean_object* v_res_3365_; 
v_t_boxed_3364_ = lean_unbox(v_t_3361_);
v_res_3365_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(v_motive_3359_, v_ctorIdx_3360_, v_t_boxed_3364_, v_h_3362_, v_k_3363_);
lean_dec(v_k_3363_);
lean_dec(v_ctorIdx_3360_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(lean_object* v_sticky_3366_){
_start:
{
lean_inc(v_sticky_3366_);
return v_sticky_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(v_sticky_3367_);
lean_dec(v_sticky_3367_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(lean_object* v_motive_3369_, uint8_t v_t_3370_, lean_object* v_h_3371_, lean_object* v_sticky_3372_){
_start:
{
lean_inc(v_sticky_3372_);
return v_sticky_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___boxed(lean_object* v_motive_3373_, lean_object* v_t_3374_, lean_object* v_h_3375_, lean_object* v_sticky_3376_){
_start:
{
uint8_t v_t_boxed_3377_; lean_object* v_res_3378_; 
v_t_boxed_3377_ = lean_unbox(v_t_3374_);
v_res_3378_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(v_motive_3373_, v_t_boxed_3377_, v_h_3375_, v_sticky_3376_);
lean_dec(v_sticky_3376_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3379_){
_start:
{
lean_inc(v_nonSticky_3379_);
return v_nonSticky_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(v_nonSticky_3380_);
lean_dec(v_nonSticky_3380_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(lean_object* v_motive_3382_, uint8_t v_t_3383_, lean_object* v_h_3384_, lean_object* v_nonSticky_3385_){
_start:
{
lean_inc(v_nonSticky_3385_);
return v_nonSticky_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___boxed(lean_object* v_motive_3386_, lean_object* v_t_3387_, lean_object* v_h_3388_, lean_object* v_nonSticky_3389_){
_start:
{
uint8_t v_t_boxed_3390_; lean_object* v_res_3391_; 
v_t_boxed_3390_ = lean_unbox(v_t_3387_);
v_res_3391_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(v_motive_3386_, v_t_boxed_3390_, v_h_3388_, v_nonSticky_3389_);
lean_dec(v_nonSticky_3389_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object* v_sep_3396_, lean_object* v_keyword_3397_, lean_object* v_sepArray_3398_, uint8_t v_format_3399_){
_start:
{
if (v_format_3399_ == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0));
v___x_3401_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3396_, v_keyword_3397_, v_sepArray_3398_, v___x_3400_);
return v___x_3401_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1));
v___x_3403_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3396_, v_keyword_3397_, v_sepArray_3398_, v___x_3402_);
return v___x_3403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___boxed(lean_object* v_sep_3404_, lean_object* v_keyword_3405_, lean_object* v_sepArray_3406_, lean_object* v_format_3407_){
_start:
{
uint8_t v_format_boxed_3408_; lean_object* v_res_3409_; 
v_format_boxed_3408_ = lean_unbox(v_format_3407_);
v_res_3409_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v_sep_3404_, v_keyword_3405_, v_sepArray_3406_, v_format_boxed_3408_);
lean_dec_ref(v_sepArray_3406_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(lean_object* v_format_3410_, lean_object* v_a_3411_){
_start:
{
uint8_t v_nestedRhs_3412_; 
v_nestedRhs_3412_ = lean_ctor_get_uint8(v_format_3410_, 1);
if (v_nestedRhs_3412_ == 0)
{
return v_a_3411_;
}
else
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Fmt_TaggedDoc_nested(v_a_3411_);
return v___x_3413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed(lean_object* v_format_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(v_format_3414_, v_a_3415_);
lean_dec_ref(v_format_3414_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(lean_object* v_format_3417_){
_start:
{
uint8_t v_allowFlattening_3418_; 
v_allowFlattening_3418_ = lean_ctor_get_uint8(v_format_3417_, 0);
if (v_allowFlattening_3418_ == 0)
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_Fmt_TaggedDoc_hardNl;
return v___x_3419_;
}
else
{
lean_object* v___x_3420_; 
v___x_3420_ = l_Lean_Fmt_TaggedDoc_nl;
return v___x_3420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep___boxed(lean_object* v_format_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3421_);
lean_dec_ref(v_format_3421_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(lean_object* v_rhs_3423_, lean_object* v_format_3424_, lean_object* v_lhs_3425_){
_start:
{
uint8_t v_allowFlattening_3426_; 
v_allowFlattening_3426_ = lean_ctor_get_uint8(v_format_3424_, 0);
if (v_allowFlattening_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_lhs_3425_);
v___x_3428_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3424_);
v___x_3429_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3429_, 0, v_format_3424_);
v___x_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3427_, v___x_3430_);
v___x_3432_ = lean_box(0);
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_rhs_3423_);
v___x_3434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
lean_ctor_set(v___x_3434_, 2, v___x_3432_);
v___x_3435_ = lean_unsigned_to_nat(2u);
v___x_3436_ = lean_mk_empty_array_with_capacity(v___x_3435_);
v___x_3437_ = lean_array_push(v___x_3436_, v___x_3431_);
v___x_3438_ = lean_array_push(v___x_3437_, v___x_3434_);
v___x_3439_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3438_);
lean_dec_ref(v___x_3438_);
return v___x_3439_;
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3440_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3424_);
v___x_3441_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3441_, 0, v_format_3424_);
v___x_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3440_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_3425_, v___x_3442_, v_rhs_3423_, v_allowFlattening_3426_);
return v___x_3443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object* v_lhs_3444_, lean_object* v_keywordTk_3445_, lean_object* v_rhs_3446_, lean_object* v_format_3447_){
_start:
{
lean_object* v___y_3449_; uint8_t v___x_3452_; 
v___x_3452_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keywordTk_3445_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v_trailingKeywordLhs_3457_; uint8_t v___x_3458_; 
v___x_3453_ = lean_unsigned_to_nat(2u);
v___x_3454_ = lean_mk_empty_array_with_capacity(v___x_3453_);
v___x_3455_ = lean_array_push(v___x_3454_, v_lhs_3444_);
v___x_3456_ = lean_array_push(v___x_3455_, v_keywordTk_3445_);
v_trailingKeywordLhs_3457_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3456_);
lean_dec_ref(v___x_3456_);
v___x_3458_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_3446_);
if (v___x_3458_ == 0)
{
uint8_t v_nestedRhs_3459_; 
v_nestedRhs_3459_ = lean_ctor_get_uint8(v_format_3447_, 1);
if (v_nestedRhs_3459_ == 0)
{
v___y_3449_ = v_trailingKeywordLhs_3457_;
goto v___jp_3448_;
}
else
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_Fmt_TaggedDoc_hardNested(v_trailingKeywordLhs_3457_);
v___y_3449_ = v___x_3460_;
goto v___jp_3448_;
}
}
else
{
v___y_3449_ = v_trailingKeywordLhs_3457_;
goto v___jp_3448_;
}
}
else
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_dec_ref(v_keywordTk_3445_);
v___x_3461_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3446_, v_format_3447_, v_lhs_3444_);
v___x_3462_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3461_);
return v___x_3462_;
}
v___jp_3448_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3446_, v_format_3447_, v___y_3449_);
v___x_3451_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3450_);
return v___x_3451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0(lean_object* v___y_3463_){
_start:
{
lean_inc_ref(v___y_3463_);
return v___y_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0___boxed(lean_object* v___y_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0(v___y_3464_);
lean_dec_ref(v___y_3464_);
return v_res_3465_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1(void){
_start:
{
lean_object* v___f_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___f_3467_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0));
v___x_3468_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v___f_3467_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(lean_object* v_terms_3470_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3471_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3472_ = lean_box(0);
v___x_3473_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v_terms_3470_);
v___x_3474_ = lean_array_pop(v_terms_3470_);
v___x_3475_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_3473_, v___x_3474_);
v___x_3476_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3475_);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3472_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
lean_ctor_set(v___x_3478_, 2, v___x_3472_);
v___x_3479_ = lean_array_get_size(v_terms_3470_);
v___x_3480_ = lean_unsigned_to_nat(1u);
v___x_3481_ = lean_nat_sub(v___x_3479_, v___x_3480_);
v___x_3482_ = lean_array_get(v___x_3471_, v_terms_3470_, v___x_3481_);
lean_dec(v___x_3481_);
lean_dec_ref(v_terms_3470_);
v___x_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
v___x_3484_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1);
v___x_3485_ = l_Lean_Fmt_TaggedDoc_Component_withSepBefore(v___x_3483_, v___x_3484_);
v___x_3486_ = lean_unsigned_to_nat(2u);
v___x_3487_ = lean_mk_empty_array_with_capacity(v___x_3486_);
v___x_3488_ = lean_array_push(v___x_3487_, v___x_3478_);
v___x_3489_ = lean_array_push(v___x_3488_, v___x_3485_);
v___x_3490_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3489_);
lean_dec_ref(v___x_3489_);
return v___x_3490_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3492_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(lean_object* v_app_3493_, lean_object* v_fillableTerms_3494_, lean_object* v_terms_3495_, lean_object* v_eligibleKinds_3496_){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v_allowFill_3503_; 
v___x_3497_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3498_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3499_ = lean_array_get_size(v_fillableTerms_3494_);
v___x_3500_ = lean_unsigned_to_nat(1u);
v___x_3501_ = lean_nat_sub(v___x_3499_, v___x_3500_);
v___x_3502_ = lean_array_get_borrowed(v___x_3498_, v_fillableTerms_3494_, v___x_3501_);
lean_dec(v___x_3501_);
v_allowFill_3503_ = lean_ctor_get_uint8(v___x_3502_, sizeof(void*)*1);
if (v_allowFill_3503_ == 0)
{
lean_object* v___x_3504_; 
lean_dec_ref(v_terms_3495_);
lean_dec_ref(v_app_3493_);
v___x_3504_ = lean_box(0);
return v___x_3504_;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3505_ = lean_array_get_size(v_terms_3495_);
v___x_3506_ = lean_nat_sub(v___x_3505_, v___x_3500_);
v___x_3507_ = lean_array_get_borrowed(v___x_3497_, v_terms_3495_, v___x_3506_);
lean_inc(v___x_3507_);
v___x_3508_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v___x_3507_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v___x_3509_; 
lean_dec(v___x_3506_);
lean_dec_ref(v_terms_3495_);
lean_dec_ref(v_app_3493_);
v___x_3509_ = lean_box(0);
return v___x_3509_;
}
else
{
lean_object* v_val_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3531_; 
v_val_3510_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3512_ = v___x_3508_;
v_isShared_3513_ = v_isSharedCheck_3531_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_val_3510_);
lean_dec(v___x_3508_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3531_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
uint8_t v___x_3514_; uint8_t v___x_3515_; lean_object* v___y_3517_; 
v___x_3514_ = lean_unbox(v_val_3510_);
lean_dec(v_val_3510_);
v___x_3515_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_3496_, v___x_3514_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3526_; 
lean_del_object(v___x_3512_);
lean_dec(v___x_3506_);
lean_dec_ref(v_terms_3495_);
lean_dec_ref(v_app_3493_);
v___x_3526_ = lean_box(0);
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; 
lean_inc(v___x_3507_);
v___x_3527_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v___x_3507_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_3529_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_3528_);
v___y_3517_ = v___x_3529_;
goto v___jp_3516_;
}
else
{
lean_object* v_val_3530_; 
v_val_3530_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_val_3530_);
lean_dec_ref_known(v___x_3527_, 1);
v___y_3517_ = v_val_3530_;
goto v___jp_3516_;
}
}
v___jp_3516_:
{
lean_object* v_stickyVariant_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v_stickyVariant_3518_ = lean_ctor_get(v___y_3517_, 0);
lean_inc_ref(v_stickyVariant_3518_);
v___x_3519_ = lean_array_set(v_terms_3495_, v___x_3506_, v_stickyVariant_3518_);
lean_dec(v___x_3506_);
v___x_3520_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v___x_3519_);
v___x_3521_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_3517_, v___x_3515_);
lean_dec_ref(v___y_3517_);
v___x_3522_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_app_3493_, v___x_3520_, v___x_3521_);
lean_dec(v___x_3521_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3522_);
v___x_3524_ = v___x_3512_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___boxed(lean_object* v_app_3532_, lean_object* v_fillableTerms_3533_, lean_object* v_terms_3534_, lean_object* v_eligibleKinds_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3532_, v_fillableTerms_3533_, v_terms_3534_, v_eligibleKinds_3535_);
lean_dec_ref(v_eligibleKinds_3535_);
lean_dec_ref(v_fillableTerms_3533_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(lean_object* v_format_3537_, lean_object* v_app_3538_, lean_object* v_terms_3539_){
_start:
{
uint8_t v_sparse_3540_; 
v_sparse_3540_ = lean_ctor_get_uint8(v_format_3537_, 1);
if (v_sparse_3540_ == 0)
{
uint8_t v_respectPseudoAlignment_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v_respectPseudoAlignment_3541_ = lean_ctor_get_uint8(v_format_3537_, 3);
v___x_3542_ = lean_array_get_size(v_terms_3539_);
v___x_3543_ = lean_unsigned_to_nat(2u);
v___x_3544_ = lean_nat_dec_eq(v___x_3542_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; 
lean_dec_ref(v_terms_3539_);
lean_dec_ref(v_app_3538_);
v___x_3545_ = lean_box(0);
return v___x_3545_;
}
else
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
v___x_3546_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_sub(v___x_3542_, v___x_3547_);
v___x_3549_ = lean_array_get_borrowed(v___x_3546_, v_terms_3539_, v___x_3548_);
lean_dec(v___x_3548_);
lean_inc(v___x_3549_);
v___x_3550_ = l_Lean_Fmt_Layouts_permitDenseLayout(v___x_3549_, v_respectPseudoAlignment_3541_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref(v_terms_3539_);
lean_dec_ref(v_app_3538_);
v___x_3551_ = lean_box(0);
return v___x_3551_;
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3552_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v_terms_3539_);
v___x_3553_ = lean_mk_empty_array_with_capacity(v___x_3543_);
v___x_3554_ = lean_array_push(v___x_3553_, v___x_3552_);
v___x_3555_ = lean_array_push(v___x_3554_, v_app_3538_);
v___x_3556_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3555_);
v___x_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
return v___x_3557_;
}
}
}
else
{
lean_object* v___x_3558_; 
lean_dec_ref(v_terms_3539_);
lean_dec_ref(v_app_3538_);
v___x_3558_ = lean_box(0);
return v___x_3558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f___boxed(lean_object* v_format_3559_, lean_object* v_app_3560_, lean_object* v_terms_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3559_, v_app_3560_, v_terms_3561_);
lean_dec_ref(v_format_3559_);
return v_res_3562_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0));
v___x_3565_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3566_; lean_object* v_lbTk_3567_; 
v___x_3566_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1);
v_lbTk_3567_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3566_);
return v_lbTk_3567_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3));
v___x_3570_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3569_);
return v___x_3570_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_3571_; lean_object* v_rbTk_3572_; 
v___x_3571_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4);
v_rbTk_3572_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3571_);
return v_rbTk_3572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(lean_object* v_upperBound_3573_, lean_object* v_a_3574_, lean_object* v_b_3575_){
_start:
{
lean_object* v_a_3577_; uint8_t v___x_3581_; 
v___x_3581_ = lean_nat_dec_lt(v_a_3574_, v_upperBound_3573_);
if (v___x_3581_ == 0)
{
lean_dec(v_a_3574_);
return v_b_3575_;
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v_v_3584_; uint8_t v_allowFill_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3597_; 
v___x_3582_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3583_ = lean_array_get(v___x_3582_, v_b_3575_, v_a_3574_);
v_v_3584_ = lean_ctor_get(v___x_3583_, 0);
v_allowFill_3585_ = lean_ctor_get_uint8(v___x_3583_, sizeof(void*)*1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3587_ = v___x_3583_;
v_isShared_3588_ = v_isSharedCheck_3597_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_v_3584_);
lean_dec(v___x_3583_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3597_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
uint8_t v___x_3589_; 
lean_inc(v_v_3584_);
v___x_3589_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_v_3584_);
if (v___x_3589_ == 0)
{
lean_del_object(v___x_3587_);
lean_dec(v_v_3584_);
v_a_3577_ = v_b_3575_;
goto v___jp_3576_;
}
else
{
lean_object* v_lbTk_3590_; lean_object* v_rbTk_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v_lbTk_3590_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2);
v_rbTk_3591_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5);
v___x_3592_ = l_Lean_Fmt_Layouts_parens(v_lbTk_3590_, v_v_3584_, v_rbTk_3591_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v___x_3592_);
v___x_3594_ = v___x_3587_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3592_);
lean_ctor_set_uint8(v_reuseFailAlloc_3596_, sizeof(void*)*1, v_allowFill_3585_);
v___x_3594_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_array_set(v_b_3575_, v_a_3574_, v___x_3594_);
v_a_3577_ = v___x_3595_;
goto v___jp_3576_;
}
}
}
}
v___jp_3576_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = lean_unsigned_to_nat(1u);
v___x_3579_ = lean_nat_add(v_a_3574_, v___x_3578_);
lean_dec(v_a_3574_);
v_a_3574_ = v___x_3579_;
v_b_3575_ = v_a_3577_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___boxed(lean_object* v_upperBound_3598_, lean_object* v_a_3599_, lean_object* v_b_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3598_, v_a_3599_, v_b_3600_);
lean_dec(v_upperBound_3598_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(lean_object* v_as_3602_, size_t v_i_3603_, size_t v_stop_3604_, lean_object* v_b_3605_){
_start:
{
lean_object* v___y_3607_; uint8_t v___x_3611_; 
v___x_3611_ = lean_usize_dec_eq(v_i_3603_, v_stop_3604_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; lean_object* v_v_3613_; uint8_t v___x_3614_; 
v___x_3612_ = lean_array_uget_borrowed(v_as_3602_, v_i_3603_);
v_v_3613_ = lean_ctor_get(v___x_3612_, 0);
v___x_3614_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; 
lean_inc(v___x_3612_);
v___x_3615_ = lean_array_push(v_b_3605_, v___x_3612_);
v___y_3607_ = v___x_3615_;
goto v___jp_3606_;
}
else
{
v___y_3607_ = v_b_3605_;
goto v___jp_3606_;
}
}
else
{
return v_b_3605_;
}
v___jp_3606_:
{
size_t v___x_3608_; size_t v___x_3609_; 
v___x_3608_ = ((size_t)1ULL);
v___x_3609_ = lean_usize_add(v_i_3603_, v___x_3608_);
v_i_3603_ = v___x_3609_;
v_b_3605_ = v___y_3607_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2___boxed(lean_object* v_as_3616_, lean_object* v_i_3617_, lean_object* v_stop_3618_, lean_object* v_b_3619_){
_start:
{
size_t v_i_boxed_3620_; size_t v_stop_boxed_3621_; lean_object* v_res_3622_; 
v_i_boxed_3620_ = lean_unbox_usize(v_i_3617_);
lean_dec(v_i_3617_);
v_stop_boxed_3621_ = lean_unbox_usize(v_stop_3618_);
lean_dec(v_stop_3618_);
v_res_3622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_as_3616_, v_i_boxed_3620_, v_stop_boxed_3621_, v_b_3619_);
lean_dec_ref(v_as_3616_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(size_t v_sz_3623_, size_t v_i_3624_, lean_object* v_bs_3625_){
_start:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_usize_dec_lt(v_i_3624_, v_sz_3623_);
if (v___x_3626_ == 0)
{
return v_bs_3625_;
}
else
{
lean_object* v_v_3627_; lean_object* v_v_3628_; lean_object* v___x_3629_; lean_object* v_bs_x27_3630_; size_t v___x_3631_; size_t v___x_3632_; lean_object* v___x_3633_; 
v_v_3627_ = lean_array_uget_borrowed(v_bs_3625_, v_i_3624_);
v_v_3628_ = lean_ctor_get(v_v_3627_, 0);
lean_inc(v_v_3628_);
v___x_3629_ = lean_unsigned_to_nat(0u);
v_bs_x27_3630_ = lean_array_uset(v_bs_3625_, v_i_3624_, v___x_3629_);
v___x_3631_ = ((size_t)1ULL);
v___x_3632_ = lean_usize_add(v_i_3624_, v___x_3631_);
v___x_3633_ = lean_array_uset(v_bs_x27_3630_, v_i_3624_, v_v_3628_);
v_i_3624_ = v___x_3632_;
v_bs_3625_ = v___x_3633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0___boxed(lean_object* v_sz_3635_, lean_object* v_i_3636_, lean_object* v_bs_3637_){
_start:
{
size_t v_sz_boxed_3638_; size_t v_i_boxed_3639_; lean_object* v_res_3640_; 
v_sz_boxed_3638_ = lean_unbox_usize(v_sz_3635_);
lean_dec(v_sz_3635_);
v_i_boxed_3639_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_res_3640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_boxed_3638_, v_i_boxed_3639_, v_bs_3637_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object* v_terms_3643_, lean_object* v_format_3644_){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; uint8_t v___y_3648_; lean_object* v___y_3649_; lean_object* v_app_3650_; uint8_t v___y_3663_; lean_object* v___y_3664_; lean_object* v_fillableTerms_3665_; uint8_t v___y_3682_; lean_object* v___y_3683_; lean_object* v_fillableTerms_3684_; lean_object* v___y_3690_; lean_object* v___x_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v___x_3645_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3646_ = lean_unsigned_to_nat(0u);
v___x_3716_ = lean_array_get_size(v_terms_3643_);
v___x_3717_ = ((lean_object*)(l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0));
v___x_3718_ = lean_nat_dec_lt(v___x_3646_, v___x_3716_);
if (v___x_3718_ == 0)
{
v___y_3690_ = v___x_3717_;
goto v___jp_3689_;
}
else
{
size_t v___x_3719_; size_t v___x_3720_; lean_object* v___x_3721_; 
v___x_3719_ = ((size_t)0ULL);
v___x_3720_ = lean_usize_of_nat(v___x_3716_);
v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3643_, v___x_3719_, v___x_3720_, v___x_3717_);
v___y_3690_ = v___x_3721_;
goto v___jp_3689_;
}
v___jp_3647_:
{
lean_object* v___x_3651_; lean_object* v_v_3652_; lean_object* v_doc_3653_; lean_object* v___x_3654_; lean_object* v_doc_3655_; uint8_t v___x_3656_; 
v___x_3651_ = lean_array_get(v___x_3645_, v___y_3649_, v___x_3646_);
lean_dec_ref(v___y_3649_);
v_v_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_v_3652_);
lean_dec(v___x_3651_);
v_doc_3653_ = lean_ctor_get(v_v_3652_, 0);
v___x_3654_ = l_Lean_Fmt_TaggedDoc_nested(v_app_3650_);
v_doc_3655_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3654_);
lean_inc(v_doc_3653_);
v___x_3656_ = l_Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_3653_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(v_v_3652_);
if (lean_obj_tag(v___x_3657_) == 1)
{
lean_object* v_val_3658_; uint8_t v___x_3659_; lean_object* v_doc_3660_; 
v_val_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_val_3658_);
lean_dec_ref_known(v___x_3657_, 1);
v___x_3659_ = lean_unbox(v_val_3658_);
lean_dec(v_val_3658_);
v_doc_3660_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_3655_, v___x_3659_);
return v_doc_3660_;
}
else
{
lean_dec(v___x_3657_);
return v_doc_3655_;
}
}
else
{
lean_object* v_doc_3661_; 
lean_dec(v_v_3652_);
v_doc_3661_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_3655_, v___y_3648_);
return v_doc_3661_;
}
}
v___jp_3662_:
{
lean_object* v_app_3666_; size_t v_sz_3667_; size_t v___x_3668_; lean_object* v_terms_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_inc_ref_n(v_fillableTerms_3665_, 2);
v_app_3666_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(v_fillableTerms_3665_);
v_sz_3667_ = lean_array_size(v_fillableTerms_3665_);
v___x_3668_ = ((size_t)0ULL);
v_terms_3669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_3667_, v___x_3668_, v_fillableTerms_3665_);
v___x_3670_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
lean_inc_ref(v_terms_3669_);
lean_inc_ref(v_app_3666_);
v___x_3671_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3666_, v_fillableTerms_3665_, v_terms_3669_, v___x_3670_);
if (lean_obj_tag(v___x_3671_) == 1)
{
lean_object* v_val_3672_; 
lean_dec_ref(v_terms_3669_);
lean_dec_ref(v_app_3666_);
lean_dec(v___y_3664_);
v_val_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_val_3672_);
lean_dec_ref_known(v___x_3671_, 1);
v___y_3648_ = v___y_3663_;
v___y_3649_ = v_fillableTerms_3665_;
v_app_3650_ = v_val_3672_;
goto v___jp_3647_;
}
else
{
lean_object* v___x_3673_; 
lean_dec(v___x_3671_);
lean_inc_ref(v_terms_3669_);
lean_inc_ref(v_app_3666_);
v___x_3673_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3644_, v_app_3666_, v_terms_3669_);
if (lean_obj_tag(v___x_3673_) == 1)
{
lean_object* v_val_3674_; 
lean_dec_ref(v_terms_3669_);
lean_dec_ref(v_app_3666_);
lean_dec(v___y_3664_);
v_val_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_val_3674_);
lean_dec_ref_known(v___x_3673_, 1);
v___y_3648_ = v___y_3663_;
v___y_3649_ = v_fillableTerms_3665_;
v_app_3650_ = v_val_3674_;
goto v___jp_3647_;
}
else
{
uint8_t v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_dec(v___x_3673_);
v___x_3675_ = 2;
v___x_3676_ = lean_mk_empty_array_with_capacity(v___y_3664_);
lean_dec(v___y_3664_);
v___x_3677_ = lean_box(v___x_3675_);
v___x_3678_ = lean_array_push(v___x_3676_, v___x_3677_);
lean_inc_ref(v_app_3666_);
v___x_3679_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3666_, v_fillableTerms_3665_, v_terms_3669_, v___x_3678_);
lean_dec_ref(v___x_3678_);
if (lean_obj_tag(v___x_3679_) == 1)
{
lean_object* v_val_3680_; 
lean_dec_ref(v_app_3666_);
v_val_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_val_3680_);
lean_dec_ref_known(v___x_3679_, 1);
v___y_3648_ = v___y_3663_;
v___y_3649_ = v_fillableTerms_3665_;
v_app_3650_ = v_val_3680_;
goto v___jp_3647_;
}
else
{
lean_dec(v___x_3679_);
v___y_3648_ = v___y_3663_;
v___y_3649_ = v_fillableTerms_3665_;
v_app_3650_ = v_app_3666_;
goto v___jp_3647_;
}
}
}
}
v___jp_3681_:
{
uint8_t v_parenthesize_3685_; 
v_parenthesize_3685_ = lean_ctor_get_uint8(v_format_3644_, 2);
if (v_parenthesize_3685_ == 0)
{
v___y_3663_ = v___y_3682_;
v___y_3664_ = v___y_3683_;
v_fillableTerms_3665_ = v_fillableTerms_3684_;
goto v___jp_3662_;
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = lean_array_get_size(v_fillableTerms_3684_);
v___x_3687_ = lean_nat_sub(v___x_3686_, v___y_3683_);
lean_inc(v___y_3683_);
v___x_3688_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v___x_3687_, v___y_3683_, v_fillableTerms_3684_);
lean_dec(v___x_3687_);
v___y_3663_ = v___y_3682_;
v___y_3664_ = v___y_3683_;
v_fillableTerms_3665_ = v___x_3688_;
goto v___jp_3662_;
}
}
v___jp_3689_:
{
lean_object* v___x_3691_; uint8_t v___x_3692_; 
v___x_3691_ = lean_array_get_size(v___y_3690_);
v___x_3692_ = lean_nat_dec_eq(v___x_3691_, v___x_3646_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3693_; uint8_t v___x_3694_; 
v___x_3693_ = lean_unsigned_to_nat(1u);
v___x_3694_ = lean_nat_dec_eq(v___x_3691_, v___x_3693_);
if (v___x_3694_ == 0)
{
uint8_t v___x_3695_; uint8_t v___x_3696_; 
v___x_3695_ = 1;
v___x_3696_ = lean_nat_dec_lt(v___x_3693_, v___x_3691_);
if (v___x_3696_ == 0)
{
v___y_3682_ = v___x_3695_;
v___y_3683_ = v___x_3693_;
v_fillableTerms_3684_ = v___y_3690_;
goto v___jp_3681_;
}
else
{
uint8_t v_hardNestedFirstTerm_3697_; 
v_hardNestedFirstTerm_3697_ = lean_ctor_get_uint8(v_format_3644_, 0);
if (v_hardNestedFirstTerm_3697_ == 0)
{
v___y_3682_ = v___x_3695_;
v___y_3683_ = v___x_3693_;
v_fillableTerms_3684_ = v___y_3690_;
goto v___jp_3681_;
}
else
{
uint8_t v___x_3698_; 
v___x_3698_ = lean_nat_dec_lt(v___x_3646_, v___x_3691_);
if (v___x_3698_ == 0)
{
v___y_3682_ = v___x_3695_;
v___y_3683_ = v___x_3693_;
v_fillableTerms_3684_ = v___y_3690_;
goto v___jp_3681_;
}
else
{
lean_object* v_v_3699_; lean_object* v_v_3700_; uint8_t v_allowFill_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3712_; 
v_v_3699_ = lean_array_fget(v___y_3690_, v___x_3646_);
v_v_3700_ = lean_ctor_get(v_v_3699_, 0);
v_allowFill_3701_ = lean_ctor_get_uint8(v_v_3699_, sizeof(void*)*1);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_v_3699_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3703_ = v_v_3699_;
v_isShared_3704_ = v_isSharedCheck_3712_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_v_3700_);
lean_dec(v_v_3699_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3712_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v_xs_x27_3706_; lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3705_ = lean_box(0);
v_xs_x27_3706_ = lean_array_fset(v___y_3690_, v___x_3646_, v___x_3705_);
v___x_3707_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3700_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3707_);
v___x_3709_ = v___x_3703_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3707_);
lean_ctor_set_uint8(v_reuseFailAlloc_3711_, sizeof(void*)*1, v_allowFill_3701_);
v___x_3709_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3710_; 
v___x_3710_ = lean_array_fset(v_xs_x27_3706_, v___x_3646_, v___x_3709_);
v___y_3682_ = v___x_3695_;
v___y_3683_ = v___x_3693_;
v_fillableTerms_3684_ = v___x_3710_;
goto v___jp_3681_;
}
}
}
}
}
}
else
{
lean_object* v___x_3713_; lean_object* v_v_3714_; 
v___x_3713_ = lean_array_get(v___x_3645_, v___y_3690_, v___x_3646_);
lean_dec_ref(v___y_3690_);
v_v_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_v_3714_);
lean_dec(v___x_3713_);
return v_v_3714_;
}
}
else
{
lean_object* v___x_3715_; 
lean_dec_ref(v___y_3690_);
v___x_3715_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___boxed(lean_object* v_terms_3722_, lean_object* v_format_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v_terms_3722_, v_format_3723_);
lean_dec_ref(v_format_3723_);
lean_dec_ref(v_terms_3722_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(lean_object* v_upperBound_3725_, lean_object* v_inst_3726_, lean_object* v_R_3727_, lean_object* v_a_3728_, lean_object* v_b_3729_, lean_object* v_c_3730_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3725_, v_a_3728_, v_b_3729_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___boxed(lean_object* v_upperBound_3732_, lean_object* v_inst_3733_, lean_object* v_R_3734_, lean_object* v_a_3735_, lean_object* v_b_3736_, lean_object* v_c_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(v_upperBound_3732_, v_inst_3733_, v_R_3734_, v_a_3735_, v_b_3736_, v_c_3737_);
lean_dec(v_upperBound_3732_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(size_t v_sz_3739_, size_t v_i_3740_, lean_object* v_bs_3741_){
_start:
{
uint8_t v___x_3742_; 
v___x_3742_ = lean_usize_dec_lt(v_i_3740_, v_sz_3739_);
if (v___x_3742_ == 0)
{
return v_bs_3741_;
}
else
{
lean_object* v_v_3743_; lean_object* v___x_3744_; lean_object* v_bs_x27_3745_; lean_object* v___x_3746_; size_t v___x_3747_; size_t v___x_3748_; lean_object* v___x_3749_; 
v_v_3743_ = lean_array_uget(v_bs_3741_, v_i_3740_);
v___x_3744_ = lean_unsigned_to_nat(0u);
v_bs_x27_3745_ = lean_array_uset(v_bs_3741_, v_i_3740_, v___x_3744_);
v___x_3746_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3746_, 0, v_v_3743_);
lean_ctor_set_uint8(v___x_3746_, sizeof(void*)*1, v___x_3742_);
v___x_3747_ = ((size_t)1ULL);
v___x_3748_ = lean_usize_add(v_i_3740_, v___x_3747_);
v___x_3749_ = lean_array_uset(v_bs_x27_3745_, v_i_3740_, v___x_3746_);
v_i_3740_ = v___x_3748_;
v_bs_3741_ = v___x_3749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0___boxed(lean_object* v_sz_3751_, lean_object* v_i_3752_, lean_object* v_bs_3753_){
_start:
{
size_t v_sz_boxed_3754_; size_t v_i_boxed_3755_; lean_object* v_res_3756_; 
v_sz_boxed_3754_ = lean_unbox_usize(v_sz_3751_);
lean_dec(v_sz_3751_);
v_i_boxed_3755_ = lean_unbox_usize(v_i_3752_);
lean_dec(v_i_3752_);
v_res_3756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_boxed_3754_, v_i_boxed_3755_, v_bs_3753_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application(lean_object* v_terms_3757_, lean_object* v_format_3758_){
_start:
{
size_t v_sz_3759_; size_t v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v_sz_3759_ = lean_array_size(v_terms_3757_);
v___x_3760_ = ((size_t)0ULL);
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_3759_, v___x_3760_, v_terms_3757_);
v___x_3762_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v___x_3761_, v_format_3758_);
lean_dec_ref(v___x_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application___boxed(lean_object* v_terms_3763_, lean_object* v_format_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Fmt_Layouts_application(v_terms_3763_, v_format_3764_);
lean_dec_ref(v_format_3764_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(lean_object* v_f_3766_){
_start:
{
uint8_t v_hardNestedFirstTerm_3767_; uint8_t v_sparse_3768_; uint8_t v_parenthesize_3769_; uint8_t v_respectPseudoAlignment_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
v_hardNestedFirstTerm_3767_ = lean_ctor_get_uint8(v_f_3766_, 0);
v_sparse_3768_ = lean_ctor_get_uint8(v_f_3766_, 1);
v_parenthesize_3769_ = lean_ctor_get_uint8(v_f_3766_, 2);
v_respectPseudoAlignment_3770_ = lean_ctor_get_uint8(v_f_3766_, 3);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_f_3766_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v_f_3766_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_dec(v_f_3766_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3776_, 0, v_hardNestedFirstTerm_3767_);
lean_ctor_set_uint8(v_reuseFailAlloc_3776_, 1, v_sparse_3768_);
lean_ctor_set_uint8(v_reuseFailAlloc_3776_, 2, v_parenthesize_3769_);
lean_ctor_set_uint8(v_reuseFailAlloc_3776_, 3, v_respectPseudoAlignment_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object* v_terms_3778_, lean_object* v_format_3779_){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(v_format_3779_);
v___x_3781_ = l_Lean_Fmt_Layouts_application(v_terms_3778_, v___x_3780_);
lean_dec_ref(v___x_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl(lean_object* v_x_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_obj_tag_nat(v_x_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl___boxed(lean_object* v_x_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl(v_x_3784_);
lean_dec_ref(v_x_3784_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(lean_object* v_t_3786_, lean_object* v_k_3787_){
_start:
{
lean_object* v_doc_3788_; lean_object* v___x_3789_; 
v_doc_3788_ = lean_ctor_get(v_t_3786_, 0);
lean_inc_ref(v_doc_3788_);
lean_dec_ref(v_t_3786_);
v___x_3789_ = lean_apply_1(v_k_3787_, v_doc_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(lean_object* v_motive_3790_, lean_object* v_ctorIdx_3791_, lean_object* v_t_3792_, lean_object* v_h_3793_, lean_object* v_k_3794_){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3792_, v_k_3794_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___boxed(lean_object* v_motive_3796_, lean_object* v_ctorIdx_3797_, lean_object* v_t_3798_, lean_object* v_h_3799_, lean_object* v_k_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(v_motive_3796_, v_ctorIdx_3797_, v_t_3798_, v_h_3799_, v_k_3800_);
lean_dec(v_ctorIdx_3797_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim___redArg(lean_object* v_t_3802_, lean_object* v_sep_3803_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3802_, v_sep_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim(lean_object* v_motive_3805_, lean_object* v_t_3806_, lean_object* v_h_3807_, lean_object* v_sep_3808_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3806_, v_sep_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim___redArg(lean_object* v_t_3810_, lean_object* v_elems_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3810_, v_elems_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim(lean_object* v_motive_3813_, lean_object* v_t_3814_, lean_object* v_h_3815_, lean_object* v_elems_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3814_, v_elems_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(size_t v_sz_3818_, size_t v_i_3819_, lean_object* v_bs_3820_){
_start:
{
uint8_t v___x_3821_; 
v___x_3821_ = lean_usize_dec_lt(v_i_3819_, v_sz_3818_);
if (v___x_3821_ == 0)
{
return v_bs_3820_;
}
else
{
lean_object* v_v_3822_; lean_object* v___x_3823_; lean_object* v_bs_x27_3824_; lean_object* v___y_3826_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v_v_3822_ = lean_array_uget(v_bs_3820_, v_i_3819_);
v___x_3823_ = lean_unsigned_to_nat(0u);
v_bs_x27_3824_ = lean_array_uset(v_bs_3820_, v_i_3819_, v___x_3823_);
v___x_3831_ = lean_usize_to_nat(v_i_3819_);
v___x_3832_ = lean_unsigned_to_nat(2u);
v___x_3833_ = lean_nat_mod(v___x_3831_, v___x_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_nat_dec_eq(v___x_3833_, v___x_3823_);
lean_dec(v___x_3833_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3835_, 0, v_v_3822_);
v___y_3826_ = v___x_3835_;
goto v___jp_3825_;
}
else
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3836_ = lean_unsigned_to_nat(1u);
v___x_3837_ = lean_mk_empty_array_with_capacity(v___x_3836_);
v___x_3838_ = lean_array_push(v___x_3837_, v_v_3822_);
v___x_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
v___y_3826_ = v___x_3839_;
goto v___jp_3825_;
}
v___jp_3825_:
{
size_t v___x_3827_; size_t v___x_3828_; lean_object* v___x_3829_; 
v___x_3827_ = ((size_t)1ULL);
v___x_3828_ = lean_usize_add(v_i_3819_, v___x_3827_);
v___x_3829_ = lean_array_uset(v_bs_x27_3824_, v_i_3819_, v___y_3826_);
v_i_3819_ = v___x_3828_;
v_bs_3820_ = v___x_3829_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg___boxed(lean_object* v_sz_3840_, lean_object* v_i_3841_, lean_object* v_bs_3842_){
_start:
{
size_t v_sz_boxed_3843_; size_t v_i_boxed_3844_; lean_object* v_res_3845_; 
v_sz_boxed_3843_ = lean_unbox_usize(v_sz_3840_);
lean_dec(v_sz_3840_);
v_i_boxed_3844_ = lean_unbox_usize(v_i_3841_);
lean_dec(v_i_3841_);
v_res_3845_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_boxed_3843_, v_i_boxed_3844_, v_bs_3842_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object* v_elems_3846_){
_start:
{
size_t v_sz_3847_; size_t v___x_3848_; lean_object* v___x_3849_; 
v_sz_3847_ = lean_array_size(v_elems_3846_);
v___x_3848_ = ((size_t)0ULL);
v___x_3849_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3847_, v___x_3848_, v_elems_3846_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(lean_object* v_s_3850_, lean_object* v_elems_3851_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_elems_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___boxed(lean_object* v_s_3853_, lean_object* v_elems_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(v_s_3853_, v_elems_3854_);
lean_dec_ref(v_s_3853_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(lean_object* v_as_3856_, size_t v_sz_3857_, size_t v_i_3858_, lean_object* v_bs_3859_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3857_, v_i_3858_, v_bs_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___boxed(lean_object* v_as_3861_, lean_object* v_sz_3862_, lean_object* v_i_3863_, lean_object* v_bs_3864_){
_start:
{
size_t v_sz_boxed_3865_; size_t v_i_boxed_3866_; lean_object* v_res_3867_; 
v_sz_boxed_3865_ = lean_unbox_usize(v_sz_3862_);
lean_dec(v_sz_3862_);
v_i_boxed_3866_ = lean_unbox_usize(v_i_3863_);
lean_dec(v_i_3863_);
v_res_3867_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(v_as_3861_, v_sz_boxed_3865_, v_i_boxed_3866_, v_bs_3864_);
lean_dec_ref(v_as_3861_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(size_t v_sz_3870_, size_t v_i_3871_, lean_object* v_bs_3872_){
_start:
{
uint8_t v___x_3873_; 
v___x_3873_ = lean_usize_dec_lt(v_i_3871_, v_sz_3870_);
if (v___x_3873_ == 0)
{
return v_bs_3872_;
}
else
{
lean_object* v_v_3874_; lean_object* v___x_3875_; lean_object* v_bs_x27_3876_; lean_object* v___y_3878_; 
v_v_3874_ = lean_array_uget(v_bs_3872_, v_i_3871_);
v___x_3875_ = lean_unsigned_to_nat(0u);
v_bs_x27_3876_ = lean_array_uset(v_bs_3872_, v_i_3871_, v___x_3875_);
if (lean_obj_tag(v_v_3874_) == 0)
{
v___y_3878_ = v_v_3874_;
goto v___jp_3877_;
}
else
{
lean_object* v_docs_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3897_; 
v_docs_3883_ = lean_ctor_get(v_v_3874_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v_v_3874_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3885_ = v_v_3874_;
v_isShared_3886_ = v_isSharedCheck_3897_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_docs_3883_);
lean_dec(v_v_3874_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3897_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3887_ = lean_array_get_size(v_docs_3883_);
v___x_3888_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_3889_ = lean_nat_dec_lt(v___x_3875_, v___x_3887_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; 
lean_del_object(v___x_3885_);
lean_dec_ref(v_docs_3883_);
v___x_3890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_3878_ = v___x_3890_;
goto v___jp_3877_;
}
else
{
size_t v___x_3891_; size_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3891_ = ((size_t)0ULL);
v___x_3892_ = lean_usize_of_nat(v___x_3887_);
v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_docs_3883_, v___x_3891_, v___x_3892_, v___x_3888_);
lean_dec_ref(v_docs_3883_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v___x_3893_);
v___x_3895_ = v___x_3885_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
v___y_3878_ = v___x_3895_;
goto v___jp_3877_;
}
}
}
}
v___jp_3877_:
{
size_t v___x_3879_; size_t v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = ((size_t)1ULL);
v___x_3880_ = lean_usize_add(v_i_3871_, v___x_3879_);
v___x_3881_ = lean_array_uset(v_bs_x27_3876_, v_i_3871_, v___y_3878_);
v_i_3871_ = v___x_3880_;
v_bs_3872_ = v___x_3881_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___boxed(lean_object* v_sz_3898_, lean_object* v_i_3899_, lean_object* v_bs_3900_){
_start:
{
size_t v_sz_boxed_3901_; size_t v_i_boxed_3902_; lean_object* v_res_3903_; 
v_sz_boxed_3901_ = lean_unbox_usize(v_sz_3898_);
lean_dec(v_sz_3898_);
v_i_boxed_3902_ = lean_unbox_usize(v_i_3899_);
lean_dec(v_i_3899_);
v_res_3903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_boxed_3901_, v_i_boxed_3902_, v_bs_3900_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(lean_object* v_as_3904_, lean_object* v_j_3905_){
_start:
{
lean_object* v___x_3910_; uint8_t v___x_3911_; 
v___x_3910_ = lean_array_get_size(v_as_3904_);
v___x_3911_ = lean_nat_dec_lt(v_j_3905_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; 
lean_dec(v_j_3905_);
v___x_3912_ = lean_box(0);
return v___x_3912_;
}
else
{
lean_object* v___x_3913_; 
v___x_3913_ = lean_array_fget(v_as_3904_, v_j_3905_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_dec_ref_known(v___x_3913_, 1);
goto v___jp_3906_;
}
else
{
lean_object* v_docs_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3924_; 
v_docs_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_docs_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v___x_3918_ = lean_array_get_size(v_docs_3914_);
lean_dec_ref(v_docs_3914_);
v___x_3919_ = lean_unsigned_to_nat(0u);
v___x_3920_ = lean_nat_dec_eq(v___x_3918_, v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3922_; 
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v_j_3905_);
v___x_3922_ = v___x_3916_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_j_3905_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
else
{
lean_del_object(v___x_3916_);
goto v___jp_3906_;
}
}
}
}
v___jp_3906_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = lean_unsigned_to_nat(1u);
v___x_3908_ = lean_nat_add(v_j_3905_, v___x_3907_);
lean_dec(v_j_3905_);
v_j_3905_ = v___x_3908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2___boxed(lean_object* v_as_3925_, lean_object* v_j_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_as_3925_, v_j_3926_);
lean_dec_ref(v_as_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(size_t v_sz_3928_, size_t v_i_3929_, lean_object* v_bs_3930_){
_start:
{
uint8_t v___x_3931_; 
v___x_3931_ = lean_usize_dec_lt(v_i_3929_, v_sz_3928_);
if (v___x_3931_ == 0)
{
return v_bs_3930_;
}
else
{
lean_object* v_v_3932_; lean_object* v___x_3933_; lean_object* v_bs_x27_3934_; lean_object* v___y_3936_; 
v_v_3932_ = lean_array_uget(v_bs_3930_, v_i_3929_);
v___x_3933_ = lean_unsigned_to_nat(0u);
v_bs_x27_3934_ = lean_array_uset(v_bs_3930_, v_i_3929_, v___x_3933_);
if (lean_obj_tag(v_v_3932_) == 0)
{
lean_object* v_doc_3941_; 
v_doc_3941_ = lean_ctor_get(v_v_3932_, 0);
lean_inc_ref(v_doc_3941_);
lean_dec_ref_known(v_v_3932_, 1);
v___y_3936_ = v_doc_3941_;
goto v___jp_3935_;
}
else
{
lean_object* v_docs_3942_; lean_object* v___x_3943_; 
v_docs_3942_ = lean_ctor_get(v_v_3932_, 0);
lean_inc_ref(v_docs_3942_);
lean_dec_ref_known(v_v_3932_, 1);
v___x_3943_ = l_Lean_Fmt_Layouts_fill(v_docs_3942_);
lean_dec_ref(v_docs_3942_);
v___y_3936_ = v___x_3943_;
goto v___jp_3935_;
}
v___jp_3935_:
{
size_t v___x_3937_; size_t v___x_3938_; lean_object* v___x_3939_; 
v___x_3937_ = ((size_t)1ULL);
v___x_3938_ = lean_usize_add(v_i_3929_, v___x_3937_);
v___x_3939_ = lean_array_uset(v_bs_x27_3934_, v_i_3929_, v___y_3936_);
v_i_3929_ = v___x_3938_;
v_bs_3930_ = v___x_3939_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0___boxed(lean_object* v_sz_3944_, lean_object* v_i_3945_, lean_object* v_bs_3946_){
_start:
{
size_t v_sz_boxed_3947_; size_t v_i_boxed_3948_; lean_object* v_res_3949_; 
v_sz_boxed_3947_ = lean_unbox_usize(v_sz_3944_);
lean_dec(v_sz_3944_);
v_i_boxed_3948_ = lean_unbox_usize(v_i_3945_);
lean_dec(v_i_3945_);
v_res_3949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_boxed_3947_, v_i_boxed_3948_, v_bs_3946_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object* v_lb_3951_, lean_object* v_terms_3952_, lean_object* v_rb_3953_){
_start:
{
lean_object* v_terms_3955_; size_t v_sz_3963_; size_t v___x_3964_; lean_object* v_terms_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; 
v_sz_3963_ = lean_array_size(v_terms_3952_);
v___x_3964_ = ((size_t)0ULL);
v_terms_3965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_3963_, v___x_3964_, v_terms_3952_);
v___x_3966_ = lean_unsigned_to_nat(1u);
v___x_3967_ = lean_array_get_size(v_terms_3965_);
v___x_3968_ = lean_nat_dec_lt(v___x_3966_, v___x_3967_);
if (v___x_3968_ == 0)
{
v_terms_3955_ = v_terms_3965_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_3969_; lean_object* v_firstElemsIdx_x3f_3970_; 
v___x_3969_ = lean_unsigned_to_nat(0u);
v_firstElemsIdx_x3f_3970_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_terms_3965_, v___x_3969_);
if (lean_obj_tag(v_firstElemsIdx_x3f_3970_) == 1)
{
lean_object* v_val_3971_; uint8_t v___x_3972_; 
v_val_3971_ = lean_ctor_get(v_firstElemsIdx_x3f_3970_, 0);
lean_inc(v_val_3971_);
lean_dec_ref_known(v_firstElemsIdx_x3f_3970_, 1);
v___x_3972_ = lean_nat_dec_lt(v_val_3971_, v___x_3967_);
if (v___x_3972_ == 0)
{
lean_dec(v_val_3971_);
v_terms_3955_ = v_terms_3965_;
goto v___jp_3954_;
}
else
{
lean_object* v_v_3973_; lean_object* v___x_3974_; lean_object* v_xs_x27_3975_; lean_object* v___y_3977_; 
v_v_3973_ = lean_array_fget(v_terms_3965_, v_val_3971_);
v___x_3974_ = lean_box(0);
v_xs_x27_3975_ = lean_array_fset(v_terms_3965_, v_val_3971_, v___x_3974_);
if (lean_obj_tag(v_v_3973_) == 0)
{
v___y_3977_ = v_v_3973_;
goto v___jp_3976_;
}
else
{
lean_object* v_docs_3979_; lean_object* v___x_3980_; uint8_t v___x_3981_; 
v_docs_3979_ = lean_ctor_get(v_v_3973_, 0);
v___x_3980_ = lean_array_get_size(v_docs_3979_);
v___x_3981_ = lean_nat_dec_lt(v___x_3969_, v___x_3980_);
if (v___x_3981_ == 0)
{
v___y_3977_ = v_v_3973_;
goto v___jp_3976_;
}
else
{
lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3992_; 
lean_inc_ref(v_docs_3979_);
v_isSharedCheck_3992_ = !lean_is_exclusive(v_v_3973_);
if (v_isSharedCheck_3992_ == 0)
{
lean_object* v_unused_3993_; 
v_unused_3993_ = lean_ctor_get(v_v_3973_, 0);
lean_dec(v_unused_3993_);
v___x_3983_ = v_v_3973_;
v_isShared_3984_ = v_isSharedCheck_3992_;
goto v_resetjp_3982_;
}
else
{
lean_dec(v_v_3973_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3992_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v_v_3985_; lean_object* v_xs_x27_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
v_v_3985_ = lean_array_fget(v_docs_3979_, v___x_3969_);
v_xs_x27_3986_ = lean_array_fset(v_docs_3979_, v___x_3969_, v___x_3974_);
v___x_3987_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3985_);
v___x_3988_ = lean_array_fset(v_xs_x27_3986_, v___x_3969_, v___x_3987_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v___x_3988_);
v___x_3990_ = v___x_3983_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
v___y_3977_ = v___x_3990_;
goto v___jp_3976_;
}
}
}
}
v___jp_3976_:
{
lean_object* v___x_3978_; 
v___x_3978_ = lean_array_fset(v_xs_x27_3975_, v_val_3971_, v___y_3977_);
lean_dec(v_val_3971_);
v_terms_3955_ = v___x_3978_;
goto v___jp_3954_;
}
}
}
else
{
lean_dec(v_firstElemsIdx_x3f_3970_);
v_terms_3955_ = v_terms_3965_;
goto v___jp_3954_;
}
}
v___jp_3954_:
{
lean_object* v___x_3956_; size_t v_sz_3957_; size_t v___x_3958_; lean_object* v_terms_x27_3959_; lean_object* v_terms_x27_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3956_ = ((lean_object*)(l_Lean_Fmt_Layouts_metaApplication___closed__0));
v_sz_3957_ = lean_array_size(v_terms_3955_);
v___x_3958_ = ((size_t)0ULL);
v_terms_x27_3959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_3957_, v___x_3958_, v_terms_3955_);
v_terms_x27_3960_ = l_Lean_Fmt_Layouts_sepFill(v___x_3956_, v_terms_x27_3959_);
lean_dec_ref(v_terms_x27_3959_);
v___x_3961_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_3962_ = l_Lean_Fmt_Layouts_bracketed(v_lb_3951_, v_terms_x27_3960_, v_rb_3953_, v___x_3961_);
return v___x_3962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object* v_chain_3996_){
_start:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = ((lean_object*)(l_Lean_Fmt_Layouts_pipeOperator___closed__0));
v___x_3998_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_3996_, v___x_3997_);
return v___x_3998_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0(void){
_start:
{
uint8_t v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3999_ = 1;
v___x_4000_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4001_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
lean_ctor_set_uint8(v___x_4001_, sizeof(void*)*1, v___x_3999_);
return v___x_4001_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default(void){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_obj_once(&l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0, &l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0);
return v___x_4002_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock(void){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0(lean_object* v_block_4004_){
_start:
{
uint8_t v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = 1;
v___x_4006_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4006_, 0, v_block_4004_);
lean_ctor_set_uint8(v___x_4006_, sizeof(void*)*1, v___x_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(lean_object* v_val_4009_, uint8_t v___x_4010_, lean_object* v___x_4011_, lean_object* v_____r_4012_, lean_object* v_stickyAcc_4013_){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4014_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_4009_, v___x_4010_);
v___x_4015_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v___x_4011_, v_stickyAcc_4013_, v___x_4014_);
lean_dec(v___x_4014_);
v___x_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1___boxed(lean_object* v_val_4017_, lean_object* v___x_4018_, lean_object* v___x_4019_, lean_object* v_____r_4020_, lean_object* v_stickyAcc_4021_){
_start:
{
uint8_t v___x_1444__boxed_4022_; lean_object* v_res_4023_; 
v___x_1444__boxed_4022_ = lean_unbox(v___x_4018_);
v_res_4023_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4017_, v___x_1444__boxed_4022_, v___x_4019_, v_____r_4020_, v_stickyAcc_4021_);
lean_dec_ref(v_val_4017_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(lean_object* v_upperBound_4024_, lean_object* v___y_4025_, lean_object* v___x_4026_, lean_object* v_a_4027_, lean_object* v_b_4028_){
_start:
{
uint8_t v___x_4029_; 
v___x_4029_ = lean_nat_dec_lt(v_a_4027_, v_upperBound_4024_);
if (v___x_4029_ == 0)
{
lean_dec(v_a_4027_);
return v_b_4028_;
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v_block_4032_; uint8_t v_hardNestedIfFirst_4033_; lean_object* v___x_4034_; lean_object* v_a_4036_; lean_object* v___y_4040_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4030_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4031_ = lean_array_get_borrowed(v___x_4030_, v___y_4025_, v_a_4027_);
v_block_4032_ = lean_ctor_get(v___x_4031_, 0);
v_hardNestedIfFirst_4033_ = lean_ctor_get_uint8(v___x_4031_, sizeof(void*)*1);
v___x_4034_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_b_4028_);
v___x_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4043_, 0, v_b_4028_);
v___x_4044_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_4045_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4043_, v___x_4044_);
v___x_4046_ = lean_box(0);
lean_inc_ref_n(v_block_4032_, 2);
v___x_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4047_, 0, v_block_4032_);
v___x_4048_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4046_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
lean_ctor_set(v___x_4048_, 2, v___x_4046_);
v___x_4049_ = lean_unsigned_to_nat(2u);
v___x_4050_ = lean_mk_empty_array_with_capacity(v___x_4049_);
lean_inc_ref(v___x_4050_);
v___x_4051_ = lean_array_push(v___x_4050_, v___x_4045_);
v___x_4052_ = lean_array_push(v___x_4051_, v___x_4048_);
v___x_4053_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4052_);
lean_dec_ref(v___x_4052_);
v___x_4054_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4053_);
v___x_4055_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_block_4032_);
if (lean_obj_tag(v___x_4055_) == 1)
{
lean_object* v_val_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4080_; 
v_val_4056_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4058_ = v___x_4055_;
v_isShared_4059_ = v_isSharedCheck_4080_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_val_4056_);
lean_dec(v___x_4055_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4080_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v_stickyVariant_4060_; lean_object* v___x_4061_; lean_object* v___x_4063_; 
v_stickyVariant_4060_ = lean_ctor_get(v_val_4056_, 0);
v___x_4061_ = l_Lean_Fmt_TaggedDoc_flattened(v_b_4028_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 0, v___x_4061_);
v___x_4063_ = v___x_4058_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4064_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4065_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4063_, v___x_4064_);
lean_inc_ref(v_stickyVariant_4060_);
v___x_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4066_, 0, v_stickyVariant_4060_);
v___x_4067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4046_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
lean_ctor_set(v___x_4067_, 2, v___x_4046_);
v___x_4068_ = lean_array_push(v___x_4050_, v___x_4065_);
v___x_4069_ = lean_array_push(v___x_4068_, v___x_4067_);
v___x_4070_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4069_);
lean_dec_ref(v___x_4069_);
if (v_hardNestedIfFirst_4033_ == 0)
{
goto v___jp_4071_;
}
else
{
lean_object* v___x_4074_; uint8_t v___x_4075_; 
v___x_4074_ = lean_nat_sub(v___x_4026_, v___x_4034_);
v___x_4075_ = lean_nat_dec_lt(v_a_4027_, v___x_4074_);
lean_dec(v___x_4074_);
if (v___x_4075_ == 0)
{
goto v___jp_4071_;
}
else
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_4070_);
v___x_4077_ = lean_box(0);
v___x_4078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4056_, v___x_4029_, v___x_4054_, v___x_4077_, v___x_4076_);
lean_dec(v_val_4056_);
v___y_4040_ = v___x_4078_;
goto v___jp_4039_;
}
}
v___jp_4071_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = lean_box(0);
v___x_4073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4056_, v___x_4029_, v___x_4054_, v___x_4072_, v___x_4070_);
lean_dec(v_val_4056_);
v___y_4040_ = v___x_4073_;
goto v___jp_4039_;
}
}
}
}
else
{
lean_dec(v___x_4055_);
lean_dec_ref(v___x_4050_);
lean_dec_ref(v_b_4028_);
v_a_4036_ = v___x_4054_;
goto v___jp_4035_;
}
v___jp_4035_:
{
lean_object* v___x_4037_; 
v___x_4037_ = lean_nat_add(v_a_4027_, v___x_4034_);
lean_dec(v_a_4027_);
v_a_4027_ = v___x_4037_;
v_b_4028_ = v_a_4036_;
goto _start;
}
v___jp_4039_:
{
if (lean_obj_tag(v___y_4040_) == 0)
{
lean_object* v_a_4041_; 
lean_dec(v_a_4027_);
v_a_4041_ = lean_ctor_get(v___y_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___y_4040_, 1);
return v_a_4041_;
}
else
{
lean_object* v_a_4042_; 
v_a_4042_ = lean_ctor_get(v___y_4040_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___y_4040_, 1);
v_a_4036_ = v_a_4042_;
goto v___jp_4035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___boxed(lean_object* v_upperBound_4081_, lean_object* v___y_4082_, lean_object* v___x_4083_, lean_object* v_a_4084_, lean_object* v_b_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4081_, v___y_4082_, v___x_4083_, v_a_4084_, v_b_4085_);
lean_dec(v___x_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v_upperBound_4081_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(lean_object* v_as_4087_, size_t v_i_4088_, size_t v_stop_4089_, lean_object* v_b_4090_){
_start:
{
lean_object* v___y_4092_; uint8_t v___x_4096_; 
v___x_4096_ = lean_usize_dec_eq(v_i_4088_, v_stop_4089_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v_block_4098_; uint8_t v___x_4099_; 
v___x_4097_ = lean_array_uget_borrowed(v_as_4087_, v_i_4088_);
v_block_4098_ = lean_ctor_get(v___x_4097_, 0);
v___x_4099_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_block_4098_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4100_; 
lean_inc(v___x_4097_);
v___x_4100_ = lean_array_push(v_b_4090_, v___x_4097_);
v___y_4092_ = v___x_4100_;
goto v___jp_4091_;
}
else
{
v___y_4092_ = v_b_4090_;
goto v___jp_4091_;
}
}
else
{
return v_b_4090_;
}
v___jp_4091_:
{
size_t v___x_4093_; size_t v___x_4094_; 
v___x_4093_ = ((size_t)1ULL);
v___x_4094_ = lean_usize_add(v_i_4088_, v___x_4093_);
v_i_4088_ = v___x_4094_;
v_b_4090_ = v___y_4092_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1___boxed(lean_object* v_as_4101_, lean_object* v_i_4102_, lean_object* v_stop_4103_, lean_object* v_b_4104_){
_start:
{
size_t v_i_boxed_4105_; size_t v_stop_boxed_4106_; lean_object* v_res_4107_; 
v_i_boxed_4105_ = lean_unbox_usize(v_i_4102_);
lean_dec(v_i_4102_);
v_stop_boxed_4106_ = lean_unbox_usize(v_stop_4103_);
lean_dec(v_stop_4103_);
v_res_4107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_as_4101_, v_i_boxed_4105_, v_stop_boxed_4106_, v_b_4104_);
lean_dec_ref(v_as_4101_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks(lean_object* v_blocks_4110_, uint8_t v_format_4111_){
_start:
{
lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___y_4122_; lean_object* v___x_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4119_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4132_ = lean_array_get_size(v_blocks_4110_);
v___x_4133_ = ((lean_object*)(l_Lean_Fmt_Layouts_blocks___closed__0));
v___x_4134_ = lean_nat_dec_lt(v___x_4120_, v___x_4132_);
if (v___x_4134_ == 0)
{
v___y_4122_ = v___x_4133_;
goto v___jp_4121_;
}
else
{
size_t v___x_4135_; size_t v___x_4136_; lean_object* v___x_4137_; 
v___x_4135_ = ((size_t)0ULL);
v___x_4136_ = lean_usize_of_nat(v___x_4132_);
v___x_4137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4110_, v___x_4135_, v___x_4136_, v___x_4133_);
v___y_4122_ = v___x_4137_;
goto v___jp_4121_;
}
v___jp_4112_:
{
lean_object* v___x_4117_; 
v___x_4117_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v___y_4114_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4114_);
if (v_format_4111_ == 0)
{
return v___x_4117_;
}
else
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4117_);
return v___x_4118_;
}
}
v___jp_4121_:
{
lean_object* v___x_4123_; uint8_t v___x_4124_; 
v___x_4123_ = lean_array_get_size(v___y_4122_);
v___x_4124_ = lean_nat_dec_eq(v___x_4123_, v___x_4120_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; lean_object* v_block_4126_; uint8_t v_hardNestedIfFirst_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
v___x_4125_ = lean_array_get_borrowed(v___x_4119_, v___y_4122_, v___x_4120_);
v_block_4126_ = lean_ctor_get(v___x_4125_, 0);
v_hardNestedIfFirst_4127_ = lean_ctor_get_uint8(v___x_4125_, sizeof(void*)*1);
v___x_4128_ = lean_unsigned_to_nat(1u);
v___x_4129_ = lean_nat_dec_eq(v___x_4123_, v___x_4128_);
if (v___x_4129_ == 0)
{
if (v_hardNestedIfFirst_4127_ == 0)
{
lean_inc_ref(v_block_4126_);
v___y_4113_ = v___y_4122_;
v___y_4114_ = v___x_4123_;
v___y_4115_ = v___x_4128_;
v___y_4116_ = v_block_4126_;
goto v___jp_4112_;
}
else
{
lean_object* v___x_4130_; 
lean_inc_ref(v_block_4126_);
v___x_4130_ = l_Lean_Fmt_TaggedDoc_hardNested(v_block_4126_);
v___y_4113_ = v___y_4122_;
v___y_4114_ = v___x_4123_;
v___y_4115_ = v___x_4128_;
v___y_4116_ = v___x_4130_;
goto v___jp_4112_;
}
}
else
{
lean_inc_ref(v_block_4126_);
lean_dec_ref(v___y_4122_);
return v_block_4126_;
}
}
else
{
lean_object* v___x_4131_; 
lean_dec_ref(v___y_4122_);
v___x_4131_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_4131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks___boxed(lean_object* v_blocks_4138_, lean_object* v_format_4139_){
_start:
{
uint8_t v_format_boxed_4140_; lean_object* v_res_4141_; 
v_format_boxed_4140_ = lean_unbox(v_format_4139_);
v_res_4141_ = l_Lean_Fmt_Layouts_blocks(v_blocks_4138_, v_format_boxed_4140_);
lean_dec_ref(v_blocks_4138_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(lean_object* v_upperBound_4142_, lean_object* v___y_4143_, lean_object* v___x_4144_, lean_object* v_inst_4145_, lean_object* v_R_4146_, lean_object* v_a_4147_, lean_object* v_b_4148_, lean_object* v_c_4149_){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4142_, v___y_4143_, v___x_4144_, v_a_4147_, v_b_4148_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___boxed(lean_object* v_upperBound_4151_, lean_object* v___y_4152_, lean_object* v___x_4153_, lean_object* v_inst_4154_, lean_object* v_R_4155_, lean_object* v_a_4156_, lean_object* v_b_4157_, lean_object* v_c_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(v_upperBound_4151_, v___y_4152_, v___x_4153_, v_inst_4154_, v_R_4155_, v_a_4156_, v_b_4157_, v_c_4158_);
lean_dec(v___x_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v_upperBound_4151_);
return v_res_4159_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_tuple___closed__0(void){
_start:
{
uint8_t v___x_4160_; uint8_t v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4160_ = 0;
v___x_4161_ = 1;
v___x_4162_ = l_Lean_Fmt_TaggedDoc_break;
v___x_4163_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
lean_ctor_set_uint8(v___x_4163_, sizeof(void*)*1, v___x_4161_);
lean_ctor_set_uint8(v___x_4163_, sizeof(void*)*1 + 1, v___x_4160_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple(lean_object* v_sep_4164_, lean_object* v_lb_4165_, lean_object* v_fields_4166_, lean_object* v_rb_4167_){
_start:
{
uint8_t v___x_4168_; lean_object* v_fields_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; 
v___x_4168_ = 1;
lean_inc_ref(v_sep_4164_);
v_fields_4169_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4164_, v_fields_4166_, v___x_4168_);
v___x_4170_ = lean_array_get_size(v_fields_4169_);
v___x_4171_ = lean_unsigned_to_nat(1u);
v___x_4172_ = lean_nat_dec_eq(v___x_4170_, v___x_4171_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4173_; lean_object* v_fields_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4173_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v_fields_4174_ = l_Lean_Fmt_Layouts_sepArray(v_sep_4164_, v_fields_4169_, v___x_4173_);
lean_dec_ref(v_fields_4169_);
v___x_4175_ = lean_obj_once(&l_Lean_Fmt_Layouts_tuple___closed__0, &l_Lean_Fmt_Layouts_tuple___closed__0_once, _init_l_Lean_Fmt_Layouts_tuple___closed__0);
v___x_4176_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4165_, v_fields_4174_, v_rb_4167_, v___x_4175_);
return v___x_4176_;
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
lean_dec_ref(v_sep_4164_);
v___x_4177_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4178_ = lean_unsigned_to_nat(0u);
v___x_4179_ = lean_array_get(v___x_4177_, v_fields_4169_, v___x_4178_);
lean_dec_ref(v_fields_4169_);
v___x_4180_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_4181_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4165_, v___x_4179_, v_rb_4167_, v___x_4180_);
return v___x_4181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple___boxed(lean_object* v_sep_4182_, lean_object* v_lb_4183_, lean_object* v_fields_4184_, lean_object* v_rb_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_Fmt_Layouts_tuple(v_sep_4182_, v_lb_4183_, v_fields_4184_, v_rb_4185_);
lean_dec_ref(v_fields_4184_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection(lean_object* v_sep_4187_, lean_object* v_lb_4188_, lean_object* v_elems_4189_, lean_object* v_rb_4190_, lean_object* v_format_4191_){
_start:
{
lean_object* v___y_4193_; uint8_t v___x_4201_; lean_object* v_elems_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; 
v___x_4201_ = 1;
lean_inc_ref(v_sep_4187_);
v_elems_4202_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4187_, v_elems_4189_, v___x_4201_);
v___x_4203_ = lean_unsigned_to_nat(1u);
v___x_4204_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_elems_4202_);
v___x_4205_ = lean_nat_dec_lt(v___x_4203_, v___x_4204_);
lean_dec(v___x_4204_);
if (v___x_4205_ == 0)
{
v___y_4193_ = v_elems_4202_;
goto v___jp_4192_;
}
else
{
lean_object* v___x_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; 
v___x_4206_ = lean_unsigned_to_nat(0u);
v___x_4207_ = lean_array_get_size(v_elems_4202_);
v___x_4208_ = lean_nat_dec_lt(v___x_4206_, v___x_4207_);
if (v___x_4208_ == 0)
{
v___y_4193_ = v_elems_4202_;
goto v___jp_4192_;
}
else
{
lean_object* v_v_4209_; lean_object* v___x_4210_; lean_object* v_xs_x27_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_v_4209_ = lean_array_fget(v_elems_4202_, v___x_4206_);
v___x_4210_ = lean_box(0);
v_xs_x27_4211_ = lean_array_fset(v_elems_4202_, v___x_4206_, v___x_4210_);
v___x_4212_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4209_);
v___x_4213_ = lean_array_fset(v_xs_x27_4211_, v___x_4206_, v___x_4212_);
v___y_4193_ = v___x_4213_;
goto v___jp_4192_;
}
}
v___jp_4192_:
{
uint8_t v_spacing_4194_; lean_object* v___x_4195_; lean_object* v_fields_4196_; lean_object* v___x_4197_; lean_object* v_doc_4198_; uint8_t v___x_4199_; lean_object* v___x_4200_; 
v_spacing_4194_ = lean_ctor_get_uint8(v_format_4191_, 0);
v___x_4195_ = l_Lean_Fmt_Layouts_sepFill(v_sep_4187_, v___y_4193_);
lean_dec_ref(v___y_4193_);
v_fields_4196_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4195_);
v___x_4197_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_4197_, 0, v_spacing_4194_);
v_doc_4198_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4188_, v_fields_4196_, v_rb_4190_, v___x_4197_);
v___x_4199_ = 1;
lean_inc_ref(v_doc_4198_);
v___x_4200_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4198_, v_doc_4198_, v___x_4199_);
return v___x_4200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection___boxed(lean_object* v_sep_4214_, lean_object* v_lb_4215_, lean_object* v_elems_4216_, lean_object* v_rb_4217_, lean_object* v_format_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_Fmt_Layouts_collection(v_sep_4214_, v_lb_4215_, v_elems_4216_, v_rb_4217_, v_format_4218_);
lean_dec_ref(v_format_4218_);
lean_dec_ref(v_elems_4216_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0(lean_object* v_keyword_4220_, lean_object* v_collection_4221_){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4222_ = lean_unsigned_to_nat(2u);
v___x_4223_ = lean_mk_empty_array_with_capacity(v___x_4222_);
v___x_4224_ = lean_array_push(v___x_4223_, v_keyword_4220_);
v___x_4225_ = lean_array_push(v___x_4224_, v_collection_4221_);
v___x_4226_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4225_);
lean_dec_ref(v___x_4225_);
v___x_4227_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object* v_sep_4228_, lean_object* v_keyword_4229_, lean_object* v_lb_4230_, lean_object* v_elems_4231_, lean_object* v_rb_4232_, lean_object* v_format_4233_){
_start:
{
lean_object* v___f_4234_; lean_object* v_collection_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___f_4234_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0), 2, 1);
lean_closure_set(v___f_4234_, 0, v_keyword_4229_);
v_collection_4235_ = l_Lean_Fmt_Layouts_collection(v_sep_4228_, v_lb_4230_, v_elems_4231_, v_rb_4232_, v_format_4233_);
v___x_4236_ = lean_box(0);
v___x_4237_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_collection_4235_, v___f_4234_, v___x_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___boxed(lean_object* v_sep_4238_, lean_object* v_keyword_4239_, lean_object* v_lb_4240_, lean_object* v_elems_4241_, lean_object* v_rb_4242_, lean_object* v_format_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_Fmt_Layouts_keywordPrefixedCollection(v_sep_4238_, v_keyword_4239_, v_lb_4240_, v_elems_4241_, v_rb_4242_, v_format_4243_);
lean_dec_ref(v_format_4243_);
lean_dec_ref(v_elems_4241_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl(lean_object* v_x_4245_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = lean_obj_tag_nat(v_x_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl___boxed(lean_object* v_x_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl(v_x_4247_);
lean_dec(v_x_4247_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object* v_t_4249_, lean_object* v_k_4250_){
_start:
{
if (lean_obj_tag(v_t_4249_) == 0)
{
uint8_t v_respectPseudoAlignment_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_respectPseudoAlignment_4251_ = lean_ctor_get_uint8(v_t_4249_, 0);
v___x_4252_ = lean_box(v_respectPseudoAlignment_4251_);
v___x_4253_ = lean_apply_1(v_k_4250_, v___x_4252_);
return v___x_4253_;
}
else
{
return v_k_4250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object* v_t_4254_, lean_object* v_k_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4254_, v_k_4255_);
lean_dec(v_t_4254_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object* v_motive_4257_, lean_object* v_ctorIdx_4258_, lean_object* v_t_4259_, lean_object* v_h_4260_, lean_object* v_k_4261_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4259_, v_k_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object* v_motive_4263_, lean_object* v_ctorIdx_4264_, lean_object* v_t_4265_, lean_object* v_h_4266_, lean_object* v_k_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(v_motive_4263_, v_ctorIdx_4264_, v_t_4265_, v_h_4266_, v_k_4267_);
lean_dec(v_t_4265_);
lean_dec(v_ctorIdx_4264_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object* v_t_4269_, lean_object* v_local_4270_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4269_, v_local_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object* v_t_4272_, lean_object* v_local_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(v_t_4272_, v_local_4273_);
lean_dec(v_t_4272_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object* v_motive_4275_, lean_object* v_t_4276_, lean_object* v_h_4277_, lean_object* v_local_4278_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4276_, v_local_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object* v_motive_4280_, lean_object* v_t_4281_, lean_object* v_h_4282_, lean_object* v_local_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(v_motive_4280_, v_t_4281_, v_h_4282_, v_local_4283_);
lean_dec(v_t_4281_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object* v_t_4285_, lean_object* v_global_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4285_, v_global_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object* v_t_4288_, lean_object* v_global_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(v_t_4288_, v_global_4289_);
lean_dec(v_t_4288_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object* v_motive_4291_, lean_object* v_t_4292_, lean_object* v_h_4293_, lean_object* v_global_4294_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4292_, v_global_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object* v_motive_4296_, lean_object* v_t_4297_, lean_object* v_h_4298_, lean_object* v_global_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(v_motive_4296_, v_t_4297_, v_h_4298_, v_global_4299_);
lean_dec(v_t_4297_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(lean_object* v_as_4301_, size_t v_i_4302_, size_t v_stop_4303_, lean_object* v_b_4304_){
_start:
{
lean_object* v___y_4306_; uint8_t v___x_4310_; 
v___x_4310_ = lean_usize_dec_eq(v_i_4302_, v_stop_4303_);
if (v___x_4310_ == 0)
{
lean_object* v___x_4311_; uint8_t v___x_4312_; 
v___x_4311_ = lean_array_uget_borrowed(v_as_4301_, v_i_4302_);
v___x_4312_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_4311_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; 
lean_inc(v___x_4311_);
v___x_4313_ = lean_array_push(v_b_4304_, v___x_4311_);
v___y_4306_ = v___x_4313_;
goto v___jp_4305_;
}
else
{
v___y_4306_ = v_b_4304_;
goto v___jp_4305_;
}
}
else
{
return v_b_4304_;
}
v___jp_4305_:
{
size_t v___x_4307_; size_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = ((size_t)1ULL);
v___x_4308_ = lean_usize_add(v_i_4302_, v___x_4307_);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_as_4301_, v___x_4308_, v_stop_4303_, v___y_4306_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object* v_as_4314_, lean_object* v_i_4315_, lean_object* v_stop_4316_, lean_object* v_b_4317_){
_start:
{
size_t v_i_boxed_4318_; size_t v_stop_boxed_4319_; lean_object* v_res_4320_; 
v_i_boxed_4318_ = lean_unbox_usize(v_i_4315_);
lean_dec(v_i_4315_);
v_stop_boxed_4319_ = lean_unbox_usize(v_stop_4316_);
lean_dec(v_stop_4316_);
v_res_4320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_as_4314_, v_i_boxed_4318_, v_stop_boxed_4319_, v_b_4317_);
lean_dec_ref(v_as_4314_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(size_t v_sz_4321_, size_t v_i_4322_, lean_object* v_bs_4323_){
_start:
{
uint8_t v___x_4324_; 
v___x_4324_ = lean_usize_dec_lt(v_i_4322_, v_sz_4321_);
if (v___x_4324_ == 0)
{
return v_bs_4323_;
}
else
{
lean_object* v_v_4325_; lean_object* v___x_4326_; lean_object* v_bs_x27_4327_; lean_object* v___x_4328_; size_t v___x_4329_; size_t v___x_4330_; lean_object* v___x_4331_; 
v_v_4325_ = lean_array_uget(v_bs_4323_, v_i_4322_);
v___x_4326_ = lean_unsigned_to_nat(0u);
v_bs_x27_4327_ = lean_array_uset(v_bs_4323_, v_i_4322_, v___x_4326_);
v___x_4328_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(v_v_4325_);
v___x_4329_ = ((size_t)1ULL);
v___x_4330_ = lean_usize_add(v_i_4322_, v___x_4329_);
v___x_4331_ = lean_array_uset(v_bs_x27_4327_, v_i_4322_, v___x_4328_);
v_i_4322_ = v___x_4330_;
v_bs_4323_ = v___x_4331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3___boxed(lean_object* v_sz_4333_, lean_object* v_i_4334_, lean_object* v_bs_4335_){
_start:
{
size_t v_sz_boxed_4336_; size_t v_i_boxed_4337_; lean_object* v_res_4338_; 
v_sz_boxed_4336_ = lean_unbox_usize(v_sz_4333_);
lean_dec(v_sz_4333_);
v_i_boxed_4337_ = lean_unbox_usize(v_i_4334_);
lean_dec(v_i_4334_);
v_res_4338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(v_sz_boxed_4336_, v_i_boxed_4337_, v_bs_4335_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(lean_object* v_as_4339_, size_t v_i_4340_, size_t v_stop_4341_, lean_object* v_b_4342_){
_start:
{
lean_object* v___y_4344_; uint8_t v___x_4348_; 
v___x_4348_ = lean_usize_dec_eq(v_i_4340_, v_stop_4341_);
if (v___x_4348_ == 0)
{
lean_object* v___x_4349_; lean_object* v___y_4351_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4349_ = lean_unsigned_to_nat(0u);
v___x_4355_ = lean_array_uget_borrowed(v_as_4339_, v_i_4340_);
v___x_4356_ = lean_array_get_size(v___x_4355_);
v___x_4357_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4358_ = lean_nat_dec_lt(v___x_4349_, v___x_4356_);
if (v___x_4358_ == 0)
{
v___y_4351_ = v___x_4357_;
goto v___jp_4350_;
}
else
{
size_t v___x_4359_; size_t v___x_4360_; lean_object* v___x_4361_; 
v___x_4359_ = ((size_t)0ULL);
v___x_4360_ = lean_usize_of_nat(v___x_4356_);
v___x_4361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v___x_4355_, v___x_4359_, v___x_4360_, v___x_4357_);
v___y_4351_ = v___x_4361_;
goto v___jp_4350_;
}
v___jp_4350_:
{
lean_object* v___x_4352_; uint8_t v___x_4353_; 
v___x_4352_ = lean_array_get_size(v___y_4351_);
v___x_4353_ = lean_nat_dec_eq(v___x_4352_, v___x_4349_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; 
v___x_4354_ = lean_array_push(v_b_4342_, v___y_4351_);
v___y_4344_ = v___x_4354_;
goto v___jp_4343_;
}
else
{
lean_dec_ref(v___y_4351_);
v___y_4344_ = v_b_4342_;
goto v___jp_4343_;
}
}
}
else
{
return v_b_4342_;
}
v___jp_4343_:
{
size_t v___x_4345_; size_t v___x_4346_; 
v___x_4345_ = ((size_t)1ULL);
v___x_4346_ = lean_usize_add(v_i_4340_, v___x_4345_);
v_i_4340_ = v___x_4346_;
v_b_4342_ = v___y_4344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1___boxed(lean_object* v_as_4362_, lean_object* v_i_4363_, lean_object* v_stop_4364_, lean_object* v_b_4365_){
_start:
{
size_t v_i_boxed_4366_; size_t v_stop_boxed_4367_; lean_object* v_res_4368_; 
v_i_boxed_4366_ = lean_unbox_usize(v_i_4363_);
lean_dec(v_i_4363_);
v_stop_boxed_4367_ = lean_unbox_usize(v_stop_4364_);
lean_dec(v_stop_4364_);
v_res_4368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4362_, v_i_boxed_4366_, v_stop_boxed_4367_, v_b_4365_);
lean_dec_ref(v_as_4362_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(lean_object* v_as_4371_, lean_object* v_start_4372_, lean_object* v_stop_4373_){
_start:
{
lean_object* v___x_4374_; uint8_t v___x_4375_; 
v___x_4374_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0));
v___x_4375_ = lean_nat_dec_lt(v_start_4372_, v_stop_4373_);
if (v___x_4375_ == 0)
{
return v___x_4374_;
}
else
{
lean_object* v___x_4376_; uint8_t v___x_4377_; 
v___x_4376_ = lean_array_get_size(v_as_4371_);
v___x_4377_ = lean_nat_dec_le(v_stop_4373_, v___x_4376_);
if (v___x_4377_ == 0)
{
uint8_t v___x_4378_; 
v___x_4378_ = lean_nat_dec_lt(v_start_4372_, v___x_4376_);
if (v___x_4378_ == 0)
{
return v___x_4374_;
}
else
{
size_t v___x_4379_; size_t v___x_4380_; lean_object* v___x_4381_; 
v___x_4379_ = lean_usize_of_nat(v_start_4372_);
v___x_4380_ = lean_usize_of_nat(v___x_4376_);
v___x_4381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4371_, v___x_4379_, v___x_4380_, v___x_4374_);
return v___x_4381_;
}
}
else
{
size_t v___x_4382_; size_t v___x_4383_; lean_object* v___x_4384_; 
v___x_4382_ = lean_usize_of_nat(v_start_4372_);
v___x_4383_ = lean_usize_of_nat(v_stop_4373_);
v___x_4384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4371_, v___x_4382_, v___x_4383_, v___x_4374_);
return v___x_4384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___boxed(lean_object* v_as_4385_, lean_object* v_start_4386_, lean_object* v_stop_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v_as_4385_, v_start_4386_, v_stop_4387_);
lean_dec(v_stop_4387_);
lean_dec(v_start_4386_);
lean_dec_ref(v_as_4385_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(lean_object* v_as_4389_, size_t v_i_4390_, size_t v_stop_4391_, lean_object* v_b_4392_){
_start:
{
lean_object* v___y_4394_; uint8_t v___x_4398_; 
v___x_4398_ = lean_usize_dec_eq(v_i_4390_, v_stop_4391_);
if (v___x_4398_ == 0)
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v_group_4402_; lean_object* v___x_4403_; uint8_t v___x_4404_; 
v___x_4399_ = lean_unsigned_to_nat(0u);
v___x_4400_ = lean_array_uget_borrowed(v_as_4389_, v_i_4390_);
v___x_4401_ = lean_array_get_size(v___x_4400_);
v_group_4402_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v___x_4400_, v___x_4399_, v___x_4401_);
v___x_4403_ = lean_array_get_size(v_group_4402_);
v___x_4404_ = lean_nat_dec_eq(v___x_4403_, v___x_4399_);
if (v___x_4404_ == 0)
{
lean_object* v___x_4405_; 
v___x_4405_ = lean_array_push(v_b_4392_, v_group_4402_);
v___y_4394_ = v___x_4405_;
goto v___jp_4393_;
}
else
{
lean_dec_ref(v_group_4402_);
v___y_4394_ = v_b_4392_;
goto v___jp_4393_;
}
}
else
{
return v_b_4392_;
}
v___jp_4393_:
{
size_t v___x_4395_; size_t v___x_4396_; 
v___x_4395_ = ((size_t)1ULL);
v___x_4396_ = lean_usize_add(v_i_4390_, v___x_4395_);
v_i_4390_ = v___x_4396_;
v_b_4392_ = v___y_4394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3___boxed(lean_object* v_as_4406_, lean_object* v_i_4407_, lean_object* v_stop_4408_, lean_object* v_b_4409_){
_start:
{
size_t v_i_boxed_4410_; size_t v_stop_boxed_4411_; lean_object* v_res_4412_; 
v_i_boxed_4410_ = lean_unbox_usize(v_i_4407_);
lean_dec(v_i_4407_);
v_stop_boxed_4411_ = lean_unbox_usize(v_stop_4408_);
lean_dec(v_stop_4408_);
v_res_4412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4406_, v_i_boxed_4410_, v_stop_boxed_4411_, v_b_4409_);
lean_dec_ref(v_as_4406_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(lean_object* v_as_4415_, lean_object* v_start_4416_, lean_object* v_stop_4417_){
_start:
{
lean_object* v___x_4418_; uint8_t v___x_4419_; 
v___x_4418_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___closed__0));
v___x_4419_ = lean_nat_dec_lt(v_start_4416_, v_stop_4417_);
if (v___x_4419_ == 0)
{
return v___x_4418_;
}
else
{
lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4420_ = lean_array_get_size(v_as_4415_);
v___x_4421_ = lean_nat_dec_le(v_stop_4417_, v___x_4420_);
if (v___x_4421_ == 0)
{
uint8_t v___x_4422_; 
v___x_4422_ = lean_nat_dec_lt(v_start_4416_, v___x_4420_);
if (v___x_4422_ == 0)
{
return v___x_4418_;
}
else
{
size_t v___x_4423_; size_t v___x_4424_; lean_object* v___x_4425_; 
v___x_4423_ = lean_usize_of_nat(v_start_4416_);
v___x_4424_ = lean_usize_of_nat(v___x_4420_);
v___x_4425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4415_, v___x_4423_, v___x_4424_, v___x_4418_);
return v___x_4425_;
}
}
else
{
size_t v___x_4426_; size_t v___x_4427_; lean_object* v___x_4428_; 
v___x_4426_ = lean_usize_of_nat(v_start_4416_);
v___x_4427_ = lean_usize_of_nat(v_stop_4417_);
v___x_4428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4415_, v___x_4426_, v___x_4427_, v___x_4418_);
return v___x_4428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___boxed(lean_object* v_as_4429_, lean_object* v_start_4430_, lean_object* v_stop_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_as_4429_, v_start_4430_, v_stop_4431_);
lean_dec(v_stop_4431_);
lean_dec(v_start_4430_);
lean_dec_ref(v_as_4429_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object* v_lvals_4433_, lean_object* v_binderGroups_4434_, lean_object* v_typeAscriptionTk_4435_, lean_object* v_type_4436_, lean_object* v_kind_4437_, lean_object* v_lvalsLayout_4438_){
_start:
{
uint8_t v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; uint8_t v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___x_4465_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4478_; lean_object* v___x_4488_; lean_object* v___x_4489_; uint8_t v___x_4490_; 
v___x_4465_ = lean_unsigned_to_nat(0u);
v___x_4488_ = lean_array_get_size(v_lvals_4433_);
v___x_4489_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4490_ = lean_nat_dec_lt(v___x_4465_, v___x_4488_);
if (v___x_4490_ == 0)
{
v___y_4478_ = v___x_4489_;
goto v___jp_4477_;
}
else
{
size_t v___x_4491_; size_t v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = ((size_t)0ULL);
v___x_4492_ = lean_usize_of_nat(v___x_4488_);
v___x_4493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_lvals_4433_, v___x_4491_, v___x_4492_, v___x_4489_);
v___y_4478_ = v___x_4493_;
goto v___jp_4477_;
}
v___jp_4439_:
{
size_t v_sz_4444_; size_t v___x_4445_; lean_object* v___x_4446_; lean_object* v_binderGroups_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v_sz_4444_ = lean_array_size(v___y_4441_);
v___x_4445_ = ((size_t)0ULL);
v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(v_sz_4444_, v___x_4445_, v___y_4441_);
v_binderGroups_4447_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4446_, v___y_4440_);
lean_dec_ref(v___x_4446_);
v___x_4448_ = lean_apply_1(v_lvalsLayout_4438_, v___y_4442_);
v___x_4449_ = lean_unsigned_to_nat(2u);
v___x_4450_ = lean_mk_empty_array_with_capacity(v___x_4449_);
v___x_4451_ = lean_array_push(v___x_4450_, v___x_4448_);
v___x_4452_ = lean_array_push(v___x_4451_, v_binderGroups_4447_);
v___x_4453_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4452_, v___y_4440_);
lean_dec_ref(v___x_4452_);
v___x_4454_ = l_Lean_Fmt_Layouts_typeAscription(v___x_4453_, v_typeAscriptionTk_4435_, v_type_4436_, v___y_4443_);
lean_dec_ref(v___y_4443_);
v___x_4455_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4454_);
return v___x_4455_;
}
v___jp_4456_:
{
if (lean_obj_tag(v_kind_4437_) == 0)
{
uint8_t v_respectPseudoAlignment_4460_; uint8_t v___x_4461_; lean_object* v___x_4462_; 
v_respectPseudoAlignment_4460_ = lean_ctor_get_uint8(v_kind_4437_, 0);
v___x_4461_ = 0;
v___x_4462_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4462_, 0, v___x_4461_);
lean_ctor_set_uint8(v___x_4462_, 1, v___x_4461_);
lean_ctor_set_uint8(v___x_4462_, 2, v___y_4457_);
lean_ctor_set_uint8(v___x_4462_, 3, v_respectPseudoAlignment_4460_);
v___y_4440_ = v___y_4457_;
v___y_4441_ = v___y_4458_;
v___y_4442_ = v___y_4459_;
v___y_4443_ = v___x_4462_;
goto v___jp_4439_;
}
else
{
uint8_t v___x_4463_; lean_object* v___x_4464_; 
v___x_4463_ = 0;
v___x_4464_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_4464_, 0, v___x_4463_);
lean_ctor_set_uint8(v___x_4464_, 1, v___x_4463_);
lean_ctor_set_uint8(v___x_4464_, 2, v___y_4457_);
lean_ctor_set_uint8(v___x_4464_, 3, v___x_4463_);
lean_ctor_set_uint8(v___x_4464_, 4, v___x_4463_);
v___y_4440_ = v___y_4457_;
v___y_4441_ = v___y_4458_;
v___y_4442_ = v___y_4459_;
v___y_4443_ = v___x_4464_;
goto v___jp_4439_;
}
}
v___jp_4466_:
{
uint8_t v___x_4469_; lean_object* v___x_4470_; uint8_t v___x_4471_; 
v___x_4469_ = 1;
v___x_4470_ = lean_array_get_size(v___y_4467_);
v___x_4471_ = lean_nat_dec_lt(v___x_4465_, v___x_4470_);
if (v___x_4471_ == 0)
{
v___y_4457_ = v___x_4469_;
v___y_4458_ = v___y_4468_;
v___y_4459_ = v___y_4467_;
goto v___jp_4456_;
}
else
{
lean_object* v_v_4472_; lean_object* v___x_4473_; lean_object* v_xs_x27_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v_v_4472_ = lean_array_fget(v___y_4467_, v___x_4465_);
v___x_4473_ = lean_box(0);
v_xs_x27_4474_ = lean_array_fset(v___y_4467_, v___x_4465_, v___x_4473_);
v___x_4475_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4472_);
v___x_4476_ = lean_array_fset(v_xs_x27_4474_, v___x_4465_, v___x_4475_);
v___y_4457_ = v___x_4469_;
v___y_4458_ = v___y_4468_;
v___y_4459_ = v___x_4476_;
goto v___jp_4456_;
}
}
v___jp_4477_:
{
lean_object* v___x_4479_; lean_object* v_binderGroups_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; uint8_t v___x_4483_; 
v___x_4479_ = lean_array_get_size(v_binderGroups_4434_);
v_binderGroups_4480_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_binderGroups_4434_, v___x_4465_, v___x_4479_);
v___x_4481_ = lean_array_get_size(v___y_4478_);
v___x_4482_ = lean_unsigned_to_nat(1u);
v___x_4483_ = lean_nat_dec_le(v___x_4481_, v___x_4482_);
if (v___x_4483_ == 0)
{
v___y_4467_ = v___y_4478_;
v___y_4468_ = v_binderGroups_4480_;
goto v___jp_4466_;
}
else
{
uint8_t v___x_4484_; 
v___x_4484_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_type_4436_);
if (v___x_4484_ == 0)
{
v___y_4467_ = v___y_4478_;
v___y_4468_ = v_binderGroups_4480_;
goto v___jp_4466_;
}
else
{
uint8_t v___x_4485_; 
v___x_4485_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_typeAscriptionTk_4435_);
if (v___x_4485_ == 0)
{
v___y_4467_ = v___y_4478_;
v___y_4468_ = v_binderGroups_4480_;
goto v___jp_4466_;
}
else
{
lean_object* v___x_4486_; uint8_t v___x_4487_; 
v___x_4486_ = lean_array_get_size(v_binderGroups_4480_);
v___x_4487_ = lean_nat_dec_eq(v___x_4486_, v___x_4465_);
if (v___x_4487_ == 0)
{
v___y_4467_ = v___y_4478_;
v___y_4468_ = v_binderGroups_4480_;
goto v___jp_4466_;
}
else
{
v___y_4457_ = v___x_4485_;
v___y_4458_ = v_binderGroups_4480_;
v___y_4459_ = v___y_4478_;
goto v___jp_4456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object* v_lvals_4494_, lean_object* v_binderGroups_4495_, lean_object* v_typeAscriptionTk_4496_, lean_object* v_type_4497_, lean_object* v_kind_4498_, lean_object* v_lvalsLayout_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4494_, v_binderGroups_4495_, v_typeAscriptionTk_4496_, v_type_4497_, v_kind_4498_, v_lvalsLayout_4499_);
lean_dec(v_kind_4498_);
lean_dec_ref(v_binderGroups_4495_);
lean_dec_ref(v_lvals_4494_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(uint8_t v___x_4501_, lean_object* v_terms_4502_){
_start:
{
lean_object* v___x_4503_; 
v___x_4503_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4502_, v___x_4501_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object* v___x_4504_, lean_object* v_terms_4505_){
_start:
{
uint8_t v___x_9__boxed_4506_; lean_object* v_res_4507_; 
v___x_9__boxed_4506_ = lean_unbox(v___x_4504_);
v_res_4507_ = l_Lean_Fmt_Layouts_localSignature___lam__0(v___x_9__boxed_4506_, v_terms_4505_);
lean_dec_ref(v_terms_4505_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object* v_lvals_4513_, lean_object* v_binderGroups_4514_, lean_object* v_typeAscriptionTk_4515_, lean_object* v_type_4516_){
_start:
{
lean_object* v___f_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___f_4517_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__0));
v___x_4518_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__1));
v___x_4519_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4513_, v_binderGroups_4514_, v_typeAscriptionTk_4515_, v_type_4516_, v___x_4518_, v___f_4517_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object* v_lvals_4520_, lean_object* v_binderGroups_4521_, lean_object* v_typeAscriptionTk_4522_, lean_object* v_type_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_Fmt_Layouts_localSignature(v_lvals_4520_, v_binderGroups_4521_, v_typeAscriptionTk_4522_, v_type_4523_);
lean_dec_ref(v_binderGroups_4521_);
lean_dec_ref(v_lvals_4520_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0(lean_object* v_terms_4525_){
_start:
{
uint8_t v___x_4526_; lean_object* v___x_4527_; 
v___x_4526_ = 1;
v___x_4527_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4525_, v___x_4526_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0___boxed(lean_object* v_terms_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Lean_Fmt_Layouts_globalSignature___lam__0(v_terms_4528_);
lean_dec_ref(v_terms_4528_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object* v_lvals_4531_, lean_object* v_binderGroups_4532_, lean_object* v_typeAscriptionTk_4533_, lean_object* v_type_4534_){
_start:
{
lean_object* v___f_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___f_4535_ = ((lean_object*)(l_Lean_Fmt_Layouts_globalSignature___closed__0));
v___x_4536_ = lean_box(1);
v___x_4537_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4531_, v_binderGroups_4532_, v_typeAscriptionTk_4533_, v_type_4534_, v___x_4536_, v___f_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object* v_lvals_4538_, lean_object* v_binderGroups_4539_, lean_object* v_typeAscriptionTk_4540_, lean_object* v_type_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_Fmt_Layouts_globalSignature(v_lvals_4538_, v_binderGroups_4539_, v_typeAscriptionTk_4540_, v_type_4541_);
lean_dec_ref(v_binderGroups_4539_);
lean_dec_ref(v_lvals_4538_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object* v_signature_4543_, lean_object* v_separationTk_4544_, lean_object* v_body_4545_, uint8_t v_sticky_4546_){
_start:
{
uint8_t v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; uint8_t v___y_4552_; uint8_t v___y_4556_; lean_object* v___y_4557_; uint8_t v___x_4596_; 
v___x_4596_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_separationTk_4544_);
if (v___x_4596_ == 0)
{
goto v___jp_4580_;
}
else
{
uint8_t v___x_4597_; 
v___x_4597_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4545_);
if (v___x_4597_ == 0)
{
goto v___jp_4580_;
}
else
{
lean_inc_ref(v_signature_4543_);
v___y_4556_ = v___x_4596_;
v___y_4557_ = v_signature_4543_;
goto v___jp_4555_;
}
}
v___jp_4547_:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; 
lean_inc_ref(v___y_4549_);
v___x_4553_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___y_4550_, v___y_4549_, v_body_4545_, v___y_4552_);
v___x_4554_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_4551_, v___x_4553_, v___y_4548_);
return v___x_4554_;
}
v___jp_4555_:
{
lean_object* v_doc_4558_; 
v_doc_4558_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___y_4557_);
if (v_sticky_4546_ == 0)
{
lean_dec_ref(v_body_4545_);
lean_dec_ref(v_separationTk_4544_);
lean_dec_ref(v_signature_4543_);
return v_doc_4558_;
}
else
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v_lhs_4570_; lean_object* v___x_4571_; 
v___x_4559_ = l_Lean_Fmt_TaggedDoc_flattened(v_signature_4543_);
v___x_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
v___x_4561_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1);
v___x_4562_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4560_, v___x_4561_);
v___x_4563_ = lean_box(0);
v___x_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4564_, 0, v_separationTk_4544_);
v___x_4565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4563_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
lean_ctor_set(v___x_4565_, 2, v___x_4563_);
v___x_4566_ = lean_unsigned_to_nat(2u);
v___x_4567_ = lean_mk_empty_array_with_capacity(v___x_4566_);
v___x_4568_ = lean_array_push(v___x_4567_, v___x_4562_);
v___x_4569_ = lean_array_push(v___x_4568_, v___x_4565_);
v_lhs_4570_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4569_);
lean_dec_ref(v___x_4569_);
lean_inc_ref(v_body_4545_);
v___x_4571_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_body_4545_);
if (lean_obj_tag(v___x_4571_) == 1)
{
lean_object* v_val_4572_; uint8_t v_kind_4573_; lean_object* v___x_4574_; 
v_val_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_val_4572_);
lean_dec_ref_known(v___x_4571_, 1);
v_kind_4573_ = lean_ctor_get_uint8(v_val_4572_, sizeof(void*)*1);
lean_dec(v_val_4572_);
v___x_4574_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
if (v_kind_4573_ == 1)
{
uint8_t v___x_4575_; 
v___x_4575_ = 0;
v___y_4548_ = v_kind_4573_;
v___y_4549_ = v___x_4574_;
v___y_4550_ = v_lhs_4570_;
v___y_4551_ = v_doc_4558_;
v___y_4552_ = v___x_4575_;
goto v___jp_4547_;
}
else
{
v___y_4548_ = v_kind_4573_;
v___y_4549_ = v___x_4574_;
v___y_4550_ = v_lhs_4570_;
v___y_4551_ = v_doc_4558_;
v___y_4552_ = v_sticky_4546_;
goto v___jp_4547_;
}
}
else
{
lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; lean_object* v___x_4579_; 
lean_dec(v___x_4571_);
v___x_4576_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4577_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4570_, v___x_4576_, v_body_4545_, v___y_4556_);
v___x_4578_ = 0;
v___x_4579_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4558_, v___x_4577_, v___x_4578_);
return v___x_4579_;
}
}
}
v___jp_4580_:
{
uint8_t v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v_lhs_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4581_ = 1;
lean_inc_ref(v_signature_4543_);
v___x_4582_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4543_);
v___x_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
v___x_4584_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1);
v___x_4585_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4583_, v___x_4584_);
v___x_4586_ = lean_box(0);
lean_inc_ref(v_separationTk_4544_);
v___x_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4587_, 0, v_separationTk_4544_);
v___x_4588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4586_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
lean_ctor_set(v___x_4588_, 2, v___x_4586_);
v___x_4589_ = lean_unsigned_to_nat(2u);
v___x_4590_ = lean_mk_empty_array_with_capacity(v___x_4589_);
v___x_4591_ = lean_array_push(v___x_4590_, v___x_4585_);
v___x_4592_ = lean_array_push(v___x_4591_, v___x_4588_);
v_lhs_4593_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4592_);
lean_dec_ref(v___x_4592_);
v___x_4594_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_body_4545_);
v___x_4595_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4593_, v___x_4594_, v_body_4545_, v___x_4581_);
v___y_4556_ = v___x_4581_;
v___y_4557_ = v___x_4595_;
goto v___jp_4555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object* v_signature_4598_, lean_object* v_separationTk_4599_, lean_object* v_body_4600_, lean_object* v_sticky_4601_){
_start:
{
uint8_t v_sticky_boxed_4602_; lean_object* v_res_4603_; 
v_sticky_boxed_4602_ = lean_unbox(v_sticky_4601_);
v_res_4603_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_signature_4598_, v_separationTk_4599_, v_body_4600_, v_sticky_boxed_4602_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object* v_signature_4604_, lean_object* v_matchAlts_4605_){
_start:
{
uint8_t v___x_4606_; 
v___x_4606_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_matchAlts_4605_);
if (v___x_4606_ == 0)
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4607_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4604_);
v___x_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
v___x_4609_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4610_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4608_, v___x_4609_);
v___x_4611_ = lean_box(0);
v___x_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4612_, 0, v_matchAlts_4605_);
v___x_4613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4611_);
lean_ctor_set(v___x_4613_, 1, v___x_4612_);
lean_ctor_set(v___x_4613_, 2, v___x_4611_);
v___x_4614_ = lean_unsigned_to_nat(2u);
v___x_4615_ = lean_mk_empty_array_with_capacity(v___x_4614_);
v___x_4616_ = lean_array_push(v___x_4615_, v___x_4610_);
v___x_4617_ = lean_array_push(v___x_4616_, v___x_4613_);
v___x_4618_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4617_);
lean_dec_ref(v___x_4617_);
return v___x_4618_;
}
else
{
lean_dec_ref(v_matchAlts_4605_);
return v_signature_4604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object* v_signature_4622_, lean_object* v_whereTk_4623_, lean_object* v_body_4624_){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4625_ = ((lean_object*)(l_Lean_Fmt_Layouts_whereDeclaration___closed__0));
v___x_4626_ = l_Lean_Fmt_Layouts_keywordSeparated(v_signature_4622_, v_whereTk_4623_, v_body_4624_, v___x_4625_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object* v_lbs_4628_, lean_object* v_lhses_4629_, lean_object* v_subBinderGroups_4630_, lean_object* v_typeAscriptionTk_x3f_4631_, lean_object* v_type_x3f_4632_, lean_object* v_colonEqTk_x3f_4633_, lean_object* v_default_x3f_4634_, lean_object* v_rbs_4635_, lean_object* v_kind_4636_){
_start:
{
lean_object* v_lbs_4637_; lean_object* v___x_4638_; lean_object* v_binderSignature_4639_; uint8_t v___x_4640_; lean_object* v_simpleBinder_4641_; lean_object* v_rbs_4642_; lean_object* v___x_4643_; 
v_lbs_4637_ = l_Lean_Fmt_Layouts_atomic(v_lbs_4628_);
v___x_4638_ = ((lean_object*)(l_Lean_Fmt_Layouts_binder___closed__0));
v_binderSignature_4639_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lhses_4629_, v_subBinderGroups_4630_, v_typeAscriptionTk_x3f_4631_, v_type_x3f_4632_, v_kind_4636_, v___x_4638_);
v___x_4640_ = 0;
v_simpleBinder_4641_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_binderSignature_4639_, v_colonEqTk_x3f_4633_, v_default_x3f_4634_, v___x_4640_);
v_rbs_4642_ = l_Lean_Fmt_Layouts_atomic(v_rbs_4635_);
v___x_4643_ = l_Lean_Fmt_Layouts_parens(v_lbs_4637_, v_simpleBinder_4641_, v_rbs_4642_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder___boxed(lean_object* v_lbs_4644_, lean_object* v_lhses_4645_, lean_object* v_subBinderGroups_4646_, lean_object* v_typeAscriptionTk_x3f_4647_, lean_object* v_type_x3f_4648_, lean_object* v_colonEqTk_x3f_4649_, lean_object* v_default_x3f_4650_, lean_object* v_rbs_4651_, lean_object* v_kind_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Lean_Fmt_Layouts_binder(v_lbs_4644_, v_lhses_4645_, v_subBinderGroups_4646_, v_typeAscriptionTk_x3f_4647_, v_type_x3f_4648_, v_colonEqTk_x3f_4649_, v_default_x3f_4650_, v_rbs_4651_, v_kind_4652_);
lean_dec(v_kind_4652_);
lean_dec_ref(v_rbs_4651_);
lean_dec_ref(v_subBinderGroups_4646_);
lean_dec_ref(v_lhses_4645_);
lean_dec_ref(v_lbs_4644_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object* v_keywordTk_4657_, lean_object* v_config_4658_, lean_object* v_decl_4659_, uint8_t v_format_4660_){
_start:
{
lean_object* v___f_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v_signature_4667_; lean_object* v___y_4669_; 
v___f_4661_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0));
v___x_4662_ = lean_unsigned_to_nat(2u);
v___x_4663_ = lean_mk_empty_array_with_capacity(v___x_4662_);
lean_inc_ref(v___x_4663_);
v___x_4664_ = lean_array_push(v___x_4663_, v_keywordTk_4657_);
v___x_4665_ = lean_array_push(v___x_4664_, v_config_4658_);
v___x_4666_ = ((lean_object*)(l_Lean_Fmt_Layouts_letDecl___closed__0));
v_signature_4667_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4665_, v___x_4666_);
if (v_format_4660_ == 0)
{
lean_object* v___x_4681_; 
v___x_4681_ = l_Lean_Fmt_TaggedDoc_space;
v___y_4669_ = v___x_4681_;
goto v___jp_4668_;
}
else
{
lean_object* v___x_4682_; 
v___x_4682_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4669_ = v___x_4682_;
goto v___jp_4668_;
}
v___jp_4668_:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4670_, 0, v_signature_4667_);
lean_inc_ref(v___y_4669_);
v___x_4671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4671_, 0, v___y_4669_);
lean_ctor_set(v___x_4671_, 1, v___f_4661_);
v___x_4672_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4670_, v___x_4671_);
v___x_4673_ = lean_box(0);
v___x_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4674_, 0, v_decl_4659_);
v___x_4675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4673_);
lean_ctor_set(v___x_4675_, 1, v___x_4674_);
lean_ctor_set(v___x_4675_, 2, v___x_4673_);
v___x_4676_ = lean_array_push(v___x_4663_, v___x_4672_);
v___x_4677_ = lean_array_push(v___x_4676_, v___x_4675_);
v___x_4678_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4677_);
lean_dec_ref(v___x_4677_);
v___x_4679_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4678_);
v___x_4680_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4679_);
return v___x_4680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl___boxed(lean_object* v_keywordTk_4683_, lean_object* v_config_4684_, lean_object* v_decl_4685_, lean_object* v_format_4686_){
_start:
{
uint8_t v_format_boxed_4687_; lean_object* v_res_4688_; 
v_format_boxed_4687_ = lean_unbox(v_format_4686_);
v_res_4688_ = l_Lean_Fmt_Layouts_letDecl(v_keywordTk_4683_, v_config_4684_, v_decl_4685_, v_format_boxed_4687_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(size_t v_sz_4689_, size_t v_i_4690_, lean_object* v_bs_4691_){
_start:
{
uint8_t v___x_4692_; 
v___x_4692_ = lean_usize_dec_lt(v_i_4690_, v_sz_4689_);
if (v___x_4692_ == 0)
{
return v_bs_4691_;
}
else
{
lean_object* v_v_4693_; lean_object* v_quantifier_4694_; lean_object* v_binderGroups_4695_; lean_object* v_typeAscriptionTk_x3f_4696_; lean_object* v_type_x3f_4697_; lean_object* v_separationTk_4698_; lean_object* v___x_4699_; lean_object* v_bs_x27_4700_; lean_object* v___x_4701_; lean_object* v_signature_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; lean_object* v___x_4709_; size_t v___x_4710_; size_t v___x_4711_; lean_object* v___x_4712_; 
v_v_4693_ = lean_array_uget_borrowed(v_bs_4691_, v_i_4690_);
v_quantifier_4694_ = lean_ctor_get(v_v_4693_, 0);
lean_inc_ref(v_quantifier_4694_);
v_binderGroups_4695_ = lean_ctor_get(v_v_4693_, 1);
lean_inc_ref(v_binderGroups_4695_);
v_typeAscriptionTk_x3f_4696_ = lean_ctor_get(v_v_4693_, 2);
lean_inc_ref(v_typeAscriptionTk_x3f_4696_);
v_type_x3f_4697_ = lean_ctor_get(v_v_4693_, 3);
lean_inc_ref(v_type_x3f_4697_);
v_separationTk_4698_ = lean_ctor_get(v_v_4693_, 4);
lean_inc_ref(v_separationTk_4698_);
v___x_4699_ = lean_unsigned_to_nat(0u);
v_bs_x27_4700_ = lean_array_uset(v_bs_4691_, v_i_4690_, v___x_4699_);
v___x_4701_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v_signature_4702_ = l_Lean_Fmt_Layouts_localSignature(v___x_4701_, v_binderGroups_4695_, v_typeAscriptionTk_x3f_4696_, v_type_x3f_4697_);
lean_dec_ref(v_binderGroups_4695_);
v___x_4703_ = lean_unsigned_to_nat(2u);
v___x_4704_ = lean_mk_empty_array_with_capacity(v___x_4703_);
v___x_4705_ = lean_array_push(v___x_4704_, v_signature_4702_);
v___x_4706_ = lean_array_push(v___x_4705_, v_separationTk_4698_);
v___x_4707_ = l_Lean_Fmt_Layouts_atomic(v___x_4706_);
lean_dec_ref(v___x_4706_);
v___x_4708_ = 2;
v___x_4709_ = l_Lean_Fmt_Layouts_prefixOperator(v_quantifier_4694_, v___x_4707_, v___x_4708_);
v___x_4710_ = ((size_t)1ULL);
v___x_4711_ = lean_usize_add(v_i_4690_, v___x_4710_);
v___x_4712_ = lean_array_uset(v_bs_x27_4700_, v_i_4690_, v___x_4709_);
v_i_4690_ = v___x_4711_;
v_bs_4691_ = v___x_4712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0___boxed(lean_object* v_sz_4714_, lean_object* v_i_4715_, lean_object* v_bs_4716_){
_start:
{
size_t v_sz_boxed_4717_; size_t v_i_boxed_4718_; lean_object* v_res_4719_; 
v_sz_boxed_4717_ = lean_unbox_usize(v_sz_4714_);
lean_dec(v_sz_4714_);
v_i_boxed_4718_ = lean_unbox_usize(v_i_4715_);
lean_dec(v_i_4715_);
v_res_4719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_boxed_4717_, v_i_boxed_4718_, v_bs_4716_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(size_t v_sz_4720_, size_t v_i_4721_, lean_object* v_bs_4722_){
_start:
{
uint8_t v___x_4723_; 
v___x_4723_ = lean_usize_dec_lt(v_i_4721_, v_sz_4720_);
if (v___x_4723_ == 0)
{
return v_bs_4722_;
}
else
{
lean_object* v_v_4724_; lean_object* v___x_4725_; lean_object* v_bs_x27_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; size_t v___x_4729_; size_t v___x_4730_; lean_object* v___x_4731_; 
v_v_4724_ = lean_array_uget(v_bs_4722_, v_i_4721_);
v___x_4725_ = lean_unsigned_to_nat(0u);
v_bs_x27_4726_ = lean_array_uset(v_bs_4722_, v_i_4721_, v___x_4725_);
v___x_4727_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4724_);
v___x_4728_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
lean_ctor_set_uint8(v___x_4728_, sizeof(void*)*1, v___x_4723_);
v___x_4729_ = ((size_t)1ULL);
v___x_4730_ = lean_usize_add(v_i_4721_, v___x_4729_);
v___x_4731_ = lean_array_uset(v_bs_x27_4726_, v_i_4721_, v___x_4728_);
v_i_4721_ = v___x_4730_;
v_bs_4722_ = v___x_4731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1___boxed(lean_object* v_sz_4733_, lean_object* v_i_4734_, lean_object* v_bs_4735_){
_start:
{
size_t v_sz_boxed_4736_; size_t v_i_boxed_4737_; lean_object* v_res_4738_; 
v_sz_boxed_4736_ = lean_unbox_usize(v_sz_4733_);
lean_dec(v_sz_4733_);
v_i_boxed_4737_ = lean_unbox_usize(v_i_4734_);
lean_dec(v_i_4734_);
v_res_4738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_boxed_4736_, v_i_boxed_4737_, v_bs_4735_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_quantified(lean_object* v_quantifierHeads_4739_, lean_object* v_body_4740_){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; 
v___x_4741_ = lean_array_get_size(v_quantifierHeads_4739_);
v___x_4742_ = lean_unsigned_to_nat(0u);
v___x_4743_ = lean_nat_dec_eq(v___x_4741_, v___x_4742_);
if (v___x_4743_ == 0)
{
size_t v_sz_4744_; size_t v___x_4745_; lean_object* v_quantifierHeads_4746_; size_t v_sz_4747_; lean_object* v_quantifierHeads_4748_; lean_object* v___x_4749_; lean_object* v_components_4750_; lean_object* v___x_4751_; lean_object* v_quantifiers_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v_sz_4744_ = lean_array_size(v_quantifierHeads_4739_);
v___x_4745_ = ((size_t)0ULL);
v_quantifierHeads_4746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_4744_, v___x_4745_, v_quantifierHeads_4739_);
v_sz_4747_ = lean_array_size(v_quantifierHeads_4746_);
v_quantifierHeads_4748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_4747_, v___x_4745_, v_quantifierHeads_4746_);
v___x_4749_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4749_, 0, v_body_4740_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*1, v___x_4743_);
v_components_4750_ = lean_array_push(v_quantifierHeads_4748_, v___x_4749_);
v___x_4751_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_quantifiers_4752_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(v_components_4750_, v___x_4751_);
v___x_4753_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_quantifiers_4752_);
v___x_4754_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4753_, v___x_4743_);
return v___x_4754_;
}
else
{
lean_dec_ref(v_quantifierHeads_4739_);
return v_body_4740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_subtype(lean_object* v_lbTk_4758_, lean_object* v_lhs_4759_, lean_object* v_sepTk_4760_, lean_object* v_rhs_4761_, lean_object* v_rbTk_4762_, lean_object* v_format_4763_){
_start:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; uint8_t v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v_body_4772_; lean_object* v___x_4773_; 
v___x_4764_ = lean_unsigned_to_nat(3u);
v___x_4765_ = lean_mk_empty_array_with_capacity(v___x_4764_);
v___x_4766_ = lean_array_push(v___x_4765_, v_lhs_4759_);
v___x_4767_ = lean_array_push(v___x_4766_, v_sepTk_4760_);
v___x_4768_ = lean_array_push(v___x_4767_, v_rhs_4761_);
v___x_4769_ = 0;
v___x_4770_ = ((lean_object*)(l_Lean_Fmt_Layouts_subtype___closed__0));
v___x_4771_ = l_Lean_Fmt_Layouts_infixOperator(v___x_4768_, v___x_4770_);
v_body_4772_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4771_, v___x_4769_);
v___x_4773_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_4758_, v_body_4772_, v_rbTk_4762_, v_format_4763_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(lean_object* v_tk_4774_, lean_object* v_block_4775_, uint8_t v_allowFlattening_4776_){
_start:
{
lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4777_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4778_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_tk_4774_, v___x_4777_, v_block_4775_, v_allowFlattening_4776_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken___boxed(lean_object* v_tk_4779_, lean_object* v_block_4780_, lean_object* v_allowFlattening_4781_){
_start:
{
uint8_t v_allowFlattening_boxed_4782_; lean_object* v_res_4783_; 
v_allowFlattening_boxed_4782_ = lean_unbox(v_allowFlattening_4781_);
v_res_4783_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_tk_4779_, v_block_4780_, v_allowFlattening_boxed_4782_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(uint8_t v_allowFlattening_4784_, size_t v_sz_4785_, size_t v_i_4786_, lean_object* v_bs_4787_){
_start:
{
uint8_t v___x_4788_; 
v___x_4788_ = lean_usize_dec_lt(v_i_4786_, v_sz_4785_);
if (v___x_4788_ == 0)
{
return v_bs_4787_;
}
else
{
lean_object* v_v_4789_; lean_object* v_elseTk_4790_; lean_object* v_ifTk_4791_; lean_object* v_cond_4792_; lean_object* v_thenTk_4793_; lean_object* v_thenBlock_4794_; lean_object* v___x_4795_; lean_object* v_bs_x27_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v_tk_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; uint8_t v___x_4804_; lean_object* v___x_4805_; lean_object* v_head_4806_; lean_object* v_then_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v_trailingThen_4817_; size_t v___x_4818_; size_t v___x_4819_; lean_object* v___x_4820_; 
v_v_4789_ = lean_array_uget_borrowed(v_bs_4787_, v_i_4786_);
v_elseTk_4790_ = lean_ctor_get(v_v_4789_, 0);
lean_inc_ref(v_elseTk_4790_);
v_ifTk_4791_ = lean_ctor_get(v_v_4789_, 1);
lean_inc_ref(v_ifTk_4791_);
v_cond_4792_ = lean_ctor_get(v_v_4789_, 2);
lean_inc_ref(v_cond_4792_);
v_thenTk_4793_ = lean_ctor_get(v_v_4789_, 3);
lean_inc_ref(v_thenTk_4793_);
v_thenBlock_4794_ = lean_ctor_get(v_v_4789_, 4);
lean_inc_ref(v_thenBlock_4794_);
v___x_4795_ = lean_unsigned_to_nat(0u);
v_bs_x27_4796_ = lean_array_uset(v_bs_4787_, v_i_4786_, v___x_4795_);
v___x_4797_ = lean_unsigned_to_nat(2u);
v___x_4798_ = lean_mk_empty_array_with_capacity(v___x_4797_);
lean_inc_ref_n(v___x_4798_, 2);
v___x_4799_ = lean_array_push(v___x_4798_, v_elseTk_4790_);
v___x_4800_ = lean_array_push(v___x_4799_, v_ifTk_4791_);
v_tk_4801_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4800_);
lean_dec_ref(v___x_4800_);
v___x_4802_ = lean_array_push(v___x_4798_, v_tk_4801_);
v___x_4803_ = lean_array_push(v___x_4802_, v_cond_4792_);
v___x_4804_ = 0;
v___x_4805_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4805_, 0, v___x_4788_);
lean_ctor_set_uint8(v___x_4805_, 1, v___x_4804_);
lean_ctor_set_uint8(v___x_4805_, 2, v___x_4804_);
lean_ctor_set_uint8(v___x_4805_, 3, v___x_4804_);
v_head_4806_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4803_, v___x_4805_);
v_then_4807_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_thenTk_4793_, v_thenBlock_4794_, v_allowFlattening_4784_);
v___x_4808_ = l_Lean_Fmt_TaggedDoc_hardNested(v_head_4806_);
v___x_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4808_);
v___x_4810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4811_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4809_, v___x_4810_);
v___x_4812_ = lean_box(0);
v___x_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4813_, 0, v_then_4807_);
v___x_4814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4812_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
lean_ctor_set(v___x_4814_, 2, v___x_4812_);
v___x_4815_ = lean_array_push(v___x_4798_, v___x_4811_);
v___x_4816_ = lean_array_push(v___x_4815_, v___x_4814_);
v_trailingThen_4817_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4816_);
lean_dec_ref(v___x_4816_);
v___x_4818_ = ((size_t)1ULL);
v___x_4819_ = lean_usize_add(v_i_4786_, v___x_4818_);
v___x_4820_ = lean_array_uset(v_bs_x27_4796_, v_i_4786_, v_trailingThen_4817_);
v_i_4786_ = v___x_4819_;
v_bs_4787_ = v___x_4820_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0___boxed(lean_object* v_allowFlattening_4822_, lean_object* v_sz_4823_, lean_object* v_i_4824_, lean_object* v_bs_4825_){
_start:
{
uint8_t v_allowFlattening_boxed_4826_; size_t v_sz_boxed_4827_; size_t v_i_boxed_4828_; lean_object* v_res_4829_; 
v_allowFlattening_boxed_4826_ = lean_unbox(v_allowFlattening_4822_);
v_sz_boxed_4827_ = lean_unbox_usize(v_sz_4823_);
lean_dec(v_sz_4823_);
v_i_boxed_4828_ = lean_unbox_usize(v_i_4824_);
lean_dec(v_i_4824_);
v_res_4829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_boxed_4826_, v_sz_boxed_4827_, v_i_boxed_4828_, v_bs_4825_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(lean_object* v_elseIfs_4830_, lean_object* v_elseTk_4831_, lean_object* v_elseBlock_4832_, uint8_t v_allowFlattening_4833_){
_start:
{
size_t v_sz_4834_; size_t v___x_4835_; lean_object* v_elseIfs_4836_; lean_object* v_else_4837_; lean_object* v_blocks_4838_; size_t v_sz_4839_; lean_object* v_blocks_4840_; lean_object* v_conditional_4841_; lean_object* v___x_4842_; 
v_sz_4834_ = lean_array_size(v_elseIfs_4830_);
v___x_4835_ = ((size_t)0ULL);
v_elseIfs_4836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_4833_, v_sz_4834_, v___x_4835_, v_elseIfs_4830_);
v_else_4837_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_elseTk_4831_, v_elseBlock_4832_, v_allowFlattening_4833_);
v_blocks_4838_ = lean_array_push(v_elseIfs_4836_, v_else_4837_);
v_sz_4839_ = lean_array_size(v_blocks_4838_);
v_blocks_4840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_4839_, v___x_4835_, v_blocks_4838_);
v_conditional_4841_ = l_Lean_Fmt_TaggedDoc_combine(v_blocks_4840_);
lean_dec_ref(v_blocks_4840_);
v___x_4842_ = l_Lean_Fmt_TaggedDoc_aligned(v_conditional_4841_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk___boxed(lean_object* v_elseIfs_4843_, lean_object* v_elseTk_4844_, lean_object* v_elseBlock_4845_, lean_object* v_allowFlattening_4846_){
_start:
{
uint8_t v_allowFlattening_boxed_4847_; lean_object* v_res_4848_; 
v_allowFlattening_boxed_4847_ = lean_unbox(v_allowFlattening_4846_);
v_res_4848_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4843_, v_elseTk_4844_, v_elseBlock_4845_, v_allowFlattening_boxed_4847_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(lean_object* v_as_4849_, size_t v_i_4850_, size_t v_stop_4851_, lean_object* v_b_4852_){
_start:
{
lean_object* v___y_4854_; uint8_t v___x_4858_; 
v___x_4858_ = lean_usize_dec_eq(v_i_4850_, v_stop_4851_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; lean_object* v_elseTk_4860_; lean_object* v_ifTk_4861_; lean_object* v_cond_4862_; lean_object* v_thenTk_4863_; lean_object* v_thenBlock_4864_; uint8_t v___x_4865_; 
v___x_4859_ = lean_array_uget_borrowed(v_as_4849_, v_i_4850_);
v_elseTk_4860_ = lean_ctor_get(v___x_4859_, 0);
v_ifTk_4861_ = lean_ctor_get(v___x_4859_, 1);
v_cond_4862_ = lean_ctor_get(v___x_4859_, 2);
v_thenTk_4863_ = lean_ctor_get(v___x_4859_, 3);
v_thenBlock_4864_ = lean_ctor_get(v___x_4859_, 4);
v___x_4865_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_elseTk_4860_);
if (v___x_4865_ == 0)
{
lean_object* v___x_4866_; 
lean_inc(v___x_4859_);
v___x_4866_ = lean_array_push(v_b_4852_, v___x_4859_);
v___y_4854_ = v___x_4866_;
goto v___jp_4853_;
}
else
{
uint8_t v___x_4867_; 
v___x_4867_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_ifTk_4861_);
if (v___x_4867_ == 0)
{
lean_object* v___x_4868_; 
lean_inc(v___x_4859_);
v___x_4868_ = lean_array_push(v_b_4852_, v___x_4859_);
v___y_4854_ = v___x_4868_;
goto v___jp_4853_;
}
else
{
uint8_t v___x_4869_; 
v___x_4869_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_cond_4862_);
if (v___x_4869_ == 0)
{
lean_object* v___x_4870_; 
lean_inc(v___x_4859_);
v___x_4870_ = lean_array_push(v_b_4852_, v___x_4859_);
v___y_4854_ = v___x_4870_;
goto v___jp_4853_;
}
else
{
uint8_t v___x_4871_; 
v___x_4871_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenTk_4863_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; 
lean_inc(v___x_4859_);
v___x_4872_ = lean_array_push(v_b_4852_, v___x_4859_);
v___y_4854_ = v___x_4872_;
goto v___jp_4853_;
}
else
{
uint8_t v___x_4873_; 
v___x_4873_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenBlock_4864_);
if (v___x_4873_ == 0)
{
lean_object* v___x_4874_; 
lean_inc(v___x_4859_);
v___x_4874_ = lean_array_push(v_b_4852_, v___x_4859_);
v___y_4854_ = v___x_4874_;
goto v___jp_4853_;
}
else
{
v___y_4854_ = v_b_4852_;
goto v___jp_4853_;
}
}
}
}
}
}
else
{
return v_b_4852_;
}
v___jp_4853_:
{
size_t v___x_4855_; size_t v___x_4856_; 
v___x_4855_ = ((size_t)1ULL);
v___x_4856_ = lean_usize_add(v_i_4850_, v___x_4855_);
v_i_4850_ = v___x_4856_;
v_b_4852_ = v___y_4854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0___boxed(lean_object* v_as_4875_, lean_object* v_i_4876_, lean_object* v_stop_4877_, lean_object* v_b_4878_){
_start:
{
size_t v_i_boxed_4879_; size_t v_stop_boxed_4880_; lean_object* v_res_4881_; 
v_i_boxed_4879_ = lean_unbox_usize(v_i_4876_);
lean_dec(v_i_4876_);
v_stop_boxed_4880_ = lean_unbox_usize(v_stop_4877_);
lean_dec(v_stop_4877_);
v_res_4881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_as_4875_, v_i_boxed_4879_, v_stop_boxed_4880_, v_b_4878_);
lean_dec_ref(v_as_4875_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional(lean_object* v_ifTk_4884_, lean_object* v_cond_4885_, lean_object* v_thenTk_4886_, lean_object* v_thenBlock_4887_, lean_object* v_elseIfs_4888_, lean_object* v_elseTk_4889_, lean_object* v_elseBlock_4890_, uint8_t v_allowFlattening_4891_){
_start:
{
lean_object* v___y_4893_; uint8_t v___y_4894_; lean_object* v___y_4913_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; uint8_t v___x_4920_; 
v___x_4917_ = lean_unsigned_to_nat(0u);
v___x_4918_ = lean_array_get_size(v_elseIfs_4888_);
v___x_4919_ = ((lean_object*)(l_Lean_Fmt_Layouts_conditional___closed__0));
v___x_4920_ = lean_nat_dec_lt(v___x_4917_, v___x_4918_);
if (v___x_4920_ == 0)
{
v___y_4913_ = v___x_4919_;
goto v___jp_4912_;
}
else
{
size_t v___x_4921_; size_t v___x_4922_; lean_object* v___x_4923_; 
v___x_4921_ = ((size_t)0ULL);
v___x_4922_ = lean_usize_of_nat(v___x_4918_);
v___x_4923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_4888_, v___x_4921_, v___x_4922_, v___x_4919_);
v___y_4913_ = v___x_4923_;
goto v___jp_4912_;
}
v___jp_4892_:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v_elseIfs_4900_; 
v___x_4895_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_4896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4895_);
lean_ctor_set(v___x_4896_, 1, v_ifTk_4884_);
lean_ctor_set(v___x_4896_, 2, v_cond_4885_);
lean_ctor_set(v___x_4896_, 3, v_thenTk_4886_);
lean_ctor_set(v___x_4896_, 4, v_thenBlock_4887_);
v___x_4897_ = lean_unsigned_to_nat(1u);
v___x_4898_ = lean_mk_empty_array_with_capacity(v___x_4897_);
v___x_4899_ = lean_array_push(v___x_4898_, v___x_4896_);
v_elseIfs_4900_ = l_Array_append___redArg(v___x_4899_, v___y_4893_);
lean_dec_ref(v___y_4893_);
if (v___y_4894_ == 0)
{
lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4901_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4900_, v_elseTk_4889_, v_elseBlock_4890_, v___y_4894_);
v___x_4902_ = l_Lean_Fmt_TaggedDoc_unflattenable(v___x_4901_);
return v___x_4902_;
}
else
{
lean_object* v___x_4903_; lean_object* v___x_4904_; uint8_t v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
lean_inc_ref(v_elseBlock_4890_);
lean_inc_ref(v_elseTk_4889_);
lean_inc_ref(v_elseIfs_4900_);
v___x_4903_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4900_, v_elseTk_4889_, v_elseBlock_4890_, v___y_4894_);
v___x_4904_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_4903_);
v___x_4905_ = 0;
v___x_4906_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4900_, v_elseTk_4889_, v_elseBlock_4890_, v___x_4905_);
v___x_4907_ = lean_unsigned_to_nat(2u);
v___x_4908_ = lean_mk_empty_array_with_capacity(v___x_4907_);
v___x_4909_ = lean_array_push(v___x_4908_, v___x_4904_);
v___x_4910_ = lean_array_push(v___x_4909_, v___x_4906_);
v___x_4911_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_4910_);
return v___x_4911_;
}
}
v___jp_4912_:
{
if (v_allowFlattening_4891_ == 0)
{
v___y_4893_ = v___y_4913_;
v___y_4894_ = v_allowFlattening_4891_;
goto v___jp_4892_;
}
else
{
lean_object* v___x_4914_; lean_object* v___x_4915_; uint8_t v___x_4916_; 
v___x_4914_ = lean_array_get_size(v___y_4913_);
v___x_4915_ = lean_unsigned_to_nat(0u);
v___x_4916_ = lean_nat_dec_eq(v___x_4914_, v___x_4915_);
v___y_4893_ = v___y_4913_;
v___y_4894_ = v___x_4916_;
goto v___jp_4892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional___boxed(lean_object* v_ifTk_4924_, lean_object* v_cond_4925_, lean_object* v_thenTk_4926_, lean_object* v_thenBlock_4927_, lean_object* v_elseIfs_4928_, lean_object* v_elseTk_4929_, lean_object* v_elseBlock_4930_, lean_object* v_allowFlattening_4931_){
_start:
{
uint8_t v_allowFlattening_boxed_4932_; lean_object* v_res_4933_; 
v_allowFlattening_boxed_4932_ = lean_unbox(v_allowFlattening_4931_);
v_res_4933_ = l_Lean_Fmt_Layouts_conditional(v_ifTk_4924_, v_cond_4925_, v_thenTk_4926_, v_thenBlock_4927_, v_elseIfs_4928_, v_elseTk_4929_, v_elseBlock_4930_, v_allowFlattening_boxed_4932_);
lean_dec_ref(v_elseIfs_4928_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_strLit(lean_object* v_prefix_4934_, lean_object* v_str_4935_){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; uint8_t v___x_4941_; lean_object* v___x_4942_; 
v___x_4936_ = lean_unsigned_to_nat(2u);
v___x_4937_ = lean_mk_empty_array_with_capacity(v___x_4936_);
v___x_4938_ = lean_array_push(v___x_4937_, v_prefix_4934_);
v___x_4939_ = lean_array_push(v___x_4938_, v_str_4935_);
v___x_4940_ = l_Lean_Fmt_Layouts_atomic(v___x_4939_);
lean_dec_ref(v___x_4939_);
v___x_4941_ = 0;
v___x_4942_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_4940_, v___x_4941_);
return v___x_4942_;
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
