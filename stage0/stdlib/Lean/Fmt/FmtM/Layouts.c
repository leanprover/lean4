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
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object*);
lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object*);
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
lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isPseudoAligned(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
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
lean_object* l_Array_reverse___redArg(lean_object*);
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
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_unsigned_to_nat(16u);
v___x_1495_ = lean_mk_array(v___x_1494_, v___x_1493_);
return v___x_1495_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0);
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v___x_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(lean_object* v_v_1499_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_fst_1502_; 
v___x_1500_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1);
v___x_1501_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1499_, v___x_1500_);
v_fst_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_fst_1502_);
lean_dec_ref(v___x_1501_);
return v_fst_1502_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(lean_object* v_00_u03c4_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_v_1506_){
_start:
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(v_v_1506_);
v___x_1508_ = lean_unbox(v___x_1507_);
lean_dec(v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___boxed(lean_object* v_00_u03c4_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_v_1512_){
_start:
{
uint8_t v_res_1513_; lean_object* v_r_1514_; 
v_res_1513_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(v_00_u03c4_1509_, v_inst_1510_, v_inst_1511_, v_v_1512_);
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
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_unsigned_to_nat(16u);
v___x_1577_ = lean_mk_array(v___x_1576_, v___x_1575_);
return v___x_1577_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v___x_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object* v_v_1581_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_fst_1584_; uint8_t v___x_1585_; 
v___x_1582_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1);
v___x_1583_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1581_, v___x_1582_);
v_fst_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_fst_1584_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = lean_unbox(v_fst_1584_);
lean_dec(v_fst_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object* v_v_1586_){
_start:
{
uint8_t v_res_1587_; lean_object* v_r_1588_; 
v_res_1587_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_v_1586_);
v_r_1588_ = lean_box(v_res_1587_);
return v_r_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object* v_prefixOperatorTk_1589_, lean_object* v_operand_1590_, uint8_t v_format_1591_){
_start:
{
lean_object* v___y_1593_; uint8_t v___x_1613_; 
v___x_1613_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_prefixOperatorTk_1589_);
if (v___x_1613_ == 0)
{
if (v_format_1591_ == 0)
{
goto v___jp_1597_;
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
goto v___jp_1604_;
}
else
{
goto v___jp_1611_;
}
}
else
{
goto v___jp_1611_;
}
}
else
{
goto v___jp_1604_;
}
}
}
else
{
lean_dec_ref(v_prefixOperatorTk_1589_);
return v_operand_1590_;
}
v___jp_1592_:
{
lean_object* v_doc_1594_; uint8_t v___x_1595_; 
v_doc_1594_ = lean_ctor_get(v_operand_1590_, 0);
lean_inc(v_doc_1594_);
lean_dec_ref(v_operand_1590_);
v___x_1595_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1594_);
if (v___x_1595_ == 0)
{
return v___y_1593_;
}
else
{
lean_object* v_doc_1596_; 
v_doc_1596_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___y_1593_);
return v_doc_1596_;
}
}
v___jp_1597_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1598_ = lean_unsigned_to_nat(2u);
v___x_1599_ = lean_mk_empty_array_with_capacity(v___x_1598_);
v___x_1600_ = lean_array_push(v___x_1599_, v_prefixOperatorTk_1589_);
lean_inc_ref(v_operand_1590_);
v___x_1601_ = lean_array_push(v___x_1600_, v_operand_1590_);
v___x_1602_ = l_Lean_Fmt_Layouts_atomic(v___x_1601_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1602_);
v___y_1593_ = v___x_1603_;
goto v___jp_1592_;
}
v___jp_1604_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1605_ = lean_unsigned_to_nat(2u);
v___x_1606_ = lean_mk_empty_array_with_capacity(v___x_1605_);
v___x_1607_ = lean_array_push(v___x_1606_, v_prefixOperatorTk_1589_);
lean_inc_ref(v_operand_1590_);
v___x_1608_ = lean_array_push(v___x_1607_, v_operand_1590_);
v___x_1609_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1608_);
lean_dec_ref(v___x_1608_);
v___x_1610_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1609_);
v___y_1593_ = v___x_1610_;
goto v___jp_1592_;
}
v___jp_1611_:
{
uint8_t v___x_1612_; 
lean_inc_ref(v_operand_1590_);
v___x_1612_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_operand_1590_);
if (v___x_1612_ == 0)
{
goto v___jp_1597_;
}
else
{
goto v___jp_1604_;
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
if (v_respectPseudoAlignment_1800_ == 0)
{
lean_object* v_doc_1801_; uint8_t v___x_1802_; 
v_doc_1801_ = lean_ctor_get(v_doc_1799_, 0);
lean_inc(v_doc_1801_);
lean_dec_ref(v_doc_1799_);
v___x_1802_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1801_);
if (v___x_1802_ == 0)
{
uint8_t v___x_1803_; 
v___x_1803_ = 1;
return v___x_1803_;
}
else
{
return v_respectPseudoAlignment_1800_;
}
}
else
{
uint8_t v___x_1804_; 
lean_inc_ref(v_doc_1799_);
v___x_1804_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_doc_1799_);
if (v___x_1804_ == 0)
{
lean_object* v_doc_1805_; uint8_t v___x_1806_; 
v_doc_1805_ = lean_ctor_get(v_doc_1799_, 0);
lean_inc(v_doc_1805_);
lean_dec_ref(v_doc_1799_);
v___x_1806_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1805_);
if (v___x_1806_ == 0)
{
return v_respectPseudoAlignment_1800_;
}
else
{
return v___x_1804_;
}
}
else
{
uint8_t v___x_1807_; 
lean_dec_ref(v_doc_1799_);
v___x_1807_ = 0;
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_permitDenseLayout___boxed(lean_object* v_doc_1808_, lean_object* v_respectPseudoAlignment_1809_){
_start:
{
uint8_t v_respectPseudoAlignment_boxed_1810_; uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_respectPseudoAlignment_boxed_1810_ = lean_unbox(v_respectPseudoAlignment_1809_);
v_res_1811_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_doc_1808_, v_respectPseudoAlignment_boxed_1810_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object* v_format_1813_, lean_object* v_docs_1814_){
_start:
{
uint8_t v___y_1816_; uint8_t v_spacing_1819_; 
v_spacing_1819_ = lean_ctor_get_uint8(v_format_1813_, 2);
v___y_1816_ = v_spacing_1819_;
goto v___jp_1815_;
v___jp_1815_:
{
if (v___y_1816_ == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Fmt_Layouts_atomic(v_docs_1814_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Fmt_Layouts_spacedAtomic(v_docs_1814_);
return v___x_1818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object* v_format_1820_, lean_object* v_docs_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1820_, v_docs_1821_);
lean_dec_ref(v_docs_1821_);
lean_dec_ref(v_format_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object* v_msg_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_1825_ = lean_panic_fn_borrowed(v___x_1824_, v_msg_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t v_a_1826_, lean_object* v_as_1827_, size_t v_i_1828_, size_t v_stop_1829_){
_start:
{
uint8_t v___x_1830_; 
v___x_1830_ = lean_usize_dec_eq(v_i_1828_, v_stop_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; uint8_t v___x_1832_; uint8_t v___x_1833_; 
v___x_1831_ = lean_array_uget_borrowed(v_as_1827_, v_i_1828_);
v___x_1832_ = lean_unbox(v___x_1831_);
v___x_1833_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_a_1826_, v___x_1832_);
if (v___x_1833_ == 0)
{
size_t v___x_1834_; size_t v___x_1835_; 
v___x_1834_ = ((size_t)1ULL);
v___x_1835_ = lean_usize_add(v_i_1828_, v___x_1834_);
v_i_1828_ = v___x_1835_;
goto _start;
}
else
{
return v___x_1833_;
}
}
else
{
uint8_t v___x_1837_; 
v___x_1837_ = 0;
return v___x_1837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object* v_a_1838_, lean_object* v_as_1839_, lean_object* v_i_1840_, lean_object* v_stop_1841_){
_start:
{
uint8_t v_a_boxed_1842_; size_t v_i_boxed_1843_; size_t v_stop_boxed_1844_; uint8_t v_res_1845_; lean_object* v_r_1846_; 
v_a_boxed_1842_ = lean_unbox(v_a_1838_);
v_i_boxed_1843_ = lean_unbox_usize(v_i_1840_);
lean_dec(v_i_1840_);
v_stop_boxed_1844_ = lean_unbox_usize(v_stop_1841_);
lean_dec(v_stop_1841_);
v_res_1845_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_boxed_1842_, v_as_1839_, v_i_boxed_1843_, v_stop_boxed_1844_);
lean_dec_ref(v_as_1839_);
v_r_1846_ = lean_box(v_res_1845_);
return v_r_1846_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object* v_as_1847_, uint8_t v_a_1848_){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1849_ = lean_unsigned_to_nat(0u);
v___x_1850_ = lean_array_get_size(v_as_1847_);
v___x_1851_ = lean_nat_dec_lt(v___x_1849_, v___x_1850_);
if (v___x_1851_ == 0)
{
return v___x_1851_;
}
else
{
size_t v___x_1852_; size_t v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = lean_usize_of_nat(v___x_1850_);
v___x_1854_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_1848_, v_as_1847_, v___x_1852_, v___x_1853_);
return v___x_1854_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object* v_as_1855_, lean_object* v_a_1856_){
_start:
{
uint8_t v_a_boxed_1857_; uint8_t v_res_1858_; lean_object* v_r_1859_; 
v_a_boxed_1857_ = lean_unbox(v_a_1856_);
v_res_1858_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_as_1855_, v_a_boxed_1857_);
lean_dec_ref(v_as_1855_);
v_r_1859_ = lean_box(v_res_1858_);
return v_r_1859_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1863_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2));
v___x_1864_ = lean_unsigned_to_nat(14u);
v___x_1865_ = lean_unsigned_to_nat(22u);
v___x_1866_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1));
v___x_1867_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_1868_ = l_mkPanicMessageWithDecl(v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_, v___x_1863_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(lean_object* v_format_1869_, lean_object* v_doc_1870_, lean_object* v_lastOperand_1871_, uint8_t v_isTailless_1872_, lean_object* v_combinedChain_1873_, lean_object* v_eligibleKinds_1874_){
_start:
{
lean_object* v___x_1875_; uint8_t v___y_1877_; lean_object* v___y_1878_; uint8_t v___y_1899_; uint8_t v_trailingOperator_1912_; 
v___x_1875_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_1912_ = lean_ctor_get_uint8(v_format_1869_, 1);
v___y_1899_ = v_trailingOperator_1912_;
goto v___jp_1898_;
v___jp_1876_:
{
lean_object* v_stickyVariant_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_stickyVariant_1879_ = lean_ctor_get(v___y_1878_, 0);
v___x_1880_ = lean_array_get_size(v_combinedChain_1873_);
v___x_1881_ = lean_unsigned_to_nat(1u);
v___x_1882_ = lean_nat_sub(v___x_1880_, v___x_1881_);
lean_inc_ref(v_stickyVariant_1879_);
v___x_1883_ = lean_array_set(v_combinedChain_1873_, v___x_1882_, v_stickyVariant_1879_);
lean_dec(v___x_1882_);
lean_inc_ref(v___x_1883_);
v___x_1884_ = lean_array_pop(v___x_1883_);
v___x_1885_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1869_, v___x_1884_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1885_);
v___x_1887_ = lean_array_get_size(v___x_1883_);
v___x_1888_ = lean_nat_sub(v___x_1887_, v___x_1881_);
v___x_1889_ = lean_array_get(v___x_1875_, v___x_1883_, v___x_1888_);
lean_dec(v___x_1888_);
lean_dec_ref(v___x_1883_);
v___x_1890_ = lean_unsigned_to_nat(2u);
v___x_1891_ = lean_mk_empty_array_with_capacity(v___x_1890_);
v___x_1892_ = lean_array_push(v___x_1891_, v___x_1886_);
v___x_1893_ = lean_array_push(v___x_1892_, v___x_1889_);
v___x_1894_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1869_, v___x_1893_);
lean_dec_ref(v___x_1893_);
v___x_1895_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_1878_, v___y_1877_);
lean_dec_ref(v___y_1878_);
v___x_1896_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1870_, v___x_1894_, v___x_1895_);
lean_dec(v___x_1895_);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
v___jp_1898_:
{
if (v___y_1899_ == 0)
{
lean_object* v___x_1900_; 
lean_dec_ref(v_combinedChain_1873_);
lean_dec_ref(v_lastOperand_1871_);
lean_dec_ref(v_doc_1870_);
v___x_1900_ = lean_box(0);
return v___x_1900_;
}
else
{
if (v_isTailless_1872_ == 0)
{
lean_object* v___x_1901_; 
lean_inc_ref(v_lastOperand_1871_);
v___x_1901_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v_lastOperand_1871_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; 
lean_dec_ref(v_combinedChain_1873_);
lean_dec_ref(v_lastOperand_1871_);
lean_dec_ref(v_doc_1870_);
v___x_1902_ = lean_box(0);
return v___x_1902_;
}
else
{
lean_object* v_val_1903_; uint8_t v___x_1904_; uint8_t v___x_1905_; 
v_val_1903_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_val_1903_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1904_ = lean_unbox(v_val_1903_);
lean_dec(v_val_1903_);
v___x_1905_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_1874_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
lean_dec_ref(v_combinedChain_1873_);
lean_dec_ref(v_lastOperand_1871_);
lean_dec_ref(v_doc_1870_);
v___x_1906_ = lean_box(0);
return v___x_1906_;
}
else
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_lastOperand_1871_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_1909_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_1908_);
v___y_1877_ = v___x_1905_;
v___y_1878_ = v___x_1909_;
goto v___jp_1876_;
}
else
{
lean_object* v_val_1910_; 
v_val_1910_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_val_1910_);
lean_dec_ref_known(v___x_1907_, 1);
v___y_1877_ = v___x_1905_;
v___y_1878_ = v_val_1910_;
goto v___jp_1876_;
}
}
}
}
else
{
lean_object* v___x_1911_; 
lean_dec_ref(v_combinedChain_1873_);
lean_dec_ref(v_lastOperand_1871_);
lean_dec_ref(v_doc_1870_);
v___x_1911_ = lean_box(0);
return v___x_1911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___boxed(lean_object* v_format_1913_, lean_object* v_doc_1914_, lean_object* v_lastOperand_1915_, lean_object* v_isTailless_1916_, lean_object* v_combinedChain_1917_, lean_object* v_eligibleKinds_1918_){
_start:
{
uint8_t v_isTailless_boxed_1919_; lean_object* v_res_1920_; 
v_isTailless_boxed_1919_ = lean_unbox(v_isTailless_1916_);
v_res_1920_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_1913_, v_doc_1914_, v_lastOperand_1915_, v_isTailless_boxed_1919_, v_combinedChain_1917_, v_eligibleKinds_1918_);
lean_dec_ref(v_eligibleKinds_1918_);
lean_dec_ref(v_format_1913_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(lean_object* v_format_1921_, lean_object* v_doc_1922_, lean_object* v_lastOperand_1923_, uint8_t v_isTailless_1924_, lean_object* v_combinedChain_1925_){
_start:
{
if (lean_obj_tag(v_format_1921_) == 0)
{
if (v_isTailless_1924_ == 0)
{
uint8_t v_trailingOperator_1926_; lean_object* v___x_1927_; 
v_trailingOperator_1926_ = lean_ctor_get_uint8(v_format_1921_, 1);
v___x_1927_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (v_trailingOperator_1926_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1946_ = lean_array_get_size(v_combinedChain_1925_);
v___x_1947_ = lean_unsigned_to_nat(2u);
v___x_1948_ = lean_nat_dec_eq(v___x_1946_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_dec_ref(v_combinedChain_1925_);
lean_dec_ref(v_lastOperand_1923_);
lean_dec_ref(v_doc_1922_);
v___x_1949_ = lean_box(0);
return v___x_1949_;
}
else
{
goto v___jp_1928_;
}
}
else
{
goto v___jp_1928_;
}
v___jp_1928_:
{
uint8_t v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(v_format_1921_);
v___x_1930_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_lastOperand_1923_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref(v_combinedChain_1925_);
lean_dec_ref(v_doc_1922_);
v___x_1931_ = lean_box(0);
return v___x_1931_;
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_inc_ref(v_combinedChain_1925_);
v___x_1932_ = lean_array_pop(v_combinedChain_1925_);
v___x_1933_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1921_, v___x_1932_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1933_);
v___x_1935_ = lean_array_get_size(v_combinedChain_1925_);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = lean_nat_sub(v___x_1935_, v___x_1936_);
v___x_1938_ = lean_array_get(v___x_1927_, v_combinedChain_1925_, v___x_1937_);
lean_dec(v___x_1937_);
lean_dec_ref(v_combinedChain_1925_);
v___x_1939_ = lean_unsigned_to_nat(2u);
v___x_1940_ = lean_mk_empty_array_with_capacity(v___x_1939_);
v___x_1941_ = lean_array_push(v___x_1940_, v___x_1934_);
v___x_1942_ = lean_array_push(v___x_1941_, v___x_1938_);
v___x_1943_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1921_, v___x_1942_);
lean_dec_ref(v___x_1942_);
v___x_1944_ = l_Lean_Fmt_TaggedDoc_fallbackOnHeight(v_doc_1922_, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
}
}
else
{
lean_object* v___x_1950_; 
lean_dec_ref(v_combinedChain_1925_);
lean_dec_ref(v_lastOperand_1923_);
lean_dec_ref(v_doc_1922_);
v___x_1950_ = lean_box(0);
return v___x_1950_;
}
}
else
{
lean_object* v___x_1951_; 
lean_dec_ref(v_combinedChain_1925_);
lean_dec_ref(v_lastOperand_1923_);
lean_dec_ref(v_doc_1922_);
v___x_1951_ = lean_box(0);
return v___x_1951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f___boxed(lean_object* v_format_1952_, lean_object* v_doc_1953_, lean_object* v_lastOperand_1954_, lean_object* v_isTailless_1955_, lean_object* v_combinedChain_1956_){
_start:
{
uint8_t v_isTailless_boxed_1957_; lean_object* v_res_1958_; 
v_isTailless_boxed_1957_ = lean_unbox(v_isTailless_1955_);
v_res_1958_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_1952_, v_doc_1953_, v_lastOperand_1954_, v_isTailless_boxed_1957_, v_combinedChain_1956_);
lean_dec_ref(v_format_1952_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(lean_object* v_snd_1959_, lean_object* v___x_1960_, lean_object* v_____r_1961_, lean_object* v_normalized_1962_){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_nat_add(v_snd_1959_, v___x_1960_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v_normalized_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0___boxed(lean_object* v_snd_1966_, lean_object* v___x_1967_, lean_object* v_____r_1968_, lean_object* v_normalized_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1966_, v___x_1967_, v_____r_1968_, v_normalized_1969_);
lean_dec(v___x_1967_);
lean_dec(v_snd_1966_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object* v___x_1971_, lean_object* v_chain_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___y_1975_; lean_object* v_fst_1979_; lean_object* v_snd_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2007_; 
v_fst_1979_ = lean_ctor_get(v_a_1973_, 0);
v_snd_1980_ = lean_ctor_get(v_a_1973_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_a_1973_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1982_ = v_a_1973_;
v_isShared_1983_ = v_isSharedCheck_2007_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_snd_1980_);
lean_inc(v_fst_1979_);
lean_dec(v_a_1973_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2007_;
goto v_resetjp_1981_;
}
v___jp_1974_:
{
if (lean_obj_tag(v___y_1975_) == 0)
{
lean_object* v_a_1976_; 
v_a_1976_ = lean_ctor_get(v___y_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___y_1975_, 1);
return v_a_1976_;
}
else
{
lean_object* v_a_1977_; 
v_a_1977_ = lean_ctor_get(v___y_1975_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___y_1975_, 1);
v_a_1973_ = v_a_1977_;
goto _start;
}
}
v_resetjp_1981_:
{
uint8_t v___x_1984_; 
v___x_1984_ = lean_nat_dec_lt(v_snd_1980_, v___x_1971_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1986_; 
if (v_isShared_1983_ == 0)
{
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_fst_1979_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_snd_1980_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1988_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1989_ = lean_array_get_borrowed(v___x_1988_, v_chain_1972_, v_snd_1980_);
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = lean_nat_add(v_snd_1980_, v___x_1990_);
v___x_1992_ = lean_array_get_size(v_chain_1972_);
v___x_1993_ = lean_nat_dec_lt(v___x_1991_, v___x_1992_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
lean_dec(v___x_1991_);
lean_inc(v___x_1989_);
v___x_1994_ = lean_array_push(v_fst_1979_, v___x_1989_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1994_);
v___x_1996_ = v___x_1982_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_snd_1980_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
lean_del_object(v___x_1982_);
v___x_1998_ = lean_unsigned_to_nat(2u);
v___x_1999_ = lean_array_fget_borrowed(v_chain_1972_, v___x_1991_);
lean_dec(v___x_1991_);
v___x_2000_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_inc(v___x_1989_);
v___x_2001_ = lean_array_push(v_fst_1979_, v___x_1989_);
lean_inc(v___x_1999_);
v___x_2002_ = lean_array_push(v___x_2001_, v___x_1999_);
v___x_2003_ = lean_box(0);
v___x_2004_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1980_, v___x_1998_, v___x_2003_, v___x_2002_);
lean_dec(v_snd_1980_);
v___y_1975_ = v___x_2004_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = lean_box(0);
v___x_2006_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1980_, v___x_1998_, v___x_2005_, v_fst_1979_);
lean_dec(v_snd_1980_);
v___y_1975_ = v___x_2006_;
goto v___jp_1974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object* v___x_2008_, lean_object* v_chain_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2008_, v_chain_2009_, v_a_2010_);
lean_dec_ref(v_chain_2009_);
lean_dec(v___x_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(lean_object* v___x_2012_, lean_object* v_chain_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___y_2016_; lean_object* v_fst_2020_; lean_object* v_snd_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2048_; 
v_fst_2020_ = lean_ctor_get(v_a_2014_, 0);
v_snd_2021_ = lean_ctor_get(v_a_2014_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_a_2014_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2023_ = v_a_2014_;
v_isShared_2024_ = v_isSharedCheck_2048_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_snd_2021_);
lean_inc(v_fst_2020_);
lean_dec(v_a_2014_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2048_;
goto v_resetjp_2022_;
}
v___jp_2015_:
{
if (lean_obj_tag(v___y_2016_) == 0)
{
lean_object* v_a_2017_; 
v_a_2017_ = lean_ctor_get(v___y_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___y_2016_, 1);
return v_a_2017_;
}
else
{
lean_object* v_a_2018_; 
v_a_2018_ = lean_ctor_get(v___y_2016_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___y_2016_, 1);
v_a_2014_ = v_a_2018_;
goto _start;
}
}
v_resetjp_2022_:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_nat_dec_lt(v_snd_2021_, v___x_2012_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2027_; 
if (v_isShared_2024_ == 0)
{
v___x_2027_ = v___x_2023_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_fst_2020_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_snd_2021_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2029_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2030_ = lean_array_get_borrowed(v___x_2029_, v_chain_2013_, v_snd_2021_);
v___x_2031_ = lean_unsigned_to_nat(1u);
v___x_2032_ = lean_nat_add(v_snd_2021_, v___x_2031_);
v___x_2033_ = lean_array_get_size(v_chain_2013_);
v___x_2034_ = lean_nat_dec_lt(v___x_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_dec(v___x_2032_);
lean_inc(v___x_2030_);
v___x_2035_ = lean_array_push(v_fst_2020_, v___x_2030_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2035_);
v___x_2037_ = v___x_2023_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_snd_2021_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
else
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
lean_del_object(v___x_2023_);
v___x_2039_ = lean_unsigned_to_nat(2u);
v___x_2040_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2030_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2041_ = lean_array_fget_borrowed(v_chain_2013_, v___x_2032_);
lean_dec(v___x_2032_);
lean_inc(v___x_2030_);
v___x_2042_ = lean_array_push(v_fst_2020_, v___x_2030_);
lean_inc(v___x_2041_);
v___x_2043_ = lean_array_push(v___x_2042_, v___x_2041_);
v___x_2044_ = lean_box(0);
v___x_2045_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2021_, v___x_2039_, v___x_2044_, v___x_2043_);
lean_dec(v_snd_2021_);
v___y_2016_ = v___x_2045_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v___x_2032_);
v___x_2046_ = lean_box(0);
v___x_2047_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2021_, v___x_2039_, v___x_2046_, v_fst_2020_);
lean_dec(v_snd_2021_);
v___y_2016_ = v___x_2047_;
goto v___jp_2015_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___boxed(lean_object* v___x_2049_, lean_object* v_chain_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2049_, v_chain_2050_, v_a_2051_);
lean_dec_ref(v_chain_2050_);
lean_dec(v___x_2049_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(lean_object* v_format_2061_, lean_object* v_chain_2062_){
_start:
{
lean_object* v___y_2064_; lean_object* v___y_2065_; uint8_t v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; uint8_t v___y_2088_; uint8_t v___y_2089_; lean_object* v___y_2090_; lean_object* v___f_2105_; lean_object* v___x_2106_; lean_object* v_chainSizeBeforeSuffixTrim_2107_; lean_object* v_chain_2108_; lean_object* v_chainSizeBeforePrefixTrim_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___y_2115_; lean_object* v___y_2116_; uint8_t v___y_2117_; uint8_t v___y_2118_; uint8_t v___y_2119_; lean_object* v___y_2131_; lean_object* v___y_2132_; uint8_t v___y_2133_; uint8_t v___y_2134_; uint8_t v___y_2139_; uint8_t v___x_2149_; 
v___f_2105_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0));
v___x_2106_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_chainSizeBeforeSuffixTrim_2107_ = lean_array_get_size(v_chain_2062_);
v_chain_2108_ = l_Array_popWhile___redArg(v___f_2105_, v_chain_2062_);
v_chainSizeBeforePrefixTrim_2109_ = lean_array_get_size(v_chain_2108_);
v___x_2110_ = lean_nat_sub(v_chainSizeBeforeSuffixTrim_2107_, v_chainSizeBeforePrefixTrim_2109_);
v___x_2111_ = lean_unsigned_to_nat(2u);
v___x_2112_ = lean_nat_mod(v___x_2110_, v___x_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2149_ = lean_nat_dec_eq(v___x_2112_, v___x_2113_);
lean_dec(v___x_2112_);
if (v___x_2149_ == 0)
{
uint8_t v___x_2150_; 
v___x_2150_ = 1;
v___y_2139_ = v___x_2150_;
goto v___jp_2138_;
}
else
{
uint8_t v___x_2151_; 
v___x_2151_ = 0;
v___y_2139_ = v___x_2151_;
goto v___jp_2138_;
}
v___jp_2063_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v_fst_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2082_; 
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___y_2068_);
lean_ctor_set(v___x_2070_, 1, v___y_2069_);
v___x_2071_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___y_2064_, v___y_2065_, v___x_2070_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
v_fst_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v___x_2071_, 1);
lean_dec(v_unused_2083_);
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2082_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_fst_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2082_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2076_ = lean_box(v___y_2066_);
v___x_2077_ = lean_box(v___y_2067_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v___x_2077_);
lean_ctor_set(v___x_2074_, 0, v___x_2076_);
v___x_2079_ = v___x_2074_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_fst_2072_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
return v___x_2080_;
}
}
}
v___jp_2084_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v_fst_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2103_; 
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___y_2085_);
lean_ctor_set(v___x_2091_, 1, v___y_2090_);
v___x_2092_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___y_2086_, v___y_2087_, v___x_2091_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
v_fst_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v___x_2092_, 1);
lean_dec(v_unused_2104_);
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2103_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_fst_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2103_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2097_ = lean_box(v___y_2088_);
v___x_2098_ = lean_box(v___y_2089_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 1, v___x_2098_);
lean_ctor_set(v___x_2095_, 0, v___x_2097_);
v___x_2100_ = v___x_2095_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v_fst_2093_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
return v___x_2101_;
}
}
}
v___jp_2114_:
{
if (v___y_2119_ == 0)
{
if (v___y_2117_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2120_ = lean_array_get_borrowed(v___x_2106_, v___y_2116_, v___x_2113_);
v___x_2121_ = lean_unsigned_to_nat(1u);
v___x_2122_ = lean_mk_empty_array_with_capacity(v___x_2121_);
lean_inc(v___x_2120_);
v___x_2123_ = lean_array_push(v___x_2122_, v___x_2120_);
v___y_2085_ = v___x_2123_;
v___y_2086_ = v___y_2115_;
v___y_2087_ = v___y_2116_;
v___y_2088_ = v___y_2117_;
v___y_2089_ = v___y_2118_;
v___y_2090_ = v___x_2121_;
goto v___jp_2084_;
}
else
{
lean_object* v___x_2124_; 
v___x_2124_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2085_ = v___x_2124_;
v___y_2086_ = v___y_2115_;
v___y_2087_ = v___y_2116_;
v___y_2088_ = v___y_2117_;
v___y_2089_ = v___y_2118_;
v___y_2090_ = v___x_2113_;
goto v___jp_2084_;
}
}
else
{
if (v___y_2117_ == 0)
{
lean_object* v___x_2125_; 
v___x_2125_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2064_ = v___y_2115_;
v___y_2065_ = v___y_2116_;
v___y_2066_ = v___y_2117_;
v___y_2067_ = v___y_2118_;
v___y_2068_ = v___x_2125_;
v___y_2069_ = v___x_2113_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2126_ = lean_array_get_borrowed(v___x_2106_, v___y_2116_, v___x_2113_);
v___x_2127_ = lean_unsigned_to_nat(1u);
v___x_2128_ = lean_mk_empty_array_with_capacity(v___x_2127_);
lean_inc(v___x_2126_);
v___x_2129_ = lean_array_push(v___x_2128_, v___x_2126_);
v___y_2064_ = v___y_2115_;
v___y_2065_ = v___y_2116_;
v___y_2066_ = v___y_2117_;
v___y_2067_ = v___y_2118_;
v___y_2068_ = v___x_2129_;
v___y_2069_ = v___x_2127_;
goto v___jp_2063_;
}
}
}
v___jp_2130_:
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_eq(v___y_2131_, v___x_2113_);
if (v___x_2135_ == 0)
{
uint8_t v_trailingOperator_2136_; 
v_trailingOperator_2136_ = lean_ctor_get_uint8(v_format_2061_, 1);
v___y_2115_ = v___y_2131_;
v___y_2116_ = v___y_2132_;
v___y_2117_ = v___y_2134_;
v___y_2118_ = v___y_2133_;
v___y_2119_ = v_trailingOperator_2136_;
goto v___jp_2114_;
}
else
{
lean_object* v___x_2137_; 
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
v___x_2137_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2));
return v___x_2137_;
}
}
v___jp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v_chain_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2140_ = l_Array_reverse___redArg(v_chain_2108_);
v___x_2141_ = l_Array_popWhile___redArg(v___f_2105_, v___x_2140_);
v_chain_2142_ = l_Array_reverse___redArg(v___x_2141_);
v___x_2143_ = lean_array_get_size(v_chain_2142_);
v___x_2144_ = lean_nat_sub(v_chainSizeBeforePrefixTrim_2109_, v___x_2143_);
v___x_2145_ = lean_nat_mod(v___x_2144_, v___x_2111_);
lean_dec(v___x_2144_);
v___x_2146_ = lean_nat_dec_eq(v___x_2145_, v___x_2113_);
lean_dec(v___x_2145_);
if (v___x_2146_ == 0)
{
uint8_t v___x_2147_; 
v___x_2147_ = 1;
v___y_2131_ = v___x_2143_;
v___y_2132_ = v_chain_2142_;
v___y_2133_ = v___y_2139_;
v___y_2134_ = v___x_2147_;
goto v___jp_2130_;
}
else
{
uint8_t v___x_2148_; 
v___x_2148_ = 0;
v___y_2131_ = v___x_2143_;
v___y_2132_ = v_chain_2142_;
v___y_2133_ = v___y_2139_;
v___y_2134_ = v___x_2148_;
goto v___jp_2130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___boxed(lean_object* v_format_2152_, lean_object* v_chain_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2152_, v_chain_2153_);
lean_dec_ref(v_format_2152_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(lean_object* v___x_2155_, lean_object* v_chain_2156_, lean_object* v_inst_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2155_, v_chain_2156_, v_a_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___boxed(lean_object* v___x_2160_, lean_object* v_chain_2161_, lean_object* v_inst_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(v___x_2160_, v_chain_2161_, v_inst_2162_, v_a_2163_);
lean_dec_ref(v_chain_2161_);
lean_dec(v___x_2160_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object* v___x_2165_, lean_object* v_chain_2166_, lean_object* v_inst_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2165_, v_chain_2166_, v_a_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object* v___x_2170_, lean_object* v_chain_2171_, lean_object* v_inst_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(v___x_2170_, v_chain_2171_, v_inst_2172_, v_a_2173_);
lean_dec_ref(v_chain_2171_);
lean_dec(v___x_2170_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(lean_object* v_chain_2175_, lean_object* v_format_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2209_; 
v_fst_2178_ = lean_ctor_get(v_a_2177_, 0);
v_snd_2179_ = lean_ctor_get(v_a_2177_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_a_2177_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2181_ = v_a_2177_;
v_isShared_2182_ = v_isSharedCheck_2209_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_inc(v_fst_2178_);
lean_dec(v_a_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2209_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = lean_array_get_size(v_chain_2175_);
v___x_2184_ = lean_nat_dec_lt(v_snd_2179_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2186_; 
if (v_isShared_2182_ == 0)
{
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_fst_2178_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_snd_2179_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___y_2191_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2188_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2189_ = lean_array_get_borrowed(v___x_2188_, v_chain_2175_, v_snd_2179_);
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_nat_add(v_snd_2179_, v___x_2204_);
v___x_2206_ = lean_nat_dec_lt(v___x_2205_, v___x_2183_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; 
lean_dec(v___x_2205_);
v___x_2207_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2191_ = v___x_2207_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_array_fget_borrowed(v_chain_2175_, v___x_2205_);
lean_dec(v___x_2205_);
lean_inc(v___x_2208_);
v___y_2191_ = v___x_2208_;
goto v___jp_2190_;
}
v___jp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2192_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2191_);
v___x_2193_ = lean_unsigned_to_nat(2u);
v___x_2194_ = lean_mk_empty_array_with_capacity(v___x_2193_);
lean_inc(v___x_2189_);
v___x_2195_ = lean_array_push(v___x_2194_, v___x_2189_);
v___x_2196_ = lean_array_push(v___x_2195_, v___x_2192_);
v___x_2197_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2176_, v___x_2196_);
lean_dec_ref(v___x_2196_);
v___x_2198_ = lean_array_push(v_fst_2178_, v___x_2197_);
v___x_2199_ = lean_nat_add(v_snd_2179_, v___x_2193_);
lean_dec(v_snd_2179_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 1, v___x_2199_);
lean_ctor_set(v___x_2181_, 0, v___x_2198_);
v___x_2201_ = v___x_2181_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
v_a_2177_ = v___x_2201_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg___boxed(lean_object* v_chain_2210_, lean_object* v_format_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2210_, v_format_2211_, v_a_2212_);
lean_dec_ref(v_format_2211_);
lean_dec_ref(v_chain_2210_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(lean_object* v_chain_2214_, lean_object* v_format_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v_fst_2217_; lean_object* v_snd_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2248_; 
v_fst_2217_ = lean_ctor_get(v_a_2216_, 0);
v_snd_2218_ = lean_ctor_get(v_a_2216_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_a_2216_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2220_ = v_a_2216_;
v_isShared_2221_ = v_isSharedCheck_2248_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_snd_2218_);
lean_inc(v_fst_2217_);
lean_dec(v_a_2216_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2248_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2222_ = lean_array_get_size(v_chain_2214_);
v___x_2223_ = lean_nat_dec_lt(v_snd_2218_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2225_; 
if (v_isShared_2221_ == 0)
{
v___x_2225_ = v___x_2220_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_fst_2217_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_snd_2218_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___y_2230_; lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2227_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2228_ = lean_array_get_borrowed(v___x_2227_, v_chain_2214_, v_snd_2218_);
v___x_2243_ = lean_unsigned_to_nat(1u);
v___x_2244_ = lean_nat_add(v_snd_2218_, v___x_2243_);
v___x_2245_ = lean_nat_dec_lt(v___x_2244_, v___x_2222_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
lean_dec(v___x_2244_);
v___x_2246_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2230_ = v___x_2246_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_array_fget_borrowed(v_chain_2214_, v___x_2244_);
lean_dec(v___x_2244_);
lean_inc(v___x_2247_);
v___y_2230_ = v___x_2247_;
goto v___jp_2229_;
}
v___jp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_inc(v___x_2228_);
v___x_2231_ = l_Lean_Fmt_TaggedDoc_nested(v___x_2228_);
v___x_2232_ = lean_unsigned_to_nat(2u);
v___x_2233_ = lean_mk_empty_array_with_capacity(v___x_2232_);
v___x_2234_ = lean_array_push(v___x_2233_, v___x_2231_);
v___x_2235_ = lean_array_push(v___x_2234_, v___y_2230_);
v___x_2236_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2215_, v___x_2235_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = lean_array_push(v_fst_2217_, v___x_2236_);
v___x_2238_ = lean_nat_add(v_snd_2218_, v___x_2232_);
lean_dec(v_snd_2218_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v___x_2238_);
lean_ctor_set(v___x_2220_, 0, v___x_2237_);
v___x_2240_ = v___x_2220_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
v_a_2216_ = v___x_2240_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg___boxed(lean_object* v_chain_2249_, lean_object* v_format_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2249_, v_format_2250_, v_a_2251_);
lean_dec_ref(v_format_2250_);
lean_dec_ref(v_chain_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(lean_object* v_format_2253_, lean_object* v_chain_2254_, uint8_t v_isHeadless_2255_){
_start:
{
lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2263_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2273_; lean_object* v___x_2276_; uint8_t v___y_2278_; uint8_t v_trailingOperator_2291_; 
v___x_2276_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_2291_ = lean_ctor_get_uint8(v_format_2253_, 1);
v___y_2278_ = v_trailingOperator_2291_;
goto v___jp_2277_;
v___jp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v_fst_2261_; 
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___y_2257_);
lean_ctor_set(v___x_2259_, 1, v___y_2258_);
v___x_2260_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2254_, v_format_2253_, v___x_2259_);
v_fst_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_fst_2261_);
lean_dec_ref(v___x_2260_);
return v_fst_2261_;
}
v___jp_2262_:
{
if (v_isHeadless_2255_ == 0)
{
lean_object* v___x_2264_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___y_2257_ = v___y_2263_;
v___y_2258_ = v___x_2264_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_unsigned_to_nat(1u);
v___y_2257_ = v___y_2263_;
v___y_2258_ = v___x_2265_;
goto v___jp_2256_;
}
}
v___jp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_fst_2271_; 
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___y_2267_);
lean_ctor_set(v___x_2269_, 1, v___y_2268_);
v___x_2270_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2254_, v_format_2253_, v___x_2269_);
v_fst_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_fst_2271_);
lean_dec_ref(v___x_2270_);
return v_fst_2271_;
}
v___jp_2272_:
{
if (v_isHeadless_2255_ == 0)
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_unsigned_to_nat(1u);
v___y_2267_ = v___y_2273_;
v___y_2268_ = v___x_2274_;
goto v___jp_2266_;
}
else
{
lean_object* v___x_2275_; 
v___x_2275_ = lean_unsigned_to_nat(0u);
v___y_2267_ = v___y_2273_;
v___y_2268_ = v___x_2275_;
goto v___jp_2266_;
}
}
v___jp_2277_:
{
if (v___y_2278_ == 0)
{
if (v_isHeadless_2255_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = lean_array_get_borrowed(v___x_2276_, v_chain_2254_, v___x_2279_);
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_mk_empty_array_with_capacity(v___x_2281_);
lean_inc(v___x_2280_);
v___x_2283_ = lean_array_push(v___x_2282_, v___x_2280_);
v___y_2273_ = v___x_2283_;
goto v___jp_2272_;
}
else
{
lean_object* v___x_2284_; 
v___x_2284_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2273_ = v___x_2284_;
goto v___jp_2272_;
}
}
else
{
if (v_isHeadless_2255_ == 0)
{
lean_object* v___x_2285_; 
v___x_2285_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2263_ = v___x_2285_;
goto v___jp_2262_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2286_ = lean_unsigned_to_nat(0u);
v___x_2287_ = lean_array_get_borrowed(v___x_2276_, v_chain_2254_, v___x_2286_);
v___x_2288_ = lean_unsigned_to_nat(1u);
v___x_2289_ = lean_mk_empty_array_with_capacity(v___x_2288_);
lean_inc(v___x_2287_);
v___x_2290_ = lean_array_push(v___x_2289_, v___x_2287_);
v___y_2263_ = v___x_2290_;
goto v___jp_2262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain___boxed(lean_object* v_format_2292_, lean_object* v_chain_2293_, lean_object* v_isHeadless_2294_){
_start:
{
uint8_t v_isHeadless_boxed_2295_; lean_object* v_res_2296_; 
v_isHeadless_boxed_2295_ = lean_unbox(v_isHeadless_2294_);
v_res_2296_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2292_, v_chain_2293_, v_isHeadless_boxed_2295_);
lean_dec_ref(v_chain_2293_);
lean_dec_ref(v_format_2292_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(lean_object* v_chain_2297_, lean_object* v_format_2298_, lean_object* v_inst_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2297_, v_format_2298_, v_a_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___boxed(lean_object* v_chain_2302_, lean_object* v_format_2303_, lean_object* v_inst_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(v_chain_2302_, v_format_2303_, v_inst_2304_, v_a_2305_);
lean_dec_ref(v_format_2303_);
lean_dec_ref(v_chain_2302_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(lean_object* v_chain_2307_, lean_object* v_format_2308_, lean_object* v_inst_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2307_, v_format_2308_, v_a_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___boxed(lean_object* v_chain_2312_, lean_object* v_format_2313_, lean_object* v_inst_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(v_chain_2312_, v_format_2313_, v_inst_2314_, v_a_2315_);
lean_dec_ref(v_format_2313_);
lean_dec_ref(v_chain_2312_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(lean_object* v_format_2317_, lean_object* v_docs_2318_){
_start:
{
uint8_t v___y_2320_; uint8_t v___x_2323_; 
v___x_2323_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_format_2317_);
if (v___x_2323_ == 0)
{
uint8_t v___x_2324_; 
v___x_2324_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_format_2317_);
if (v___x_2324_ == 0)
{
uint8_t v_spacing_2325_; 
v_spacing_2325_ = lean_ctor_get_uint8(v_format_2317_, 2);
v___y_2320_ = v_spacing_2325_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2326_; uint8_t v___y_2328_; uint8_t v_spacing_2355_; 
v___x_2326_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_spacing_2355_ = lean_ctor_get_uint8(v_format_2317_, 2);
v___y_2328_ = v_spacing_2355_;
goto v___jp_2327_;
v___jp_2327_:
{
if (v___y_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2329_ = lean_unsigned_to_nat(0u);
v___x_2330_ = lean_array_get_size(v_docs_2318_);
v___x_2331_ = lean_unsigned_to_nat(1u);
v___x_2332_ = lean_nat_sub(v___x_2330_, v___x_2331_);
lean_inc(v___x_2332_);
lean_inc_ref(v_docs_2318_);
v___x_2333_ = l_Array_toSubarray___redArg(v_docs_2318_, v___x_2329_, v___x_2332_);
v___x_2334_ = l_Subarray_copy___redArg(v___x_2333_);
v___x_2335_ = l_Lean_Fmt_TaggedDoc_fill(v___x_2334_);
v___x_2336_ = lean_array_get(v___x_2326_, v_docs_2318_, v___x_2332_);
lean_dec(v___x_2332_);
lean_dec_ref(v_docs_2318_);
v___x_2337_ = lean_unsigned_to_nat(2u);
v___x_2338_ = lean_mk_empty_array_with_capacity(v___x_2337_);
v___x_2339_ = lean_array_push(v___x_2338_, v___x_2335_);
v___x_2340_ = lean_array_push(v___x_2339_, v___x_2336_);
v___x_2341_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2340_, v___y_2328_);
lean_dec_ref(v___x_2340_);
return v___x_2341_;
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_array_get_size(v_docs_2318_);
v___x_2344_ = lean_unsigned_to_nat(1u);
v___x_2345_ = lean_nat_sub(v___x_2343_, v___x_2344_);
lean_inc(v___x_2345_);
lean_inc_ref(v_docs_2318_);
v___x_2346_ = l_Array_toSubarray___redArg(v_docs_2318_, v___x_2342_, v___x_2345_);
v___x_2347_ = l_Subarray_copy___redArg(v___x_2346_);
v___x_2348_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_2347_);
v___x_2349_ = lean_array_get(v___x_2326_, v_docs_2318_, v___x_2345_);
lean_dec(v___x_2345_);
lean_dec_ref(v_docs_2318_);
v___x_2350_ = lean_unsigned_to_nat(2u);
v___x_2351_ = lean_mk_empty_array_with_capacity(v___x_2350_);
v___x_2352_ = lean_array_push(v___x_2351_, v___x_2348_);
v___x_2353_ = lean_array_push(v___x_2352_, v___x_2349_);
v___x_2354_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2353_, v___x_2324_);
lean_dec_ref(v___x_2353_);
return v___x_2354_;
}
}
}
}
else
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_Fmt_Layouts_lines(v_docs_2318_);
lean_dec_ref(v_docs_2318_);
return v___x_2356_;
}
v___jp_2319_:
{
if (v___y_2320_ == 0)
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_Fmt_TaggedDoc_fill(v_docs_2318_);
return v___x_2321_;
}
else
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v_docs_2318_);
return v___x_2322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill___boxed(lean_object* v_format_2357_, lean_object* v_docs_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2357_, v_docs_2358_);
lean_dec_ref(v_format_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(lean_object* v_columnPos_2360_, lean_object* v_indentation_2361_, lean_object* v_nonCumulativeIndentation_2362_){
_start:
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = lean_nat_add(v_indentation_2361_, v_nonCumulativeIndentation_2362_);
v___x_2364_ = lean_nat_dec_le(v_columnPos_2360_, v___x_2363_);
lean_dec(v___x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed(lean_object* v_columnPos_2365_, lean_object* v_indentation_2366_, lean_object* v_nonCumulativeIndentation_2367_){
_start:
{
uint8_t v_res_2368_; lean_object* v_r_2369_; 
v_res_2368_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(v_columnPos_2365_, v_indentation_2366_, v_nonCumulativeIndentation_2367_);
lean_dec(v_nonCumulativeIndentation_2367_);
lean_dec(v_indentation_2366_);
lean_dec(v_columnPos_2365_);
v_r_2369_ = lean_box(v_res_2368_);
return v_r_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(lean_object* v_format_2386_, lean_object* v_combinedChain_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v_firstOperand_2390_; lean_object* v___y_2392_; uint8_t v___y_2412_; uint8_t v_hardNestedFirstOperand_2419_; 
v___x_2388_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2389_ = lean_unsigned_to_nat(0u);
v_firstOperand_2390_ = lean_array_get_borrowed(v___x_2388_, v_combinedChain_2387_, v___x_2389_);
v_hardNestedFirstOperand_2419_ = lean_ctor_get_uint8(v_format_2386_, 0);
v___y_2412_ = v_hardNestedFirstOperand_2419_;
goto v___jp_2411_;
v___jp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_compactFirstOperation_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v_compactedChain_2406_; lean_object* v___x_2407_; 
v___x_2393_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion));
v___x_2394_ = l_Lean_Fmt_TaggedDoc_guarded(v___x_2393_, v___y_2392_);
v___x_2395_ = lean_unsigned_to_nat(2u);
v___x_2396_ = lean_mk_empty_array_with_capacity(v___x_2395_);
lean_inc(v_firstOperand_2390_);
v___x_2397_ = lean_array_push(v___x_2396_, v_firstOperand_2390_);
v___x_2398_ = lean_array_push(v___x_2397_, v___x_2394_);
v_compactFirstOperation_2399_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2386_, v___x_2398_);
lean_dec_ref(v___x_2398_);
v___x_2400_ = lean_unsigned_to_nat(1u);
v___x_2401_ = lean_mk_empty_array_with_capacity(v___x_2400_);
v___x_2402_ = lean_array_push(v___x_2401_, v_compactFirstOperation_2399_);
v___x_2403_ = lean_array_get_size(v_combinedChain_2387_);
v___x_2404_ = l_Array_toSubarray___redArg(v_combinedChain_2387_, v___x_2395_, v___x_2403_);
v___x_2405_ = l_Subarray_copy___redArg(v___x_2404_);
v_compactedChain_2406_ = l_Array_append___redArg(v___x_2402_, v___x_2405_);
lean_dec_ref(v___x_2405_);
v___x_2407_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2386_, v_compactedChain_2406_);
return v___x_2407_;
}
v___jp_2408_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_unsigned_to_nat(1u);
v___x_2410_ = lean_array_get_borrowed(v___x_2388_, v_combinedChain_2387_, v___x_2409_);
lean_inc(v___x_2410_);
v___y_2392_ = v___x_2410_;
goto v___jp_2391_;
}
v___jp_2411_:
{
if (v___y_2412_ == 0)
{
goto v___jp_2408_;
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2413_ = lean_unsigned_to_nat(2u);
v___x_2414_ = lean_array_get_size(v_combinedChain_2387_);
v___x_2415_ = lean_nat_dec_lt(v___x_2413_, v___x_2414_);
if (v___x_2415_ == 0)
{
goto v___jp_2408_;
}
else
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = lean_array_get_borrowed(v___x_2388_, v_combinedChain_2387_, v___x_2416_);
lean_inc(v___x_2417_);
v___x_2418_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_2417_);
v___y_2392_ = v___x_2418_;
goto v___jp_2391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation___boxed(lean_object* v_format_2420_, lean_object* v_combinedChain_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2420_, v_combinedChain_2421_);
lean_dec_ref(v_format_2420_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(lean_object* v_format_2423_, lean_object* v_docs_2424_, lean_object* v_wrap_2425_){
_start:
{
uint8_t v___y_2427_; uint8_t v_spacing_2430_; 
v_spacing_2430_ = lean_ctor_get_uint8(v_format_2423_, 2);
v___y_2427_ = v_spacing_2430_;
goto v___jp_2426_;
v___jp_2426_:
{
if (v___y_2427_ == 0)
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_Fmt_TaggedDoc_fillWrapping(v_docs_2424_, v_wrap_2425_);
return v___x_2428_;
}
else
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(v_docs_2424_, v_wrap_2425_);
return v___x_2429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping___boxed(lean_object* v_format_2431_, lean_object* v_docs_2432_, lean_object* v_wrap_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2431_, v_docs_2432_, v_wrap_2433_);
lean_dec_ref(v_format_2431_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(lean_object* v___x_2435_, size_t v_sz_2436_, size_t v_i_2437_, lean_object* v_bs_2438_){
_start:
{
uint8_t v___x_2439_; 
v___x_2439_ = lean_usize_dec_lt(v_i_2437_, v_sz_2436_);
if (v___x_2439_ == 0)
{
return v_bs_2438_;
}
else
{
lean_object* v___x_2440_; lean_object* v_v_2441_; lean_object* v___x_2442_; lean_object* v_bs_x27_2443_; lean_object* v___y_2445_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2440_ = lean_unsigned_to_nat(1u);
v_v_2441_ = lean_array_uget(v_bs_2438_, v_i_2437_);
v___x_2442_ = lean_unsigned_to_nat(0u);
v_bs_x27_2443_ = lean_array_uset(v_bs_2438_, v_i_2437_, v___x_2442_);
v___x_2450_ = lean_usize_to_nat(v_i_2437_);
v___x_2451_ = lean_nat_sub(v___x_2435_, v___x_2440_);
v___x_2452_ = lean_nat_dec_lt(v___x_2450_, v___x_2451_);
lean_dec(v___x_2451_);
lean_dec(v___x_2450_);
if (v___x_2452_ == 0)
{
v___y_2445_ = v_v_2441_;
goto v___jp_2444_;
}
else
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2441_);
v___y_2445_ = v___x_2453_;
goto v___jp_2444_;
}
v___jp_2444_:
{
size_t v___x_2446_; size_t v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = ((size_t)1ULL);
v___x_2447_ = lean_usize_add(v_i_2437_, v___x_2446_);
v___x_2448_ = lean_array_uset(v_bs_x27_2443_, v_i_2437_, v___y_2445_);
v_i_2437_ = v___x_2447_;
v_bs_2438_ = v___x_2448_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg___boxed(lean_object* v___x_2454_, lean_object* v_sz_2455_, lean_object* v_i_2456_, lean_object* v_bs_2457_){
_start:
{
size_t v_sz_boxed_2458_; size_t v_i_boxed_2459_; lean_object* v_res_2460_; 
v_sz_boxed_2458_ = lean_unbox_usize(v_sz_2455_);
lean_dec(v_sz_2455_);
v_i_boxed_2459_ = lean_unbox_usize(v_i_2456_);
lean_dec(v_i_2456_);
v_res_2460_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2454_, v_sz_boxed_2458_, v_i_boxed_2459_, v_bs_2457_);
lean_dec(v___x_2454_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object* v_chain_2475_, lean_object* v_format_2476_){
_start:
{
uint8_t v___y_2478_; lean_object* v_doc_2479_; lean_object* v___x_2483_; lean_object* v_snd_2484_; lean_object* v_fst_2485_; lean_object* v_fst_2486_; lean_object* v_snd_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2483_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2476_, v_chain_2475_);
v_snd_2484_ = lean_ctor_get(v___x_2483_, 1);
lean_inc(v_snd_2484_);
v_fst_2485_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_fst_2485_);
lean_dec_ref(v___x_2483_);
v_fst_2486_ = lean_ctor_get(v_snd_2484_, 0);
lean_inc(v_fst_2486_);
v_snd_2487_ = lean_ctor_get(v_snd_2484_, 1);
lean_inc(v_snd_2487_);
lean_dec(v_snd_2484_);
v___x_2488_ = lean_array_get_size(v_fst_2485_);
v___x_2489_ = lean_unsigned_to_nat(0u);
v___x_2490_ = lean_nat_dec_eq(v___x_2488_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v_combinedChain_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___y_2497_; uint8_t v___y_2498_; lean_object* v_doc_2499_; lean_object* v___y_2514_; uint8_t v___y_2515_; lean_object* v___y_2516_; uint8_t v___x_2524_; lean_object* v___y_2526_; uint8_t v___y_2527_; lean_object* v_combinedChain_2533_; uint8_t v___y_2536_; uint8_t v___y_2543_; uint8_t v___y_2544_; uint8_t v___y_2552_; 
v___x_2491_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2492_ = lean_unbox(v_fst_2486_);
v_combinedChain_2493_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2476_, v_fst_2485_, v___x_2492_);
v___x_2494_ = lean_array_get_size(v_combinedChain_2493_);
v___x_2495_ = lean_unsigned_to_nat(1u);
v___x_2524_ = lean_nat_dec_eq(v___x_2494_, v___x_2495_);
if (v___x_2524_ == 0)
{
uint8_t v_trailingOperator_2554_; 
v_trailingOperator_2554_ = lean_ctor_get_uint8(v_format_2476_, 1);
v___y_2552_ = v_trailingOperator_2554_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2555_; 
lean_dec(v_snd_2487_);
lean_dec(v_fst_2486_);
lean_dec(v_fst_2485_);
v___x_2555_ = lean_array_get(v___x_2491_, v_combinedChain_2493_, v___x_2489_);
lean_dec_ref(v_combinedChain_2493_);
return v___x_2555_;
}
v___jp_2496_:
{
lean_object* v___x_2500_; lean_object* v_lastOperand_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2500_ = lean_nat_sub(v___x_2488_, v___x_2495_);
v_lastOperand_2501_ = lean_array_get(v___x_2491_, v_fst_2485_, v___x_2500_);
lean_dec(v___x_2500_);
lean_dec(v_fst_2485_);
v___x_2502_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
v___x_2503_ = lean_unbox(v_snd_2487_);
lean_inc_ref(v___y_2497_);
lean_inc(v_lastOperand_2501_);
lean_inc_ref(v_doc_2499_);
v___x_2504_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2476_, v_doc_2499_, v_lastOperand_2501_, v___x_2503_, v___y_2497_, v___x_2502_);
if (lean_obj_tag(v___x_2504_) == 1)
{
lean_object* v_val_2505_; 
lean_dec(v_lastOperand_2501_);
lean_dec_ref(v_doc_2499_);
lean_dec_ref(v___y_2497_);
lean_dec(v_snd_2487_);
v_val_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_val_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___y_2478_ = v___y_2498_;
v_doc_2479_ = v_val_2505_;
goto v___jp_2477_;
}
else
{
uint8_t v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v___x_2504_);
v___x_2506_ = lean_unbox(v_snd_2487_);
lean_inc_ref(v___y_2497_);
lean_inc(v_lastOperand_2501_);
lean_inc_ref(v_doc_2499_);
v___x_2507_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2476_, v_doc_2499_, v_lastOperand_2501_, v___x_2506_, v___y_2497_);
if (lean_obj_tag(v___x_2507_) == 1)
{
lean_object* v_val_2508_; 
lean_dec(v_lastOperand_2501_);
lean_dec_ref(v_doc_2499_);
lean_dec_ref(v___y_2497_);
lean_dec(v_snd_2487_);
v_val_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_val_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v___y_2478_ = v___y_2498_;
v_doc_2479_ = v_val_2508_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; 
lean_dec(v___x_2507_);
v___x_2509_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
v___x_2510_ = lean_unbox(v_snd_2487_);
lean_dec(v_snd_2487_);
lean_inc_ref(v_doc_2499_);
v___x_2511_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2476_, v_doc_2499_, v_lastOperand_2501_, v___x_2510_, v___y_2497_, v___x_2509_);
if (lean_obj_tag(v___x_2511_) == 1)
{
lean_object* v_val_2512_; 
lean_dec_ref(v_doc_2499_);
v_val_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_val_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v___y_2478_ = v___y_2498_;
v_doc_2479_ = v_val_2512_;
goto v___jp_2477_;
}
else
{
lean_dec(v___x_2511_);
v___y_2478_ = v___y_2498_;
v_doc_2479_ = v_doc_2499_;
goto v___jp_2477_;
}
}
}
}
v___jp_2513_:
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_unbox(v_fst_2486_);
lean_dec(v_fst_2486_);
if (v___x_2517_ == 0)
{
if (v___y_2515_ == 0)
{
v___y_2497_ = v___y_2514_;
v___y_2498_ = v___y_2515_;
v_doc_2499_ = v___y_2516_;
goto v___jp_2496_;
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_doc_2523_; 
lean_inc_ref(v___y_2514_);
v___x_2518_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2476_, v___y_2514_);
v___x_2519_ = lean_unsigned_to_nat(2u);
v___x_2520_ = lean_mk_empty_array_with_capacity(v___x_2519_);
v___x_2521_ = lean_array_push(v___x_2520_, v___x_2518_);
v___x_2522_ = lean_array_push(v___x_2521_, v___y_2516_);
v_doc_2523_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2522_);
v___y_2497_ = v___y_2514_;
v___y_2498_ = v___y_2515_;
v_doc_2499_ = v_doc_2523_;
goto v___jp_2496_;
}
}
else
{
v___y_2497_ = v___y_2514_;
v___y_2498_ = v___y_2515_;
v_doc_2499_ = v___y_2516_;
goto v___jp_2496_;
}
}
v___jp_2525_:
{
if (v___y_2527_ == 0)
{
uint8_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = 1;
lean_inc_ref(v___y_2526_);
v___x_2529_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2476_, v___y_2526_);
v___y_2514_ = v___y_2526_;
v___y_2515_ = v___x_2528_;
v___y_2516_ = v___x_2529_;
goto v___jp_2513_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
lean_inc_ref(v___y_2526_);
v___x_2531_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2476_, v___y_2526_, v___x_2530_);
v___y_2514_ = v___y_2526_;
v___y_2515_ = v___x_2524_;
v___y_2516_ = v___x_2531_;
goto v___jp_2513_;
}
}
v___jp_2532_:
{
uint8_t v_trailingOperator_2534_; 
v_trailingOperator_2534_ = lean_ctor_get_uint8(v_format_2476_, 1);
v___y_2526_ = v_combinedChain_2533_;
v___y_2527_ = v_trailingOperator_2534_;
goto v___jp_2525_;
}
v___jp_2535_:
{
if (v___y_2536_ == 0)
{
v_combinedChain_2533_ = v_combinedChain_2493_;
goto v___jp_2532_;
}
else
{
size_t v_sz_2537_; size_t v___x_2538_; lean_object* v_combinedChain_2539_; 
v_sz_2537_ = lean_array_size(v_combinedChain_2493_);
v___x_2538_ = ((size_t)0ULL);
v_combinedChain_2539_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2494_, v_sz_2537_, v___x_2538_, v_combinedChain_2493_);
v_combinedChain_2533_ = v_combinedChain_2539_;
goto v___jp_2532_;
}
}
v___jp_2540_:
{
uint8_t v_hardNestedFirstOperand_2541_; 
v_hardNestedFirstOperand_2541_ = lean_ctor_get_uint8(v_format_2476_, 0);
v___y_2536_ = v_hardNestedFirstOperand_2541_;
goto v___jp_2535_;
}
v___jp_2542_:
{
if (v___y_2544_ == 0)
{
if (v___y_2543_ == 0)
{
v_combinedChain_2533_ = v_combinedChain_2493_;
goto v___jp_2532_;
}
else
{
goto v___jp_2540_;
}
}
else
{
uint8_t v___x_2545_; 
v___x_2545_ = lean_nat_dec_lt(v___x_2489_, v___x_2494_);
if (v___x_2545_ == 0)
{
v_combinedChain_2533_ = v_combinedChain_2493_;
goto v___jp_2532_;
}
else
{
lean_object* v_v_2546_; lean_object* v___x_2547_; lean_object* v_xs_x27_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v_v_2546_ = lean_array_fget(v_combinedChain_2493_, v___x_2489_);
v___x_2547_ = lean_box(0);
v_xs_x27_2548_ = lean_array_fset(v_combinedChain_2493_, v___x_2489_, v___x_2547_);
v___x_2549_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2546_);
v___x_2550_ = lean_array_fset(v_xs_x27_2548_, v___x_2489_, v___x_2549_);
v_combinedChain_2533_ = v___x_2550_;
goto v___jp_2532_;
}
}
}
v___jp_2551_:
{
if (v___y_2552_ == 0)
{
uint8_t v_hardNestedFirstOperand_2553_; 
v_hardNestedFirstOperand_2553_ = lean_ctor_get_uint8(v_format_2476_, 0);
v___y_2543_ = v___y_2552_;
v___y_2544_ = v_hardNestedFirstOperand_2553_;
goto v___jp_2542_;
}
else
{
goto v___jp_2540_;
}
}
}
else
{
lean_object* v___x_2556_; 
lean_dec(v_snd_2487_);
lean_dec(v_fst_2486_);
lean_dec(v_fst_2485_);
v___x_2556_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_2556_;
}
v___jp_2477_:
{
if (v___y_2478_ == 0)
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2479_);
return v___x_2480_;
}
else
{
lean_object* v_doc_2481_; lean_object* v___x_2482_; 
v_doc_2481_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2479_);
v___x_2482_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2481_);
return v___x_2482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator___boxed(lean_object* v_chain_2557_, lean_object* v_format_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_2557_, v_format_2558_);
lean_dec_ref(v_format_2558_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(lean_object* v___x_2560_, lean_object* v_as_2561_, size_t v_sz_2562_, size_t v_i_2563_, lean_object* v_bs_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2560_, v_sz_2562_, v_i_2563_, v_bs_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___boxed(lean_object* v___x_2566_, lean_object* v_as_2567_, lean_object* v_sz_2568_, lean_object* v_i_2569_, lean_object* v_bs_2570_){
_start:
{
size_t v_sz_boxed_2571_; size_t v_i_boxed_2572_; lean_object* v_res_2573_; 
v_sz_boxed_2571_ = lean_unbox_usize(v_sz_2568_);
lean_dec(v_sz_2568_);
v_i_boxed_2572_ = lean_unbox_usize(v_i_2569_);
lean_dec(v_i_2569_);
v_res_2573_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(v___x_2566_, v_as_2567_, v_sz_boxed_2571_, v_i_boxed_2572_, v_bs_2570_);
lean_dec_ref(v_as_2567_);
lean_dec(v___x_2566_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object* v_lhs_2574_, lean_object* v_typeAscriptionTk_2575_, lean_object* v_rhs_2576_, lean_object* v_format_2577_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2578_ = lean_unsigned_to_nat(3u);
v___x_2579_ = lean_mk_empty_array_with_capacity(v___x_2578_);
v___x_2580_ = lean_array_push(v___x_2579_, v_lhs_2574_);
v___x_2581_ = lean_array_push(v___x_2580_, v_typeAscriptionTk_2575_);
v___x_2582_ = lean_array_push(v___x_2581_, v_rhs_2576_);
v___x_2583_ = l_Lean_Fmt_Layouts_infixOperator(v___x_2582_, v_format_2577_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription___boxed(lean_object* v_lhs_2584_, lean_object* v_typeAscriptionTk_2585_, lean_object* v_rhs_2586_, lean_object* v_format_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Fmt_Layouts_typeAscription(v_lhs_2584_, v_typeAscriptionTk_2585_, v_rhs_2586_, v_format_2587_);
lean_dec_ref(v_format_2587_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl(lean_object* v_x_2589_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = lean_obj_tag_nat(v_x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl___boxed(lean_object* v_x_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___impl(v_x_2591_);
lean_dec_ref(v_x_2591_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(lean_object* v_t_2593_, lean_object* v_k_2594_){
_start:
{
if (lean_obj_tag(v_t_2593_) == 0)
{
uint8_t v_spacing_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_spacing_2595_ = lean_ctor_get_uint8(v_t_2593_, 0);
lean_dec_ref_known(v_t_2593_, 0);
v___x_2596_ = lean_box(v_spacing_2595_);
v___x_2597_ = lean_apply_1(v_k_2594_, v___x_2596_);
return v___x_2597_;
}
else
{
lean_object* v_sep_2598_; uint8_t v_unindentedRb_2599_; uint8_t v_stickynessKind_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v_sep_2598_ = lean_ctor_get(v_t_2593_, 0);
lean_inc_ref(v_sep_2598_);
v_unindentedRb_2599_ = lean_ctor_get_uint8(v_t_2593_, sizeof(void*)*1);
v_stickynessKind_2600_ = lean_ctor_get_uint8(v_t_2593_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_2593_, 1);
v___x_2601_ = lean_box(v_unindentedRb_2599_);
v___x_2602_ = lean_box(v_stickynessKind_2600_);
v___x_2603_ = lean_apply_3(v_k_2594_, v_sep_2598_, v___x_2601_, v___x_2602_);
return v___x_2603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(lean_object* v_motive_2604_, lean_object* v_ctorIdx_2605_, lean_object* v_t_2606_, lean_object* v_h_2607_, lean_object* v_k_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2606_, v_k_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___boxed(lean_object* v_motive_2610_, lean_object* v_ctorIdx_2611_, lean_object* v_t_2612_, lean_object* v_h_2613_, lean_object* v_k_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(v_motive_2610_, v_ctorIdx_2611_, v_t_2612_, v_h_2613_, v_k_2614_);
lean_dec(v_ctorIdx_2611_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim___redArg(lean_object* v_t_2616_, lean_object* v_dense_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2616_, v_dense_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim(lean_object* v_motive_2619_, lean_object* v_t_2620_, lean_object* v_h_2621_, lean_object* v_dense_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2620_, v_dense_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim___redArg(lean_object* v_t_2624_, lean_object* v_sparse_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2624_, v_sparse_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim(lean_object* v_motive_2627_, lean_object* v_t_2628_, lean_object* v_h_2629_, lean_object* v_sparse_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2628_, v_sparse_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object* v_lb_2632_, lean_object* v_rb_2633_, uint8_t v_isBodyAligned_2634_, uint8_t v_isBodyPseudoAligned_2635_, uint8_t v___x_2636_, lean_object* v_body_2637_){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v_doc_2644_; 
v___x_2638_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2637_);
v___x_2639_ = lean_unsigned_to_nat(3u);
v___x_2640_ = lean_mk_empty_array_with_capacity(v___x_2639_);
v___x_2641_ = lean_array_push(v___x_2640_, v_lb_2632_);
v___x_2642_ = lean_array_push(v___x_2641_, v___x_2638_);
v___x_2643_ = lean_array_push(v___x_2642_, v_rb_2633_);
v_doc_2644_ = l_Lean_Fmt_Layouts_atomic(v___x_2643_);
lean_dec_ref(v___x_2643_);
if (v_isBodyAligned_2634_ == 0)
{
if (v_isBodyPseudoAligned_2635_ == 0)
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2644_, v___x_2636_);
return v___x_2645_;
}
else
{
lean_object* v_doc_2646_; lean_object* v___x_2647_; 
v_doc_2646_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2644_);
v___x_2647_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2646_, v___x_2636_);
return v___x_2647_;
}
}
else
{
lean_object* v_doc_2648_; lean_object* v___x_2649_; 
v_doc_2648_ = l_Lean_Fmt_TaggedDoc_aligned(v_doc_2644_);
v___x_2649_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2648_, v___x_2636_);
return v___x_2649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0___boxed(lean_object* v_lb_2650_, lean_object* v_rb_2651_, lean_object* v_isBodyAligned_2652_, lean_object* v_isBodyPseudoAligned_2653_, lean_object* v___x_2654_, lean_object* v_body_2655_){
_start:
{
uint8_t v_isBodyAligned_boxed_2656_; uint8_t v_isBodyPseudoAligned_boxed_2657_; uint8_t v___x_590__boxed_2658_; lean_object* v_res_2659_; 
v_isBodyAligned_boxed_2656_ = lean_unbox(v_isBodyAligned_2652_);
v_isBodyPseudoAligned_boxed_2657_ = lean_unbox(v_isBodyPseudoAligned_2653_);
v___x_590__boxed_2658_ = lean_unbox(v___x_2654_);
v_res_2659_ = l_Lean_Fmt_Layouts_bracketed___lam__0(v_lb_2650_, v_rb_2651_, v_isBodyAligned_boxed_2656_, v_isBodyPseudoAligned_boxed_2657_, v___x_590__boxed_2658_, v_body_2655_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object* v_lb_2663_, lean_object* v_body_2664_, lean_object* v_rb_2665_, lean_object* v_format_2666_){
_start:
{
uint8_t v___x_2667_; 
v___x_2667_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2664_);
if (v___x_2667_ == 0)
{
lean_object* v_doc_2668_; uint8_t v___x_2669_; 
v_doc_2668_ = lean_ctor_get(v_body_2664_, 0);
v___x_2669_ = 1;
if (lean_obj_tag(v_format_2666_) == 0)
{
uint8_t v_spacing_2670_; 
v_spacing_2670_ = lean_ctor_get_uint8(v_format_2666_, 0);
lean_dec_ref_known(v_format_2666_, 0);
if (v_spacing_2670_ == 0)
{
uint8_t v_isBodyAligned_2671_; uint8_t v_isBodyPseudoAligned_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v_f_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_inc(v_doc_2668_);
v_isBodyAligned_2671_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2668_);
lean_inc_ref(v_body_2664_);
v_isBodyPseudoAligned_2672_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_body_2664_);
v___x_2673_ = lean_box(v_isBodyAligned_2671_);
v___x_2674_ = lean_box(v_isBodyPseudoAligned_2672_);
v___x_2675_ = lean_box(v___x_2669_);
v_f_2676_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_bracketed___lam__0___boxed), 6, 5);
lean_closure_set(v_f_2676_, 0, v_lb_2663_);
lean_closure_set(v_f_2676_, 1, v_rb_2665_);
lean_closure_set(v_f_2676_, 2, v___x_2673_);
lean_closure_set(v_f_2676_, 3, v___x_2674_);
lean_closure_set(v_f_2676_, 4, v___x_2675_);
v___x_2677_ = ((lean_object*)(l_Lean_Fmt_Layouts_bracketed___closed__0));
v___x_2678_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_body_2664_, v_f_2676_, v___x_2677_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2679_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2664_);
v___x_2680_ = lean_unsigned_to_nat(3u);
v___x_2681_ = lean_mk_empty_array_with_capacity(v___x_2680_);
v___x_2682_ = lean_array_push(v___x_2681_, v_lb_2663_);
v___x_2683_ = lean_array_push(v___x_2682_, v___x_2679_);
v___x_2684_ = lean_array_push(v___x_2683_, v_rb_2665_);
v___x_2685_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2684_);
lean_dec_ref(v___x_2684_);
return v___x_2685_;
}
}
else
{
lean_object* v_sep_2686_; uint8_t v_unindentedRb_2687_; uint8_t v_stickynessKind_2688_; lean_object* v_sparse_2690_; lean_object* v___y_2701_; lean_object* v___y_2704_; lean_object* v___y_2716_; lean_object* v___y_2728_; lean_object* v_body_2740_; uint8_t v___x_2741_; 
v_sep_2686_ = lean_ctor_get(v_format_2666_, 0);
lean_inc_ref(v_sep_2686_);
v_unindentedRb_2687_ = lean_ctor_get_uint8(v_format_2666_, sizeof(void*)*1);
v_stickynessKind_2688_ = lean_ctor_get_uint8(v_format_2666_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_format_2666_, 1);
v_body_2740_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_2664_);
v___x_2741_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2686_);
if (v___x_2741_ == 0)
{
uint8_t v___x_2742_; 
v___x_2742_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2740_);
if (v___x_2742_ == 0)
{
lean_object* v_doc_2743_; lean_object* v_doc_2744_; uint8_t v___x_2745_; 
v_doc_2743_ = lean_ctor_get(v_sep_2686_, 0);
v_doc_2744_ = lean_ctor_get(v_body_2740_, 0);
lean_inc(v_doc_2744_);
lean_dec_ref(v_body_2740_);
v___x_2745_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2743_);
if (v___x_2745_ == 0)
{
uint8_t v___x_2746_; 
v___x_2746_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2744_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_inc(v_doc_2743_);
v___x_2747_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2743_, v_doc_2744_);
v___x_2748_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2747_);
v___y_2728_ = v___x_2748_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2749_; 
lean_dec(v_doc_2744_);
lean_inc(v_doc_2743_);
v___x_2749_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2743_);
v___y_2728_ = v___x_2749_;
goto v___jp_2727_;
}
}
else
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2744_);
v___y_2728_ = v___x_2750_;
goto v___jp_2727_;
}
}
else
{
lean_dec_ref(v_body_2740_);
lean_inc_ref(v_sep_2686_);
v___y_2728_ = v_sep_2686_;
goto v___jp_2727_;
}
}
else
{
v___y_2728_ = v_body_2740_;
goto v___jp_2727_;
}
v___jp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v_stickyVariant_2697_; lean_object* v_nonStickyVariant_2698_; lean_object* v___x_2699_; 
lean_inc_ref(v_sparse_2690_);
v___x_2691_ = l_Lean_Fmt_TaggedDoc_aligned(v_sparse_2690_);
v___x_2692_ = lean_unsigned_to_nat(2u);
v___x_2693_ = lean_mk_empty_array_with_capacity(v___x_2692_);
v___x_2694_ = lean_array_push(v___x_2693_, v_sparse_2690_);
v___x_2695_ = lean_array_push(v___x_2694_, v___x_2691_);
v___x_2696_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2695_);
v_stickyVariant_2697_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_2696_, v___x_2669_);
lean_inc_ref(v_stickyVariant_2697_);
v_nonStickyVariant_2698_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_stickyVariant_2697_);
v___x_2699_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_2698_, v_stickyVariant_2697_, v_stickynessKind_2688_);
return v___x_2699_;
}
v___jp_2700_:
{
if (v_unindentedRb_2687_ == 0)
{
v_sparse_2690_ = v___y_2701_;
goto v___jp_2689_;
}
else
{
lean_object* v_sparse_2702_; 
v_sparse_2702_ = l_Lean_Fmt_TaggedDoc_unindented(v___y_2701_, v___x_2669_);
v_sparse_2690_ = v_sparse_2702_;
goto v___jp_2689_;
}
}
v___jp_2703_:
{
uint8_t v___x_2705_; 
v___x_2705_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_2704_);
if (v___x_2705_ == 0)
{
uint8_t v___x_2706_; 
v___x_2706_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rb_2665_);
if (v___x_2706_ == 0)
{
lean_object* v_doc_2707_; lean_object* v_doc_2708_; uint8_t v___x_2709_; 
v_doc_2707_ = lean_ctor_get(v___y_2704_, 0);
lean_inc(v_doc_2707_);
lean_dec_ref(v___y_2704_);
v_doc_2708_ = lean_ctor_get(v_rb_2665_, 0);
lean_inc(v_doc_2708_);
lean_dec_ref(v_rb_2665_);
v___x_2709_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2707_);
if (v___x_2709_ == 0)
{
uint8_t v___x_2710_; 
v___x_2710_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2708_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2707_, v_doc_2708_);
v___x_2712_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2711_);
v___y_2701_ = v___x_2712_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_2713_; 
lean_dec(v_doc_2708_);
v___x_2713_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2707_);
v___y_2701_ = v___x_2713_;
goto v___jp_2700_;
}
}
else
{
lean_object* v___x_2714_; 
lean_dec(v_doc_2707_);
v___x_2714_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2708_);
v___y_2701_ = v___x_2714_;
goto v___jp_2700_;
}
}
else
{
lean_dec_ref(v_rb_2665_);
v___y_2701_ = v___y_2704_;
goto v___jp_2700_;
}
}
else
{
lean_dec_ref(v___y_2704_);
v___y_2701_ = v_rb_2665_;
goto v___jp_2700_;
}
}
v___jp_2715_:
{
uint8_t v___x_2717_; 
v___x_2717_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_2716_);
if (v___x_2717_ == 0)
{
uint8_t v___x_2718_; 
v___x_2718_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2686_);
if (v___x_2718_ == 0)
{
lean_object* v_doc_2719_; lean_object* v_doc_2720_; uint8_t v___x_2721_; 
v_doc_2719_ = lean_ctor_get(v___y_2716_, 0);
lean_inc(v_doc_2719_);
lean_dec_ref(v___y_2716_);
v_doc_2720_ = lean_ctor_get(v_sep_2686_, 0);
lean_inc(v_doc_2720_);
lean_dec_ref(v_sep_2686_);
v___x_2721_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2719_);
if (v___x_2721_ == 0)
{
uint8_t v___x_2722_; 
v___x_2722_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2720_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2719_, v_doc_2720_);
v___x_2724_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2723_);
v___y_2704_ = v___x_2724_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2725_; 
lean_dec(v_doc_2720_);
v___x_2725_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2719_);
v___y_2704_ = v___x_2725_;
goto v___jp_2703_;
}
}
else
{
lean_object* v___x_2726_; 
lean_dec(v_doc_2719_);
v___x_2726_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2720_);
v___y_2704_ = v___x_2726_;
goto v___jp_2703_;
}
}
else
{
lean_dec_ref(v_sep_2686_);
v___y_2704_ = v___y_2716_;
goto v___jp_2703_;
}
}
else
{
lean_dec_ref(v___y_2716_);
v___y_2704_ = v_sep_2686_;
goto v___jp_2703_;
}
}
v___jp_2727_:
{
lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2729_ = l_Lean_Fmt_TaggedDoc_hardNested(v___y_2728_);
v___x_2730_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_lb_2663_);
if (v___x_2730_ == 0)
{
uint8_t v___x_2731_; 
v___x_2731_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2729_);
if (v___x_2731_ == 0)
{
lean_object* v_doc_2732_; lean_object* v_doc_2733_; uint8_t v___x_2734_; 
v_doc_2732_ = lean_ctor_get(v_lb_2663_, 0);
lean_inc(v_doc_2732_);
lean_dec_ref(v_lb_2663_);
v_doc_2733_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_doc_2733_);
lean_dec_ref(v___x_2729_);
v___x_2734_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2732_);
if (v___x_2734_ == 0)
{
uint8_t v___x_2735_; 
v___x_2735_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2733_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2732_, v_doc_2733_);
v___x_2737_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2736_);
v___y_2716_ = v___x_2737_;
goto v___jp_2715_;
}
else
{
lean_object* v___x_2738_; 
lean_dec(v_doc_2733_);
v___x_2738_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2732_);
v___y_2716_ = v___x_2738_;
goto v___jp_2715_;
}
}
else
{
lean_object* v___x_2739_; 
lean_dec(v_doc_2732_);
v___x_2739_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2733_);
v___y_2716_ = v___x_2739_;
goto v___jp_2715_;
}
}
else
{
lean_dec_ref(v___x_2729_);
v___y_2716_ = v_lb_2663_;
goto v___jp_2715_;
}
}
else
{
lean_dec_ref(v_lb_2663_);
v___y_2716_ = v___x_2729_;
goto v___jp_2715_;
}
}
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_dec_ref(v_format_2666_);
lean_dec_ref(v_body_2664_);
v___x_2751_ = lean_unsigned_to_nat(2u);
v___x_2752_ = lean_mk_empty_array_with_capacity(v___x_2751_);
v___x_2753_ = lean_array_push(v___x_2752_, v_lb_2663_);
v___x_2754_ = lean_array_push(v___x_2753_, v_rb_2665_);
v___x_2755_ = l_Lean_Fmt_Layouts_atomic(v___x_2754_);
lean_dec_ref(v___x_2754_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object* v_lbTk_2758_, lean_object* v_body_2759_, lean_object* v_rbTk_2760_){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_2762_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2758_, v_body_2759_, v_rbTk_2760_, v___x_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0(void){
_start:
{
uint8_t v___x_2763_; uint8_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = 1;
v___x_2764_ = 1;
v___x_2765_ = l_Lean_Fmt_TaggedDoc_break;
v___x_2766_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set_uint8(v___x_2766_, sizeof(void*)*1, v___x_2764_);
lean_ctor_set_uint8(v___x_2766_, sizeof(void*)*1 + 1, v___x_2763_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object* v_lbTk_2767_, lean_object* v_seq_2768_, lean_object* v_rbTk_2769_){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_obj_once(&l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0, &l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0);
v___x_2771_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2767_, v_seq_2768_, v_rbTk_2769_, v___x_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(uint8_t v_isComplex_2772_, lean_object* v_subAlts_2773_){
_start:
{
if (v_isComplex_2772_ == 0)
{
uint8_t v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = 1;
v___x_2775_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_subAlts_2773_, v___x_2774_);
return v___x_2775_;
}
else
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Fmt_Layouts_lines(v_subAlts_2773_);
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts___boxed(lean_object* v_isComplex_2777_, lean_object* v_subAlts_2778_){
_start:
{
uint8_t v_isComplex_boxed_2779_; lean_object* v_res_2780_; 
v_isComplex_boxed_2779_ = lean_unbox(v_isComplex_2777_);
v_res_2780_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_boxed_2779_, v_subAlts_2778_);
lean_dec_ref(v_subAlts_2778_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t v_sz_2781_, size_t v_i_2782_, lean_object* v_bs_2783_){
_start:
{
uint8_t v___x_2784_; 
v___x_2784_ = lean_usize_dec_lt(v_i_2782_, v_sz_2781_);
if (v___x_2784_ == 0)
{
return v_bs_2783_;
}
else
{
lean_object* v_v_2785_; lean_object* v___x_2786_; lean_object* v_bs_x27_2787_; lean_object* v___x_2788_; size_t v___x_2789_; size_t v___x_2790_; lean_object* v___x_2791_; 
v_v_2785_ = lean_array_uget(v_bs_2783_, v_i_2782_);
v___x_2786_ = lean_unsigned_to_nat(0u);
v_bs_x27_2787_ = lean_array_uset(v_bs_2783_, v_i_2782_, v___x_2786_);
v___x_2788_ = l_Lean_Fmt_TaggedDoc_nested(v_v_2785_);
v___x_2789_ = ((size_t)1ULL);
v___x_2790_ = lean_usize_add(v_i_2782_, v___x_2789_);
v___x_2791_ = lean_array_uset(v_bs_x27_2787_, v_i_2782_, v___x_2788_);
v_i_2782_ = v___x_2790_;
v_bs_2783_ = v___x_2791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object* v_sz_2793_, lean_object* v_i_2794_, lean_object* v_bs_2795_){
_start:
{
size_t v_sz_boxed_2796_; size_t v_i_boxed_2797_; lean_object* v_res_2798_; 
v_sz_boxed_2796_ = lean_unbox_usize(v_sz_2793_);
lean_dec(v_sz_2793_);
v_i_boxed_2797_ = lean_unbox_usize(v_i_2794_);
lean_dec(v_i_2794_);
v_res_2798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_boxed_2796_, v_i_boxed_2797_, v_bs_2795_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object* v_subAlts_2799_, lean_object* v_arrowTk_2800_, lean_object* v_rhs_2801_, uint8_t v_isComplex_2802_){
_start:
{
uint8_t v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; uint8_t v___y_2846_; uint8_t v___x_2860_; 
v___x_2860_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_arrowTk_2800_);
if (v___x_2860_ == 0)
{
v___y_2846_ = v___x_2860_;
goto v___jp_2845_;
}
else
{
uint8_t v___x_2861_; 
v___x_2861_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_2801_);
if (v___x_2861_ == 0)
{
v___y_2846_ = v___x_2861_;
goto v___jp_2845_;
}
else
{
lean_object* v_subAlts_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec_ref(v_rhs_2801_);
lean_dec_ref(v_arrowTk_2800_);
v_subAlts_2862_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_2802_, v_subAlts_2799_);
lean_dec_ref(v_subAlts_2799_);
lean_inc_ref(v_subAlts_2862_);
v___x_2863_ = l_Lean_Fmt_TaggedDoc_flattened(v_subAlts_2862_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v_subAlts_2862_);
return v___x_2864_;
}
}
v___jp_2803_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v_lhs_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v_nonStickyDoc_2822_; lean_object* v_flat_2823_; lean_object* v___x_2824_; 
v___x_2807_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_2802_, v___y_2806_);
lean_dec_ref(v___y_2806_);
v___x_2808_ = lean_unsigned_to_nat(2u);
v___x_2809_ = lean_mk_empty_array_with_capacity(v___x_2808_);
lean_inc_ref_n(v___x_2809_, 2);
v___x_2810_ = lean_array_push(v___x_2809_, v___x_2807_);
v___x_2811_ = lean_array_push(v___x_2810_, v_arrowTk_2800_);
v_lhs_2812_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2811_);
lean_dec_ref(v___x_2811_);
v___x_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2813_, 0, v_lhs_2812_);
v___x_2814_ = l_Lean_Fmt_TaggedDoc_nl;
lean_inc_ref(v___y_2805_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v___y_2805_);
lean_inc_ref(v___x_2813_);
v___x_2816_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2813_, v___x_2815_);
v___x_2817_ = lean_box(0);
lean_inc_ref(v_rhs_2801_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_rhs_2801_);
v___x_2819_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
lean_ctor_set(v___x_2819_, 2, v___x_2817_);
v___x_2820_ = lean_array_push(v___x_2809_, v___x_2816_);
v___x_2821_ = lean_array_push(v___x_2820_, v___x_2819_);
v_nonStickyDoc_2822_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2821_);
lean_dec_ref(v___x_2821_);
lean_inc_ref(v_nonStickyDoc_2822_);
v_flat_2823_ = l_Lean_Fmt_TaggedDoc_flattened(v_nonStickyDoc_2822_);
v___x_2824_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_2801_);
if (lean_obj_tag(v___x_2824_) == 1)
{
lean_object* v_val_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2843_; 
v_val_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2843_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_val_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2843_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v_stickyVariant_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v_stickyVariant_2829_ = lean_ctor_get(v_val_2825_, 0);
v___x_2830_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v___y_2805_);
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___y_2805_);
v___x_2832_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2813_, v___x_2831_);
lean_inc_ref(v_stickyVariant_2829_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v_stickyVariant_2829_);
v___x_2834_ = v___x_2827_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_stickyVariant_2829_);
v___x_2834_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v_stickyDoc_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2817_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
lean_ctor_set(v___x_2835_, 2, v___x_2817_);
v___x_2836_ = lean_array_push(v___x_2809_, v___x_2832_);
v___x_2837_ = lean_array_push(v___x_2836_, v___x_2835_);
v_stickyDoc_2838_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2837_);
lean_dec_ref(v___x_2837_);
v___x_2839_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_2825_, v___y_2804_);
lean_dec(v_val_2825_);
v___x_2840_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_2822_, v_stickyDoc_2838_, v___x_2839_);
lean_dec(v___x_2839_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v_flat_2823_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
return v___x_2841_;
}
}
}
else
{
lean_object* v___x_2844_; 
lean_dec(v___x_2824_);
lean_dec_ref_known(v___x_2813_, 1);
lean_dec_ref(v___x_2809_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v_flat_2823_);
lean_ctor_set(v___x_2844_, 1, v_nonStickyDoc_2822_);
return v___x_2844_;
}
}
v___jp_2845_:
{
lean_object* v___x_2847_; size_t v_sz_2848_; size_t v___x_2849_; lean_object* v_subAlts_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v___x_2847_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_sz_2848_ = lean_array_size(v_subAlts_2799_);
v___x_2849_ = ((size_t)0ULL);
v_subAlts_2850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_2848_, v___x_2849_, v_subAlts_2799_);
v___x_2851_ = lean_array_get_size(v_subAlts_2850_);
v___x_2852_ = lean_unsigned_to_nat(1u);
v___x_2853_ = lean_nat_sub(v___x_2851_, v___x_2852_);
v___x_2854_ = lean_nat_dec_lt(v___x_2853_, v___x_2851_);
if (v___x_2854_ == 0)
{
lean_dec(v___x_2853_);
v___y_2804_ = v___y_2846_;
v___y_2805_ = v___x_2847_;
v___y_2806_ = v_subAlts_2850_;
goto v___jp_2803_;
}
else
{
lean_object* v_v_2855_; lean_object* v___x_2856_; lean_object* v_xs_x27_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_v_2855_ = lean_array_fget(v_subAlts_2850_, v___x_2853_);
v___x_2856_ = lean_box(0);
v_xs_x27_2857_ = lean_array_fset(v_subAlts_2850_, v___x_2853_, v___x_2856_);
v___x_2858_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2855_);
v___x_2859_ = lean_array_fset(v_xs_x27_2857_, v___x_2853_, v___x_2858_);
lean_dec(v___x_2853_);
v___y_2804_ = v___y_2846_;
v___y_2805_ = v___x_2847_;
v___y_2806_ = v___x_2859_;
goto v___jp_2803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt___boxed(lean_object* v_subAlts_2865_, lean_object* v_arrowTk_2866_, lean_object* v_rhs_2867_, lean_object* v_isComplex_2868_){
_start:
{
uint8_t v_isComplex_boxed_2869_; lean_object* v_res_2870_; 
v_isComplex_boxed_2869_ = lean_unbox(v_isComplex_2868_);
v_res_2870_ = l_Lean_Fmt_Layouts_alt(v_subAlts_2865_, v_arrowTk_2866_, v_rhs_2867_, v_isComplex_boxed_2869_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(size_t v_sz_2871_, size_t v_i_2872_, lean_object* v_bs_2873_){
_start:
{
uint8_t v___x_2874_; 
v___x_2874_ = lean_usize_dec_lt(v_i_2872_, v_sz_2871_);
if (v___x_2874_ == 0)
{
return v_bs_2873_;
}
else
{
lean_object* v_v_2875_; lean_object* v_flat_2876_; lean_object* v___x_2877_; lean_object* v_bs_x27_2878_; size_t v___x_2879_; size_t v___x_2880_; lean_object* v___x_2881_; 
v_v_2875_ = lean_array_uget_borrowed(v_bs_2873_, v_i_2872_);
v_flat_2876_ = lean_ctor_get(v_v_2875_, 0);
lean_inc_ref(v_flat_2876_);
v___x_2877_ = lean_unsigned_to_nat(0u);
v_bs_x27_2878_ = lean_array_uset(v_bs_2873_, v_i_2872_, v___x_2877_);
v___x_2879_ = ((size_t)1ULL);
v___x_2880_ = lean_usize_add(v_i_2872_, v___x_2879_);
v___x_2881_ = lean_array_uset(v_bs_x27_2878_, v_i_2872_, v_flat_2876_);
v_i_2872_ = v___x_2880_;
v_bs_2873_ = v___x_2881_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object* v_sz_2883_, lean_object* v_i_2884_, lean_object* v_bs_2885_){
_start:
{
size_t v_sz_boxed_2886_; size_t v_i_boxed_2887_; lean_object* v_res_2888_; 
v_sz_boxed_2886_ = lean_unbox_usize(v_sz_2883_);
lean_dec(v_sz_2883_);
v_i_boxed_2887_ = lean_unbox_usize(v_i_2884_);
lean_dec(v_i_2884_);
v_res_2888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_boxed_2886_, v_i_boxed_2887_, v_bs_2885_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t v_sz_2889_, size_t v_i_2890_, lean_object* v_bs_2891_){
_start:
{
uint8_t v___x_2892_; 
v___x_2892_ = lean_usize_dec_lt(v_i_2890_, v_sz_2889_);
if (v___x_2892_ == 0)
{
return v_bs_2891_;
}
else
{
lean_object* v_v_2893_; lean_object* v_nonFlat_2894_; lean_object* v___x_2895_; lean_object* v_bs_x27_2896_; size_t v___x_2897_; size_t v___x_2898_; lean_object* v___x_2899_; 
v_v_2893_ = lean_array_uget_borrowed(v_bs_2891_, v_i_2890_);
v_nonFlat_2894_ = lean_ctor_get(v_v_2893_, 1);
lean_inc_ref(v_nonFlat_2894_);
v___x_2895_ = lean_unsigned_to_nat(0u);
v_bs_x27_2896_ = lean_array_uset(v_bs_2891_, v_i_2890_, v___x_2895_);
v___x_2897_ = ((size_t)1ULL);
v___x_2898_ = lean_usize_add(v_i_2890_, v___x_2897_);
v___x_2899_ = lean_array_uset(v_bs_x27_2896_, v_i_2890_, v_nonFlat_2894_);
v_i_2890_ = v___x_2898_;
v_bs_2891_ = v___x_2899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object* v_sz_2901_, lean_object* v_i_2902_, lean_object* v_bs_2903_){
_start:
{
size_t v_sz_boxed_2904_; size_t v_i_boxed_2905_; lean_object* v_res_2906_; 
v_sz_boxed_2904_ = lean_unbox_usize(v_sz_2901_);
lean_dec(v_sz_2901_);
v_i_boxed_2905_ = lean_unbox_usize(v_i_2902_);
lean_dec(v_i_2902_);
v_res_2906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_boxed_2904_, v_i_boxed_2905_, v_bs_2903_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts(lean_object* v_alts_2907_, uint8_t v_allowFlattenedAlts_2908_){
_start:
{
size_t v_sz_2909_; size_t v___x_2910_; lean_object* v___x_2911_; lean_object* v_unflattened_2912_; 
v_sz_2909_ = lean_array_size(v_alts_2907_);
v___x_2910_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2907_);
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_2909_, v___x_2910_, v_alts_2907_);
v_unflattened_2912_ = l_Lean_Fmt_Layouts_lines(v___x_2911_);
lean_dec_ref(v___x_2911_);
if (v_allowFlattenedAlts_2908_ == 0)
{
lean_object* v___x_2913_; 
lean_dec_ref(v_alts_2907_);
v___x_2913_ = l_Lean_Fmt_TaggedDoc_withPosition(v_unflattened_2912_);
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; lean_object* v_flattened_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_2909_, v___x_2910_, v_alts_2907_);
v_flattened_2915_ = l_Lean_Fmt_Layouts_lines(v___x_2914_);
lean_dec_ref(v___x_2914_);
v___x_2916_ = lean_unsigned_to_nat(2u);
v___x_2917_ = lean_mk_empty_array_with_capacity(v___x_2916_);
v___x_2918_ = lean_array_push(v___x_2917_, v_flattened_2915_);
v___x_2919_ = lean_array_push(v___x_2918_, v_unflattened_2912_);
v___x_2920_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2919_);
v___x_2921_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_2920_);
return v___x_2921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts___boxed(lean_object* v_alts_2922_, lean_object* v_allowFlattenedAlts_2923_){
_start:
{
uint8_t v_allowFlattenedAlts_boxed_2924_; lean_object* v_res_2925_; 
v_allowFlattenedAlts_boxed_2924_ = lean_unbox(v_allowFlattenedAlts_2923_);
v_res_2925_ = l_Lean_Fmt_Layouts_alts(v_alts_2922_, v_allowFlattenedAlts_boxed_2924_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl(uint8_t v_x_2926_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_box(v_x_2926_);
v___x_2928_ = lean_obj_tag_nat(v___x_2927_);
lean_dec(v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl___boxed(lean_object* v_x_2929_){
_start:
{
uint8_t v_x_4__boxed_2930_; lean_object* v_res_2931_; 
v_x_4__boxed_2930_ = lean_unbox(v_x_2929_);
v_res_2931_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___impl(v_x_4__boxed_2930_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(lean_object* v_k_2932_){
_start:
{
lean_inc(v_k_2932_);
return v_k_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg___boxed(lean_object* v_k_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(v_k_2933_);
lean_dec(v_k_2933_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(lean_object* v_motive_2935_, lean_object* v_ctorIdx_2936_, uint8_t v_t_2937_, lean_object* v_h_2938_, lean_object* v_k_2939_){
_start:
{
lean_inc(v_k_2939_);
return v_k_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___boxed(lean_object* v_motive_2940_, lean_object* v_ctorIdx_2941_, lean_object* v_t_2942_, lean_object* v_h_2943_, lean_object* v_k_2944_){
_start:
{
uint8_t v_t_boxed_2945_; lean_object* v_res_2946_; 
v_t_boxed_2945_ = lean_unbox(v_t_2942_);
v_res_2946_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(v_motive_2940_, v_ctorIdx_2941_, v_t_boxed_2945_, v_h_2943_, v_k_2944_);
lean_dec(v_k_2944_);
lean_dec(v_ctorIdx_2941_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(lean_object* v_sticky_2947_){
_start:
{
lean_inc(v_sticky_2947_);
return v_sticky_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(v_sticky_2948_);
lean_dec(v_sticky_2948_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(lean_object* v_motive_2950_, uint8_t v_t_2951_, lean_object* v_h_2952_, lean_object* v_sticky_2953_){
_start:
{
lean_inc(v_sticky_2953_);
return v_sticky_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___boxed(lean_object* v_motive_2954_, lean_object* v_t_2955_, lean_object* v_h_2956_, lean_object* v_sticky_2957_){
_start:
{
uint8_t v_t_boxed_2958_; lean_object* v_res_2959_; 
v_t_boxed_2958_ = lean_unbox(v_t_2955_);
v_res_2959_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(v_motive_2954_, v_t_boxed_2958_, v_h_2956_, v_sticky_2957_);
lean_dec(v_sticky_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_2960_){
_start:
{
lean_inc(v_nonSticky_2960_);
return v_nonSticky_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(v_nonSticky_2961_);
lean_dec(v_nonSticky_2961_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(lean_object* v_motive_2963_, uint8_t v_t_2964_, lean_object* v_h_2965_, lean_object* v_nonSticky_2966_){
_start:
{
lean_inc(v_nonSticky_2966_);
return v_nonSticky_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___boxed(lean_object* v_motive_2967_, lean_object* v_t_2968_, lean_object* v_h_2969_, lean_object* v_nonSticky_2970_){
_start:
{
uint8_t v_t_boxed_2971_; lean_object* v_res_2972_; 
v_t_boxed_2971_ = lean_unbox(v_t_2968_);
v_res_2972_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(v_motive_2967_, v_t_boxed_2971_, v_h_2969_, v_nonSticky_2970_);
lean_dec(v_nonSticky_2970_);
return v_res_2972_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0(void){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_2974_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
lean_ctor_set(v___x_2975_, 1, v___x_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object* v_keywordTk_2976_, lean_object* v_seq_2977_, uint8_t v_format_2978_){
_start:
{
lean_object* v___x_2979_; uint8_t v___x_2980_; lean_object* v_doc_2981_; 
v___x_2979_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_2980_ = 1;
v_doc_2981_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_keywordTk_2976_, v___x_2979_, v_seq_2977_, v___x_2980_);
if (v_format_2978_ == 0)
{
lean_object* v___x_2982_; uint8_t v___x_2983_; lean_object* v___x_2984_; 
lean_inc_ref(v_doc_2981_);
v___x_2982_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_2981_);
v___x_2983_ = 1;
v___x_2984_ = l_Lean_Fmt_TaggedDoc_sticky(v___x_2982_, v_doc_2981_, v___x_2983_);
return v___x_2984_;
}
else
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_2981_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___boxed(lean_object* v_keywordTk_2986_, lean_object* v_seq_2987_, lean_object* v_format_2988_){
_start:
{
uint8_t v_format_boxed_2989_; lean_object* v_res_2990_; 
v_format_boxed_2989_ = lean_unbox(v_format_2988_);
v_res_2990_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_keywordTk_2986_, v_seq_2987_, v_format_boxed_2989_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl(uint8_t v_x_2991_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_box(v_x_2991_);
v___x_2993_ = lean_obj_tag_nat(v___x_2992_);
lean_dec(v___x_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl___boxed(lean_object* v_x_2994_){
_start:
{
uint8_t v_x_4__boxed_2995_; lean_object* v_res_2996_; 
v_x_4__boxed_2995_ = lean_unbox(v_x_2994_);
v_res_2996_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___impl(v_x_4__boxed_2995_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(lean_object* v_k_2997_){
_start:
{
lean_inc(v_k_2997_);
return v_k_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg___boxed(lean_object* v_k_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(v_k_2998_);
lean_dec(v_k_2998_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(lean_object* v_motive_3000_, lean_object* v_ctorIdx_3001_, uint8_t v_t_3002_, lean_object* v_h_3003_, lean_object* v_k_3004_){
_start:
{
lean_inc(v_k_3004_);
return v_k_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___boxed(lean_object* v_motive_3005_, lean_object* v_ctorIdx_3006_, lean_object* v_t_3007_, lean_object* v_h_3008_, lean_object* v_k_3009_){
_start:
{
uint8_t v_t_boxed_3010_; lean_object* v_res_3011_; 
v_t_boxed_3010_ = lean_unbox(v_t_3007_);
v_res_3011_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(v_motive_3005_, v_ctorIdx_3006_, v_t_boxed_3010_, v_h_3008_, v_k_3009_);
lean_dec(v_k_3009_);
lean_dec(v_ctorIdx_3006_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(lean_object* v_sticky_3012_){
_start:
{
lean_inc(v_sticky_3012_);
return v_sticky_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(v_sticky_3013_);
lean_dec(v_sticky_3013_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(lean_object* v_motive_3015_, uint8_t v_t_3016_, lean_object* v_h_3017_, lean_object* v_sticky_3018_){
_start:
{
lean_inc(v_sticky_3018_);
return v_sticky_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___boxed(lean_object* v_motive_3019_, lean_object* v_t_3020_, lean_object* v_h_3021_, lean_object* v_sticky_3022_){
_start:
{
uint8_t v_t_boxed_3023_; lean_object* v_res_3024_; 
v_t_boxed_3023_ = lean_unbox(v_t_3020_);
v_res_3024_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(v_motive_3019_, v_t_boxed_3023_, v_h_3021_, v_sticky_3022_);
lean_dec(v_sticky_3022_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3025_){
_start:
{
lean_inc(v_nonSticky_3025_);
return v_nonSticky_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(v_nonSticky_3026_);
lean_dec(v_nonSticky_3026_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(lean_object* v_motive_3028_, uint8_t v_t_3029_, lean_object* v_h_3030_, lean_object* v_nonSticky_3031_){
_start:
{
lean_inc(v_nonSticky_3031_);
return v_nonSticky_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___boxed(lean_object* v_motive_3032_, lean_object* v_t_3033_, lean_object* v_h_3034_, lean_object* v_nonSticky_3035_){
_start:
{
uint8_t v_t_boxed_3036_; lean_object* v_res_3037_; 
v_t_boxed_3036_ = lean_unbox(v_t_3033_);
v_res_3037_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(v_motive_3032_, v_t_boxed_3036_, v_h_3034_, v_nonSticky_3035_);
lean_dec(v_nonSticky_3035_);
return v_res_3037_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3039_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3038_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object* v_keyword_3041_, lean_object* v_term_3042_, uint8_t v_format_3043_){
_start:
{
uint8_t v___x_3044_; 
v___x_3044_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_term_3042_);
if (v___x_3044_ == 0)
{
uint8_t v___x_3045_; lean_object* v___y_3047_; uint8_t v___x_3079_; 
v___x_3045_ = 1;
lean_inc_ref(v_term_3042_);
v___x_3079_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_term_3042_, v___x_3044_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_inc_ref(v_keyword_3041_);
v___x_3080_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3041_);
v___x_3081_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_term_3042_);
v___x_3082_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3080_, v___x_3081_, v_term_3042_, v___x_3045_);
v___x_3083_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3082_);
v___y_3047_ = v___x_3083_;
goto v___jp_3046_;
}
else
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
lean_inc_ref(v_keyword_3041_);
v___x_3084_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3041_);
v___x_3085_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v_term_3042_);
v___x_3086_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3084_, v___x_3085_, v_term_3042_, v___x_3045_);
v___y_3047_ = v___x_3086_;
goto v___jp_3046_;
}
v___jp_3046_:
{
if (v_format_3043_ == 0)
{
lean_object* v___x_3048_; 
lean_inc_ref(v_term_3042_);
v___x_3048_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_term_3042_);
if (lean_obj_tag(v___x_3048_) == 1)
{
lean_object* v_val_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3073_; 
v_val_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3073_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_val_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3073_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
uint8_t v_kind_3053_; 
v_kind_3053_ = lean_ctor_get_uint8(v_val_3049_, sizeof(void*)*1);
lean_dec(v_val_3049_);
if (v_kind_3053_ == 1)
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3041_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3054_);
v___x_3056_ = v___x_3051_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3057_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3058_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3056_, v___x_3057_);
v___x_3059_ = lean_box(0);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v_term_3042_);
v___x_3061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
lean_ctor_set(v___x_3061_, 2, v___x_3059_);
v___x_3062_ = lean_unsigned_to_nat(2u);
v___x_3063_ = lean_mk_empty_array_with_capacity(v___x_3062_);
v___x_3064_ = lean_array_push(v___x_3063_, v___x_3058_);
v___x_3065_ = lean_array_push(v___x_3064_, v___x_3061_);
v___x_3066_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3065_);
lean_dec_ref(v___x_3065_);
v___x_3067_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3047_, v___x_3066_, v_kind_3053_);
return v___x_3067_;
}
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_del_object(v___x_3051_);
v___x_3069_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3041_);
v___x_3070_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3071_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3069_, v___x_3070_, v_term_3042_, v___x_3045_);
v___x_3072_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3047_, v___x_3071_, v_kind_3053_);
return v___x_3072_;
}
}
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; 
lean_dec(v___x_3048_);
v___x_3074_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3041_);
v___x_3075_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3076_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3074_, v___x_3075_, v_term_3042_, v___x_3045_);
v___x_3077_ = 0;
v___x_3078_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3047_, v___x_3076_, v___x_3077_);
return v___x_3078_;
}
}
else
{
lean_dec_ref(v_term_3042_);
lean_dec_ref(v_keyword_3041_);
return v___y_3047_;
}
}
}
else
{
uint8_t v___x_3087_; 
lean_dec_ref(v_term_3042_);
v___x_3087_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keyword_3041_);
if (v___x_3087_ == 0)
{
if (v_format_3043_ == 0)
{
lean_object* v___x_3088_; uint8_t v___x_3089_; lean_object* v___x_3090_; 
lean_inc_ref(v_keyword_3041_);
v___x_3088_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3041_);
v___x_3089_ = 0;
v___x_3090_ = l_Lean_Fmt_TaggedDoc_sticky(v_keyword_3041_, v___x_3088_, v___x_3089_);
return v___x_3090_;
}
else
{
return v_keyword_3041_;
}
}
else
{
lean_object* v___x_3091_; 
lean_dec_ref(v_keyword_3041_);
v___x_3091_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___boxed(lean_object* v_keyword_3092_, lean_object* v_term_3093_, lean_object* v_format_3094_){
_start:
{
uint8_t v_format_boxed_3095_; lean_object* v_res_3096_; 
v_format_boxed_3095_ = lean_unbox(v_format_3094_);
v_res_3096_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3092_, v_term_3093_, v_format_boxed_3095_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl(uint8_t v_x_3097_){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = lean_box(v_x_3097_);
v___x_3099_ = lean_obj_tag_nat(v___x_3098_);
lean_dec(v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl___boxed(lean_object* v_x_3100_){
_start:
{
uint8_t v_x_4__boxed_3101_; lean_object* v_res_3102_; 
v_x_4__boxed_3101_ = lean_unbox(v_x_3100_);
v_res_3102_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___impl(v_x_4__boxed_3101_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(lean_object* v_k_3103_){
_start:
{
lean_inc(v_k_3103_);
return v_k_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg___boxed(lean_object* v_k_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(v_k_3104_);
lean_dec(v_k_3104_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(lean_object* v_motive_3106_, lean_object* v_ctorIdx_3107_, uint8_t v_t_3108_, lean_object* v_h_3109_, lean_object* v_k_3110_){
_start:
{
lean_inc(v_k_3110_);
return v_k_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___boxed(lean_object* v_motive_3111_, lean_object* v_ctorIdx_3112_, lean_object* v_t_3113_, lean_object* v_h_3114_, lean_object* v_k_3115_){
_start:
{
uint8_t v_t_boxed_3116_; lean_object* v_res_3117_; 
v_t_boxed_3116_ = lean_unbox(v_t_3113_);
v_res_3117_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(v_motive_3111_, v_ctorIdx_3112_, v_t_boxed_3116_, v_h_3114_, v_k_3115_);
lean_dec(v_k_3115_);
lean_dec(v_ctorIdx_3112_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(lean_object* v_sticky_3118_){
_start:
{
lean_inc(v_sticky_3118_);
return v_sticky_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(v_sticky_3119_);
lean_dec(v_sticky_3119_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(lean_object* v_motive_3121_, uint8_t v_t_3122_, lean_object* v_h_3123_, lean_object* v_sticky_3124_){
_start:
{
lean_inc(v_sticky_3124_);
return v_sticky_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___boxed(lean_object* v_motive_3125_, lean_object* v_t_3126_, lean_object* v_h_3127_, lean_object* v_sticky_3128_){
_start:
{
uint8_t v_t_boxed_3129_; lean_object* v_res_3130_; 
v_t_boxed_3129_ = lean_unbox(v_t_3126_);
v_res_3130_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(v_motive_3125_, v_t_boxed_3129_, v_h_3127_, v_sticky_3128_);
lean_dec(v_sticky_3128_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3131_){
_start:
{
lean_inc(v_nonSticky_3131_);
return v_nonSticky_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(v_nonSticky_3132_);
lean_dec(v_nonSticky_3132_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(lean_object* v_motive_3134_, uint8_t v_t_3135_, lean_object* v_h_3136_, lean_object* v_nonSticky_3137_){
_start:
{
lean_inc(v_nonSticky_3137_);
return v_nonSticky_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___boxed(lean_object* v_motive_3138_, lean_object* v_t_3139_, lean_object* v_h_3140_, lean_object* v_nonSticky_3141_){
_start:
{
uint8_t v_t_boxed_3142_; lean_object* v_res_3143_; 
v_t_boxed_3142_ = lean_unbox(v_t_3139_);
v_res_3143_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(v_motive_3138_, v_t_boxed_3142_, v_h_3140_, v_nonSticky_3141_);
lean_dec(v_nonSticky_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object* v_keyword_3144_, lean_object* v_alts_3145_, uint8_t v_format_3146_){
_start:
{
uint8_t v___x_3147_; lean_object* v_alts_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_nonStickyDoc_3153_; 
v___x_3147_ = 1;
v_alts_3148_ = l_Lean_Fmt_Layouts_alts(v_alts_3145_, v___x_3147_);
v___x_3149_ = lean_unsigned_to_nat(2u);
v___x_3150_ = lean_mk_empty_array_with_capacity(v___x_3149_);
lean_inc_ref(v_keyword_3144_);
lean_inc_ref(v___x_3150_);
v___x_3151_ = lean_array_push(v___x_3150_, v_keyword_3144_);
lean_inc_ref(v_alts_3148_);
v___x_3152_ = lean_array_push(v___x_3151_, v_alts_3148_);
v_nonStickyDoc_3153_ = l_Lean_Fmt_Layouts_lines(v___x_3152_);
lean_dec_ref(v___x_3152_);
if (v_format_3146_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v_stickyDoc_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3154_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3144_);
v___x_3155_ = lean_array_push(v___x_3150_, v___x_3154_);
v___x_3156_ = lean_array_push(v___x_3155_, v_alts_3148_);
v_stickyDoc_3157_ = l_Lean_Fmt_Layouts_lines(v___x_3156_);
lean_dec_ref(v___x_3156_);
v___x_3158_ = 0;
v___x_3159_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3153_, v_stickyDoc_3157_, v___x_3158_);
return v___x_3159_;
}
else
{
lean_dec_ref(v___x_3150_);
lean_dec_ref(v_alts_3148_);
lean_dec_ref(v_keyword_3144_);
return v_nonStickyDoc_3153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts___boxed(lean_object* v_keyword_3160_, lean_object* v_alts_3161_, lean_object* v_format_3162_){
_start:
{
uint8_t v_format_boxed_3163_; lean_object* v_res_3164_; 
v_format_boxed_3163_ = lean_unbox(v_format_3162_);
v_res_3164_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v_keyword_3160_, v_alts_3161_, v_format_boxed_3163_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl(lean_object* v_x_3165_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = lean_obj_tag_nat(v_x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl___boxed(lean_object* v_x_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___impl(v_x_3167_);
lean_dec_ref(v_x_3167_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(lean_object* v_t_3169_, lean_object* v_k_3170_){
_start:
{
lean_object* v_sepArrayFormat_3171_; lean_object* v___x_3172_; 
v_sepArrayFormat_3171_ = lean_ctor_get(v_t_3169_, 0);
lean_inc_ref(v_sepArrayFormat_3171_);
lean_dec_ref(v_t_3169_);
v___x_3172_ = lean_apply_1(v_k_3170_, v_sepArrayFormat_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(lean_object* v_motive_3173_, lean_object* v_ctorIdx_3174_, lean_object* v_t_3175_, lean_object* v_h_3176_, lean_object* v_k_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3175_, v_k_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___boxed(lean_object* v_motive_3179_, lean_object* v_ctorIdx_3180_, lean_object* v_t_3181_, lean_object* v_h_3182_, lean_object* v_k_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(v_motive_3179_, v_ctorIdx_3180_, v_t_3181_, v_h_3182_, v_k_3183_);
lean_dec(v_ctorIdx_3180_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim___redArg(lean_object* v_t_3185_, lean_object* v_sticky_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3185_, v_sticky_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim(lean_object* v_motive_3188_, lean_object* v_t_3189_, lean_object* v_h_3190_, lean_object* v_sticky_3191_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3189_, v_sticky_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim___redArg(lean_object* v_t_3193_, lean_object* v_nonSticky_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3193_, v_nonSticky_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim(lean_object* v_motive_3196_, lean_object* v_t_3197_, lean_object* v_h_3198_, lean_object* v_nonSticky_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3197_, v_nonSticky_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(lean_object* v_x_3201_){
_start:
{
if (lean_obj_tag(v_x_3201_) == 0)
{
uint8_t v___x_3202_; 
v___x_3202_ = 1;
return v___x_3202_;
}
else
{
uint8_t v___x_3203_; 
v___x_3203_ = 0;
return v___x_3203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky___boxed(lean_object* v_x_3204_){
_start:
{
uint8_t v_res_3205_; lean_object* v_r_3206_; 
v_res_3205_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_x_3204_);
lean_dec_ref(v_x_3204_);
v_r_3206_ = lean_box(v_res_3205_);
return v_r_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(lean_object* v_x_3207_){
_start:
{
lean_object* v_sepArrayFormat_3208_; 
v_sepArrayFormat_3208_ = lean_ctor_get(v_x_3207_, 0);
lean_inc_ref(v_sepArrayFormat_3208_);
return v_sepArrayFormat_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat___boxed(lean_object* v_x_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(v_x_3209_);
lean_dec_ref(v_x_3209_);
return v_res_3210_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3212_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v___x_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray(lean_object* v_sep_3214_, lean_object* v_keyword_3215_, lean_object* v_sepArray_3216_, lean_object* v_format_3217_){
_start:
{
lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___x_3256_; lean_object* v___y_3258_; uint8_t v___y_3259_; lean_object* v___y_3264_; uint8_t v___y_3265_; lean_object* v___y_3281_; lean_object* v_sepArrayFormat_3285_; 
v___x_3256_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_sepArrayFormat_3285_ = lean_ctor_get(v_format_3217_, 0);
lean_inc_ref(v_sepArrayFormat_3285_);
v___y_3281_ = v_sepArrayFormat_3285_;
goto v___jp_3280_;
v___jp_3218_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v_nonStickyDoc_3245_; uint8_t v___x_3246_; 
lean_inc_ref(v_keyword_3215_);
v___x_3222_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3215_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
v___x_3224_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v___x_3223_);
v___x_3225_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3223_, v___x_3224_);
v___x_3226_ = lean_box(0);
lean_inc_ref(v___y_3219_);
lean_inc_ref(v_sep_3214_);
v___x_3227_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3214_, v___y_3221_, v___y_3219_);
lean_dec_ref(v___y_3221_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
v___x_3229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3226_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
lean_ctor_set(v___x_3229_, 2, v___x_3226_);
v___x_3230_ = lean_unsigned_to_nat(2u);
v___x_3231_ = lean_mk_empty_array_with_capacity(v___x_3230_);
lean_inc_ref_n(v___x_3231_, 3);
v___x_3232_ = lean_array_push(v___x_3231_, v___x_3225_);
v___x_3233_ = lean_array_push(v___x_3232_, v___x_3229_);
v___x_3234_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3233_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_3236_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3223_, v___x_3235_);
v___x_3237_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3214_, v___y_3220_, v___y_3219_);
lean_dec_ref(v___y_3220_);
v___x_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
v___x_3239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3226_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
lean_ctor_set(v___x_3239_, 2, v___x_3226_);
v___x_3240_ = lean_array_push(v___x_3231_, v___x_3236_);
lean_inc_ref(v___x_3239_);
v___x_3241_ = lean_array_push(v___x_3240_, v___x_3239_);
v___x_3242_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3241_);
lean_dec_ref(v___x_3241_);
v___x_3243_ = lean_array_push(v___x_3231_, v___x_3234_);
v___x_3244_ = lean_array_push(v___x_3243_, v___x_3242_);
v_nonStickyDoc_3245_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3244_);
v___x_3246_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3217_);
lean_dec_ref(v_format_3217_);
if (v___x_3246_ == 0)
{
lean_dec_ref_known(v___x_3239_, 3);
lean_dec_ref(v___x_3231_);
lean_dec_ref(v_keyword_3215_);
return v_nonStickyDoc_3245_;
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v_stickyDoc_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; 
v___x_3247_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3215_);
v___x_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3247_);
v___x_3249_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3250_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3248_, v___x_3249_);
v___x_3251_ = lean_array_push(v___x_3231_, v___x_3250_);
v___x_3252_ = lean_array_push(v___x_3251_, v___x_3239_);
v_stickyDoc_3253_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3252_);
lean_dec_ref(v___x_3252_);
v___x_3254_ = 0;
v___x_3255_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3245_, v_stickyDoc_3253_, v___x_3254_);
return v___x_3255_;
}
}
v___jp_3257_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = lean_unsigned_to_nat(0u);
v___x_3261_ = lean_array_get(v___x_3256_, v___y_3258_, v___x_3260_);
lean_dec_ref(v___y_3258_);
v___x_3262_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3215_, v___x_3261_, v___y_3259_);
return v___x_3262_;
}
v___jp_3263_:
{
lean_object* v_sepArray_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
lean_inc_ref(v_sep_3214_);
v_sepArray_3266_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_3214_, v_sepArray_3216_, v___y_3265_);
v___x_3267_ = lean_array_get_size(v_sepArray_3266_);
v___x_3268_ = lean_unsigned_to_nat(1u);
v___x_3269_ = lean_nat_dec_eq(v___x_3267_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = lean_unsigned_to_nat(0u);
v___x_3271_ = lean_nat_dec_lt(v___x_3270_, v___x_3267_);
if (v___x_3271_ == 0)
{
lean_inc_ref(v_sepArray_3266_);
v___y_3219_ = v___y_3264_;
v___y_3220_ = v_sepArray_3266_;
v___y_3221_ = v_sepArray_3266_;
goto v___jp_3218_;
}
else
{
lean_object* v_v_3272_; lean_object* v___x_3273_; lean_object* v_xs_x27_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_v_3272_ = lean_array_fget_borrowed(v_sepArray_3266_, v___x_3270_);
v___x_3273_ = lean_box(0);
lean_inc_ref(v_sepArray_3266_);
v_xs_x27_3274_ = lean_array_fset(v_sepArray_3266_, v___x_3270_, v___x_3273_);
lean_inc(v_v_3272_);
v___x_3275_ = l_Lean_Fmt_TaggedDoc_flattened(v_v_3272_);
v___x_3276_ = lean_array_fset(v_xs_x27_3274_, v___x_3270_, v___x_3275_);
v___y_3219_ = v___y_3264_;
v___y_3220_ = v_sepArray_3266_;
v___y_3221_ = v___x_3276_;
goto v___jp_3218_;
}
}
else
{
uint8_t v___x_3277_; 
lean_dec_ref(v___y_3264_);
lean_dec_ref(v_sep_3214_);
v___x_3277_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3217_);
lean_dec_ref(v_format_3217_);
if (v___x_3277_ == 0)
{
uint8_t v___x_3278_; 
v___x_3278_ = 1;
v___y_3258_ = v_sepArray_3266_;
v___y_3259_ = v___x_3278_;
goto v___jp_3257_;
}
else
{
uint8_t v___x_3279_; 
v___x_3279_ = 0;
v___y_3258_ = v_sepArray_3266_;
v___y_3259_ = v___x_3279_;
goto v___jp_3257_;
}
}
}
v___jp_3280_:
{
switch(lean_obj_tag(v___y_3281_))
{
case 1:
{
uint8_t v_trailingSep_3282_; 
v_trailingSep_3282_ = lean_ctor_get_uint8(v___y_3281_, sizeof(void*)*1 + 1);
v___y_3264_ = v___y_3281_;
v___y_3265_ = v_trailingSep_3282_;
goto v___jp_3263_;
}
case 3:
{
uint8_t v_trailingSep_3283_; 
v_trailingSep_3283_ = lean_ctor_get_uint8(v___y_3281_, sizeof(void*)*1);
v___y_3264_ = v___y_3281_;
v___y_3265_ = v_trailingSep_3283_;
goto v___jp_3263_;
}
default: 
{
uint8_t v_trailingSep_3284_; 
v_trailingSep_3284_ = lean_ctor_get_uint8(v___y_3281_, sizeof(void*)*2);
v___y_3264_ = v___y_3281_;
v___y_3265_ = v_trailingSep_3284_;
goto v___jp_3263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___boxed(lean_object* v_sep_3286_, lean_object* v_keyword_3287_, lean_object* v_sepArray_3288_, lean_object* v_format_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3286_, v_keyword_3287_, v_sepArray_3288_, v_format_3289_);
lean_dec_ref(v_sepArray_3288_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl(uint8_t v_x_3291_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_box(v_x_3291_);
v___x_3293_ = lean_obj_tag_nat(v___x_3292_);
lean_dec(v___x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl___boxed(lean_object* v_x_3294_){
_start:
{
uint8_t v_x_4__boxed_3295_; lean_object* v_res_3296_; 
v_x_4__boxed_3295_ = lean_unbox(v_x_3294_);
v_res_3296_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___impl(v_x_4__boxed_3295_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(lean_object* v_k_3297_){
_start:
{
lean_inc(v_k_3297_);
return v_k_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg___boxed(lean_object* v_k_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(v_k_3298_);
lean_dec(v_k_3298_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(lean_object* v_motive_3300_, lean_object* v_ctorIdx_3301_, uint8_t v_t_3302_, lean_object* v_h_3303_, lean_object* v_k_3304_){
_start:
{
lean_inc(v_k_3304_);
return v_k_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___boxed(lean_object* v_motive_3305_, lean_object* v_ctorIdx_3306_, lean_object* v_t_3307_, lean_object* v_h_3308_, lean_object* v_k_3309_){
_start:
{
uint8_t v_t_boxed_3310_; lean_object* v_res_3311_; 
v_t_boxed_3310_ = lean_unbox(v_t_3307_);
v_res_3311_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(v_motive_3305_, v_ctorIdx_3306_, v_t_boxed_3310_, v_h_3308_, v_k_3309_);
lean_dec(v_k_3309_);
lean_dec(v_ctorIdx_3306_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(lean_object* v_sticky_3312_){
_start:
{
lean_inc(v_sticky_3312_);
return v_sticky_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(v_sticky_3313_);
lean_dec(v_sticky_3313_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(lean_object* v_motive_3315_, uint8_t v_t_3316_, lean_object* v_h_3317_, lean_object* v_sticky_3318_){
_start:
{
lean_inc(v_sticky_3318_);
return v_sticky_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___boxed(lean_object* v_motive_3319_, lean_object* v_t_3320_, lean_object* v_h_3321_, lean_object* v_sticky_3322_){
_start:
{
uint8_t v_t_boxed_3323_; lean_object* v_res_3324_; 
v_t_boxed_3323_ = lean_unbox(v_t_3320_);
v_res_3324_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(v_motive_3319_, v_t_boxed_3323_, v_h_3321_, v_sticky_3322_);
lean_dec(v_sticky_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3325_){
_start:
{
lean_inc(v_nonSticky_3325_);
return v_nonSticky_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(v_nonSticky_3326_);
lean_dec(v_nonSticky_3326_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(lean_object* v_motive_3328_, uint8_t v_t_3329_, lean_object* v_h_3330_, lean_object* v_nonSticky_3331_){
_start:
{
lean_inc(v_nonSticky_3331_);
return v_nonSticky_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___boxed(lean_object* v_motive_3332_, lean_object* v_t_3333_, lean_object* v_h_3334_, lean_object* v_nonSticky_3335_){
_start:
{
uint8_t v_t_boxed_3336_; lean_object* v_res_3337_; 
v_t_boxed_3336_ = lean_unbox(v_t_3333_);
v_res_3337_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(v_motive_3332_, v_t_boxed_3336_, v_h_3334_, v_nonSticky_3335_);
lean_dec(v_nonSticky_3335_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object* v_sep_3342_, lean_object* v_keyword_3343_, lean_object* v_sepArray_3344_, uint8_t v_format_3345_){
_start:
{
if (v_format_3345_ == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0));
v___x_3347_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3342_, v_keyword_3343_, v_sepArray_3344_, v___x_3346_);
return v___x_3347_;
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1));
v___x_3349_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3342_, v_keyword_3343_, v_sepArray_3344_, v___x_3348_);
return v___x_3349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___boxed(lean_object* v_sep_3350_, lean_object* v_keyword_3351_, lean_object* v_sepArray_3352_, lean_object* v_format_3353_){
_start:
{
uint8_t v_format_boxed_3354_; lean_object* v_res_3355_; 
v_format_boxed_3354_ = lean_unbox(v_format_3353_);
v_res_3355_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v_sep_3350_, v_keyword_3351_, v_sepArray_3352_, v_format_boxed_3354_);
lean_dec_ref(v_sepArray_3352_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(lean_object* v_format_3356_, lean_object* v_a_3357_){
_start:
{
uint8_t v_nestedRhs_3358_; 
v_nestedRhs_3358_ = lean_ctor_get_uint8(v_format_3356_, 1);
if (v_nestedRhs_3358_ == 0)
{
return v_a_3357_;
}
else
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lean_Fmt_TaggedDoc_nested(v_a_3357_);
return v___x_3359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed(lean_object* v_format_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(v_format_3360_, v_a_3361_);
lean_dec_ref(v_format_3360_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(lean_object* v_format_3363_){
_start:
{
uint8_t v_allowFlattening_3364_; 
v_allowFlattening_3364_ = lean_ctor_get_uint8(v_format_3363_, 0);
if (v_allowFlattening_3364_ == 0)
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Lean_Fmt_TaggedDoc_hardNl;
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Lean_Fmt_TaggedDoc_nl;
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep___boxed(lean_object* v_format_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3367_);
lean_dec_ref(v_format_3367_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(lean_object* v_rhs_3369_, lean_object* v_format_3370_, lean_object* v_lhs_3371_){
_start:
{
uint8_t v_allowFlattening_3372_; 
v_allowFlattening_3372_ = lean_ctor_get_uint8(v_format_3370_, 0);
if (v_allowFlattening_3372_ == 0)
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3373_, 0, v_lhs_3371_);
v___x_3374_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3370_);
v___x_3375_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3375_, 0, v_format_3370_);
v___x_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3373_, v___x_3376_);
v___x_3378_ = lean_box(0);
v___x_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_rhs_3369_);
v___x_3380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
lean_ctor_set(v___x_3380_, 2, v___x_3378_);
v___x_3381_ = lean_unsigned_to_nat(2u);
v___x_3382_ = lean_mk_empty_array_with_capacity(v___x_3381_);
v___x_3383_ = lean_array_push(v___x_3382_, v___x_3377_);
v___x_3384_ = lean_array_push(v___x_3383_, v___x_3380_);
v___x_3385_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3384_);
lean_dec_ref(v___x_3384_);
return v___x_3385_;
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3386_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3370_);
v___x_3387_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3387_, 0, v_format_3370_);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_3371_, v___x_3388_, v_rhs_3369_, v_allowFlattening_3372_);
return v___x_3389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object* v_lhs_3390_, lean_object* v_keywordTk_3391_, lean_object* v_rhs_3392_, lean_object* v_format_3393_){
_start:
{
lean_object* v___y_3395_; uint8_t v___x_3398_; 
v___x_3398_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keywordTk_3391_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v_trailingKeywordLhs_3403_; uint8_t v___x_3404_; 
v___x_3399_ = lean_unsigned_to_nat(2u);
v___x_3400_ = lean_mk_empty_array_with_capacity(v___x_3399_);
v___x_3401_ = lean_array_push(v___x_3400_, v_lhs_3390_);
v___x_3402_ = lean_array_push(v___x_3401_, v_keywordTk_3391_);
v_trailingKeywordLhs_3403_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3402_);
lean_dec_ref(v___x_3402_);
v___x_3404_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_3392_);
if (v___x_3404_ == 0)
{
uint8_t v_nestedRhs_3405_; 
v_nestedRhs_3405_ = lean_ctor_get_uint8(v_format_3393_, 1);
if (v_nestedRhs_3405_ == 0)
{
v___y_3395_ = v_trailingKeywordLhs_3403_;
goto v___jp_3394_;
}
else
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_Fmt_TaggedDoc_hardNested(v_trailingKeywordLhs_3403_);
v___y_3395_ = v___x_3406_;
goto v___jp_3394_;
}
}
else
{
v___y_3395_ = v_trailingKeywordLhs_3403_;
goto v___jp_3394_;
}
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
lean_dec_ref(v_keywordTk_3391_);
v___x_3407_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3392_, v_format_3393_, v_lhs_3390_);
v___x_3408_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3407_);
return v___x_3408_;
}
v___jp_3394_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3392_, v_format_3393_, v___y_3395_);
v___x_3397_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3396_);
return v___x_3397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0(lean_object* v___y_3409_){
_start:
{
lean_inc_ref(v___y_3409_);
return v___y_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0___boxed(lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___lam__0(v___y_3410_);
lean_dec_ref(v___y_3410_);
return v_res_3411_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1(void){
_start:
{
lean_object* v___f_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___f_3413_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0));
v___x_3414_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v___f_3413_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(lean_object* v_terms_3416_){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3417_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3418_ = lean_box(0);
v___x_3419_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v_terms_3416_);
v___x_3420_ = lean_array_pop(v_terms_3416_);
v___x_3421_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_3419_, v___x_3420_);
v___x_3422_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3421_);
v___x_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
v___x_3424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3418_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
lean_ctor_set(v___x_3424_, 2, v___x_3418_);
v___x_3425_ = lean_array_get_size(v_terms_3416_);
v___x_3426_ = lean_unsigned_to_nat(1u);
v___x_3427_ = lean_nat_sub(v___x_3425_, v___x_3426_);
v___x_3428_ = lean_array_get(v___x_3417_, v_terms_3416_, v___x_3427_);
lean_dec(v___x_3427_);
lean_dec_ref(v_terms_3416_);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
v___x_3430_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1);
v___x_3431_ = l_Lean_Fmt_TaggedDoc_Component_withSepBefore(v___x_3429_, v___x_3430_);
v___x_3432_ = lean_unsigned_to_nat(2u);
v___x_3433_ = lean_mk_empty_array_with_capacity(v___x_3432_);
v___x_3434_ = lean_array_push(v___x_3433_, v___x_3424_);
v___x_3435_ = lean_array_push(v___x_3434_, v___x_3431_);
v___x_3436_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3435_);
lean_dec_ref(v___x_3435_);
return v___x_3436_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3438_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(lean_object* v_app_3439_, lean_object* v_fillableTerms_3440_, lean_object* v_terms_3441_, lean_object* v_eligibleKinds_3442_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v_allowFill_3449_; 
v___x_3443_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3444_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3445_ = lean_array_get_size(v_fillableTerms_3440_);
v___x_3446_ = lean_unsigned_to_nat(1u);
v___x_3447_ = lean_nat_sub(v___x_3445_, v___x_3446_);
v___x_3448_ = lean_array_get_borrowed(v___x_3444_, v_fillableTerms_3440_, v___x_3447_);
lean_dec(v___x_3447_);
v_allowFill_3449_ = lean_ctor_get_uint8(v___x_3448_, sizeof(void*)*1);
if (v_allowFill_3449_ == 0)
{
lean_object* v___x_3450_; 
lean_dec_ref(v_terms_3441_);
lean_dec_ref(v_app_3439_);
v___x_3450_ = lean_box(0);
return v___x_3450_;
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3451_ = lean_array_get_size(v_terms_3441_);
v___x_3452_ = lean_nat_sub(v___x_3451_, v___x_3446_);
v___x_3453_ = lean_array_get_borrowed(v___x_3443_, v_terms_3441_, v___x_3452_);
lean_inc(v___x_3453_);
v___x_3454_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v___x_3453_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v___x_3455_; 
lean_dec(v___x_3452_);
lean_dec_ref(v_terms_3441_);
lean_dec_ref(v_app_3439_);
v___x_3455_ = lean_box(0);
return v___x_3455_;
}
else
{
lean_object* v_val_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3477_; 
v_val_3456_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3458_ = v___x_3454_;
v_isShared_3459_ = v_isSharedCheck_3477_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_val_3456_);
lean_dec(v___x_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3477_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
uint8_t v___x_3460_; uint8_t v___x_3461_; lean_object* v___y_3463_; 
v___x_3460_ = lean_unbox(v_val_3456_);
lean_dec(v_val_3456_);
v___x_3461_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_3442_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3472_; 
lean_del_object(v___x_3458_);
lean_dec(v___x_3452_);
lean_dec_ref(v_terms_3441_);
lean_dec_ref(v_app_3439_);
v___x_3472_ = lean_box(0);
return v___x_3472_;
}
else
{
lean_object* v___x_3473_; 
lean_inc(v___x_3453_);
v___x_3473_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v___x_3453_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_3475_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_3474_);
v___y_3463_ = v___x_3475_;
goto v___jp_3462_;
}
else
{
lean_object* v_val_3476_; 
v_val_3476_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_val_3476_);
lean_dec_ref_known(v___x_3473_, 1);
v___y_3463_ = v_val_3476_;
goto v___jp_3462_;
}
}
v___jp_3462_:
{
lean_object* v_stickyVariant_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
v_stickyVariant_3464_ = lean_ctor_get(v___y_3463_, 0);
lean_inc_ref(v_stickyVariant_3464_);
v___x_3465_ = lean_array_set(v_terms_3441_, v___x_3452_, v_stickyVariant_3464_);
lean_dec(v___x_3452_);
v___x_3466_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v___x_3465_);
v___x_3467_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_3463_, v___x_3461_);
lean_dec_ref(v___y_3463_);
v___x_3468_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_app_3439_, v___x_3466_, v___x_3467_);
lean_dec(v___x_3467_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3468_);
v___x_3470_ = v___x_3458_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___boxed(lean_object* v_app_3478_, lean_object* v_fillableTerms_3479_, lean_object* v_terms_3480_, lean_object* v_eligibleKinds_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3478_, v_fillableTerms_3479_, v_terms_3480_, v_eligibleKinds_3481_);
lean_dec_ref(v_eligibleKinds_3481_);
lean_dec_ref(v_fillableTerms_3479_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(lean_object* v_format_3483_, lean_object* v_app_3484_, lean_object* v_terms_3485_){
_start:
{
uint8_t v_sparse_3486_; 
v_sparse_3486_ = lean_ctor_get_uint8(v_format_3483_, 1);
if (v_sparse_3486_ == 0)
{
uint8_t v_respectPseudoAlignment_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_respectPseudoAlignment_3487_ = lean_ctor_get_uint8(v_format_3483_, 3);
v___x_3488_ = lean_array_get_size(v_terms_3485_);
v___x_3489_ = lean_unsigned_to_nat(2u);
v___x_3490_ = lean_nat_dec_eq(v___x_3488_, v___x_3489_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; 
lean_dec_ref(v_terms_3485_);
lean_dec_ref(v_app_3484_);
v___x_3491_ = lean_box(0);
return v___x_3491_;
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3492_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_nat_sub(v___x_3488_, v___x_3493_);
v___x_3495_ = lean_array_get_borrowed(v___x_3492_, v_terms_3485_, v___x_3494_);
lean_dec(v___x_3494_);
lean_inc(v___x_3495_);
v___x_3496_ = l_Lean_Fmt_Layouts_permitDenseLayout(v___x_3495_, v_respectPseudoAlignment_3487_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
lean_dec_ref(v_terms_3485_);
lean_dec_ref(v_app_3484_);
v___x_3497_ = lean_box(0);
return v___x_3497_;
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3498_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v_terms_3485_);
v___x_3499_ = lean_mk_empty_array_with_capacity(v___x_3489_);
v___x_3500_ = lean_array_push(v___x_3499_, v___x_3498_);
v___x_3501_ = lean_array_push(v___x_3500_, v_app_3484_);
v___x_3502_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3501_);
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
return v___x_3503_;
}
}
}
else
{
lean_object* v___x_3504_; 
lean_dec_ref(v_terms_3485_);
lean_dec_ref(v_app_3484_);
v___x_3504_ = lean_box(0);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f___boxed(lean_object* v_format_3505_, lean_object* v_app_3506_, lean_object* v_terms_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3505_, v_app_3506_, v_terms_3507_);
lean_dec_ref(v_format_3505_);
return v_res_3508_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0));
v___x_3511_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3510_);
return v___x_3511_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3512_; lean_object* v_lbTk_3513_; 
v___x_3512_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1);
v_lbTk_3513_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3512_);
return v_lbTk_3513_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3));
v___x_3516_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3515_);
return v___x_3516_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_3517_; lean_object* v_rbTk_3518_; 
v___x_3517_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4);
v_rbTk_3518_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3517_);
return v_rbTk_3518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(lean_object* v_upperBound_3519_, lean_object* v_a_3520_, lean_object* v_b_3521_){
_start:
{
lean_object* v_a_3523_; uint8_t v___x_3527_; 
v___x_3527_ = lean_nat_dec_lt(v_a_3520_, v_upperBound_3519_);
if (v___x_3527_ == 0)
{
lean_dec(v_a_3520_);
return v_b_3521_;
}
else
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_v_3530_; uint8_t v_allowFill_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3543_; 
v___x_3528_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3529_ = lean_array_get(v___x_3528_, v_b_3521_, v_a_3520_);
v_v_3530_ = lean_ctor_get(v___x_3529_, 0);
v_allowFill_3531_ = lean_ctor_get_uint8(v___x_3529_, sizeof(void*)*1);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3533_ = v___x_3529_;
v_isShared_3534_ = v_isSharedCheck_3543_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_v_3530_);
lean_dec(v___x_3529_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3543_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
uint8_t v___x_3535_; 
lean_inc(v_v_3530_);
v___x_3535_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_v_3530_);
if (v___x_3535_ == 0)
{
lean_del_object(v___x_3533_);
lean_dec(v_v_3530_);
v_a_3523_ = v_b_3521_;
goto v___jp_3522_;
}
else
{
lean_object* v_lbTk_3536_; lean_object* v_rbTk_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; 
v_lbTk_3536_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2);
v_rbTk_3537_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5);
v___x_3538_ = l_Lean_Fmt_Layouts_parens(v_lbTk_3536_, v_v_3530_, v_rbTk_3537_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3538_);
v___x_3540_ = v___x_3533_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3538_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, sizeof(void*)*1, v_allowFill_3531_);
v___x_3540_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___x_3541_; 
v___x_3541_ = lean_array_set(v_b_3521_, v_a_3520_, v___x_3540_);
v_a_3523_ = v___x_3541_;
goto v___jp_3522_;
}
}
}
}
v___jp_3522_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = lean_nat_add(v_a_3520_, v___x_3524_);
lean_dec(v_a_3520_);
v_a_3520_ = v___x_3525_;
v_b_3521_ = v_a_3523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___boxed(lean_object* v_upperBound_3544_, lean_object* v_a_3545_, lean_object* v_b_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3544_, v_a_3545_, v_b_3546_);
lean_dec(v_upperBound_3544_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(lean_object* v_as_3548_, size_t v_i_3549_, size_t v_stop_3550_, lean_object* v_b_3551_){
_start:
{
lean_object* v___y_3553_; uint8_t v___x_3557_; 
v___x_3557_ = lean_usize_dec_eq(v_i_3549_, v_stop_3550_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; lean_object* v_v_3559_; uint8_t v___x_3560_; 
v___x_3558_ = lean_array_uget_borrowed(v_as_3548_, v_i_3549_);
v_v_3559_ = lean_ctor_get(v___x_3558_, 0);
v___x_3560_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_inc(v___x_3558_);
v___x_3561_ = lean_array_push(v_b_3551_, v___x_3558_);
v___y_3553_ = v___x_3561_;
goto v___jp_3552_;
}
else
{
v___y_3553_ = v_b_3551_;
goto v___jp_3552_;
}
}
else
{
return v_b_3551_;
}
v___jp_3552_:
{
size_t v___x_3554_; size_t v___x_3555_; 
v___x_3554_ = ((size_t)1ULL);
v___x_3555_ = lean_usize_add(v_i_3549_, v___x_3554_);
v_i_3549_ = v___x_3555_;
v_b_3551_ = v___y_3553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2___boxed(lean_object* v_as_3562_, lean_object* v_i_3563_, lean_object* v_stop_3564_, lean_object* v_b_3565_){
_start:
{
size_t v_i_boxed_3566_; size_t v_stop_boxed_3567_; lean_object* v_res_3568_; 
v_i_boxed_3566_ = lean_unbox_usize(v_i_3563_);
lean_dec(v_i_3563_);
v_stop_boxed_3567_ = lean_unbox_usize(v_stop_3564_);
lean_dec(v_stop_3564_);
v_res_3568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_as_3562_, v_i_boxed_3566_, v_stop_boxed_3567_, v_b_3565_);
lean_dec_ref(v_as_3562_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(size_t v_sz_3569_, size_t v_i_3570_, lean_object* v_bs_3571_){
_start:
{
uint8_t v___x_3572_; 
v___x_3572_ = lean_usize_dec_lt(v_i_3570_, v_sz_3569_);
if (v___x_3572_ == 0)
{
return v_bs_3571_;
}
else
{
lean_object* v_v_3573_; lean_object* v_v_3574_; lean_object* v___x_3575_; lean_object* v_bs_x27_3576_; size_t v___x_3577_; size_t v___x_3578_; lean_object* v___x_3579_; 
v_v_3573_ = lean_array_uget_borrowed(v_bs_3571_, v_i_3570_);
v_v_3574_ = lean_ctor_get(v_v_3573_, 0);
lean_inc(v_v_3574_);
v___x_3575_ = lean_unsigned_to_nat(0u);
v_bs_x27_3576_ = lean_array_uset(v_bs_3571_, v_i_3570_, v___x_3575_);
v___x_3577_ = ((size_t)1ULL);
v___x_3578_ = lean_usize_add(v_i_3570_, v___x_3577_);
v___x_3579_ = lean_array_uset(v_bs_x27_3576_, v_i_3570_, v_v_3574_);
v_i_3570_ = v___x_3578_;
v_bs_3571_ = v___x_3579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0___boxed(lean_object* v_sz_3581_, lean_object* v_i_3582_, lean_object* v_bs_3583_){
_start:
{
size_t v_sz_boxed_3584_; size_t v_i_boxed_3585_; lean_object* v_res_3586_; 
v_sz_boxed_3584_ = lean_unbox_usize(v_sz_3581_);
lean_dec(v_sz_3581_);
v_i_boxed_3585_ = lean_unbox_usize(v_i_3582_);
lean_dec(v_i_3582_);
v_res_3586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_boxed_3584_, v_i_boxed_3585_, v_bs_3583_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object* v_terms_3589_, lean_object* v_format_3590_){
_start:
{
lean_object* v_app_3592_; lean_object* v_fillableTerms_3596_; lean_object* v___y_3610_; lean_object* v_fillableTerms_3611_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___y_3619_; lean_object* v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3616_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3617_ = lean_unsigned_to_nat(0u);
v___x_3644_ = lean_array_get_size(v_terms_3589_);
v___x_3645_ = ((lean_object*)(l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0));
v___x_3646_ = lean_nat_dec_lt(v___x_3617_, v___x_3644_);
if (v___x_3646_ == 0)
{
v___y_3619_ = v___x_3645_;
goto v___jp_3618_;
}
else
{
size_t v___x_3647_; size_t v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = ((size_t)0ULL);
v___x_3648_ = lean_usize_of_nat(v___x_3644_);
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3589_, v___x_3647_, v___x_3648_, v___x_3645_);
v___y_3619_ = v___x_3649_;
goto v___jp_3618_;
}
v___jp_3591_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = l_Lean_Fmt_TaggedDoc_nested(v_app_3592_);
v___x_3594_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3593_);
return v___x_3594_;
}
v___jp_3595_:
{
lean_object* v_app_3597_; size_t v_sz_3598_; size_t v___x_3599_; lean_object* v_terms_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
lean_inc_ref_n(v_fillableTerms_3596_, 2);
v_app_3597_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(v_fillableTerms_3596_);
v_sz_3598_ = lean_array_size(v_fillableTerms_3596_);
v___x_3599_ = ((size_t)0ULL);
v_terms_3600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_3598_, v___x_3599_, v_fillableTerms_3596_);
v___x_3601_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
lean_inc_ref(v_terms_3600_);
lean_inc_ref(v_app_3597_);
v___x_3602_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3597_, v_fillableTerms_3596_, v_terms_3600_, v___x_3601_);
if (lean_obj_tag(v___x_3602_) == 1)
{
lean_object* v_val_3603_; 
lean_dec_ref(v_terms_3600_);
lean_dec_ref(v_app_3597_);
lean_dec_ref(v_fillableTerms_3596_);
v_val_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_val_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v_app_3592_ = v_val_3603_;
goto v___jp_3591_;
}
else
{
lean_object* v___x_3604_; 
lean_dec(v___x_3602_);
lean_inc_ref(v_terms_3600_);
lean_inc_ref(v_app_3597_);
v___x_3604_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3590_, v_app_3597_, v_terms_3600_);
if (lean_obj_tag(v___x_3604_) == 1)
{
lean_object* v_val_3605_; 
lean_dec_ref(v_terms_3600_);
lean_dec_ref(v_app_3597_);
lean_dec_ref(v_fillableTerms_3596_);
v_val_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_val_3605_);
lean_dec_ref_known(v___x_3604_, 1);
v_app_3592_ = v_val_3605_;
goto v___jp_3591_;
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
lean_dec(v___x_3604_);
v___x_3606_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
lean_inc_ref(v_app_3597_);
v___x_3607_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3597_, v_fillableTerms_3596_, v_terms_3600_, v___x_3606_);
lean_dec_ref(v_fillableTerms_3596_);
if (lean_obj_tag(v___x_3607_) == 1)
{
lean_object* v_val_3608_; 
lean_dec_ref(v_app_3597_);
v_val_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_val_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v_app_3592_ = v_val_3608_;
goto v___jp_3591_;
}
else
{
lean_dec(v___x_3607_);
v_app_3592_ = v_app_3597_;
goto v___jp_3591_;
}
}
}
}
v___jp_3609_:
{
uint8_t v_parenthesize_3612_; 
v_parenthesize_3612_ = lean_ctor_get_uint8(v_format_3590_, 2);
if (v_parenthesize_3612_ == 0)
{
lean_dec(v___y_3610_);
v_fillableTerms_3596_ = v_fillableTerms_3611_;
goto v___jp_3595_;
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3613_ = lean_array_get_size(v_fillableTerms_3611_);
v___x_3614_ = lean_nat_sub(v___x_3613_, v___y_3610_);
v___x_3615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v___x_3614_, v___y_3610_, v_fillableTerms_3611_);
lean_dec(v___x_3614_);
v_fillableTerms_3596_ = v___x_3615_;
goto v___jp_3595_;
}
}
v___jp_3618_:
{
lean_object* v___x_3620_; uint8_t v___x_3621_; 
v___x_3620_ = lean_array_get_size(v___y_3619_);
v___x_3621_ = lean_nat_dec_eq(v___x_3620_, v___x_3617_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; uint8_t v___x_3623_; 
v___x_3622_ = lean_unsigned_to_nat(1u);
v___x_3623_ = lean_nat_dec_eq(v___x_3620_, v___x_3622_);
if (v___x_3623_ == 0)
{
uint8_t v___x_3624_; 
v___x_3624_ = lean_nat_dec_lt(v___x_3622_, v___x_3620_);
if (v___x_3624_ == 0)
{
v___y_3610_ = v___x_3622_;
v_fillableTerms_3611_ = v___y_3619_;
goto v___jp_3609_;
}
else
{
uint8_t v_hardNestedFirstTerm_3625_; 
v_hardNestedFirstTerm_3625_ = lean_ctor_get_uint8(v_format_3590_, 0);
if (v_hardNestedFirstTerm_3625_ == 0)
{
v___y_3610_ = v___x_3622_;
v_fillableTerms_3611_ = v___y_3619_;
goto v___jp_3609_;
}
else
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_nat_dec_lt(v___x_3617_, v___x_3620_);
if (v___x_3626_ == 0)
{
v___y_3610_ = v___x_3622_;
v_fillableTerms_3611_ = v___y_3619_;
goto v___jp_3609_;
}
else
{
lean_object* v_v_3627_; lean_object* v_v_3628_; uint8_t v_allowFill_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3640_; 
v_v_3627_ = lean_array_fget(v___y_3619_, v___x_3617_);
v_v_3628_ = lean_ctor_get(v_v_3627_, 0);
v_allowFill_3629_ = lean_ctor_get_uint8(v_v_3627_, sizeof(void*)*1);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_v_3627_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3631_ = v_v_3627_;
v_isShared_3632_ = v_isSharedCheck_3640_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_v_3628_);
lean_dec(v_v_3627_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3640_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v_xs_x27_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
v___x_3633_ = lean_box(0);
v_xs_x27_3634_ = lean_array_fset(v___y_3619_, v___x_3617_, v___x_3633_);
v___x_3635_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3628_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3635_);
v___x_3637_ = v___x_3631_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3635_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*1, v_allowFill_3629_);
v___x_3637_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3638_; 
v___x_3638_ = lean_array_fset(v_xs_x27_3634_, v___x_3617_, v___x_3637_);
v___y_3610_ = v___x_3622_;
v_fillableTerms_3611_ = v___x_3638_;
goto v___jp_3609_;
}
}
}
}
}
}
else
{
lean_object* v___x_3641_; lean_object* v_v_3642_; 
v___x_3641_ = lean_array_get(v___x_3616_, v___y_3619_, v___x_3617_);
lean_dec_ref(v___y_3619_);
v_v_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_v_3642_);
lean_dec(v___x_3641_);
return v_v_3642_;
}
}
else
{
lean_object* v___x_3643_; 
lean_dec_ref(v___y_3619_);
v___x_3643_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___boxed(lean_object* v_terms_3650_, lean_object* v_format_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v_terms_3650_, v_format_3651_);
lean_dec_ref(v_format_3651_);
lean_dec_ref(v_terms_3650_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(lean_object* v_upperBound_3653_, lean_object* v_inst_3654_, lean_object* v_R_3655_, lean_object* v_a_3656_, lean_object* v_b_3657_, lean_object* v_c_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3653_, v_a_3656_, v_b_3657_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___boxed(lean_object* v_upperBound_3660_, lean_object* v_inst_3661_, lean_object* v_R_3662_, lean_object* v_a_3663_, lean_object* v_b_3664_, lean_object* v_c_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(v_upperBound_3660_, v_inst_3661_, v_R_3662_, v_a_3663_, v_b_3664_, v_c_3665_);
lean_dec(v_upperBound_3660_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(size_t v_sz_3667_, size_t v_i_3668_, lean_object* v_bs_3669_){
_start:
{
uint8_t v___x_3670_; 
v___x_3670_ = lean_usize_dec_lt(v_i_3668_, v_sz_3667_);
if (v___x_3670_ == 0)
{
return v_bs_3669_;
}
else
{
lean_object* v_v_3671_; lean_object* v___x_3672_; lean_object* v_bs_x27_3673_; lean_object* v___x_3674_; size_t v___x_3675_; size_t v___x_3676_; lean_object* v___x_3677_; 
v_v_3671_ = lean_array_uget(v_bs_3669_, v_i_3668_);
v___x_3672_ = lean_unsigned_to_nat(0u);
v_bs_x27_3673_ = lean_array_uset(v_bs_3669_, v_i_3668_, v___x_3672_);
v___x_3674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3674_, 0, v_v_3671_);
lean_ctor_set_uint8(v___x_3674_, sizeof(void*)*1, v___x_3670_);
v___x_3675_ = ((size_t)1ULL);
v___x_3676_ = lean_usize_add(v_i_3668_, v___x_3675_);
v___x_3677_ = lean_array_uset(v_bs_x27_3673_, v_i_3668_, v___x_3674_);
v_i_3668_ = v___x_3676_;
v_bs_3669_ = v___x_3677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0___boxed(lean_object* v_sz_3679_, lean_object* v_i_3680_, lean_object* v_bs_3681_){
_start:
{
size_t v_sz_boxed_3682_; size_t v_i_boxed_3683_; lean_object* v_res_3684_; 
v_sz_boxed_3682_ = lean_unbox_usize(v_sz_3679_);
lean_dec(v_sz_3679_);
v_i_boxed_3683_ = lean_unbox_usize(v_i_3680_);
lean_dec(v_i_3680_);
v_res_3684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_boxed_3682_, v_i_boxed_3683_, v_bs_3681_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application(lean_object* v_terms_3685_, lean_object* v_format_3686_){
_start:
{
size_t v_sz_3687_; size_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v_sz_3687_ = lean_array_size(v_terms_3685_);
v___x_3688_ = ((size_t)0ULL);
v___x_3689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_3687_, v___x_3688_, v_terms_3685_);
v___x_3690_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v___x_3689_, v_format_3686_);
lean_dec_ref(v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application___boxed(lean_object* v_terms_3691_, lean_object* v_format_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_Fmt_Layouts_application(v_terms_3691_, v_format_3692_);
lean_dec_ref(v_format_3692_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(lean_object* v_f_3694_){
_start:
{
uint8_t v_hardNestedFirstTerm_3695_; uint8_t v_sparse_3696_; uint8_t v_parenthesize_3697_; uint8_t v_respectPseudoAlignment_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
v_hardNestedFirstTerm_3695_ = lean_ctor_get_uint8(v_f_3694_, 0);
v_sparse_3696_ = lean_ctor_get_uint8(v_f_3694_, 1);
v_parenthesize_3697_ = lean_ctor_get_uint8(v_f_3694_, 2);
v_respectPseudoAlignment_3698_ = lean_ctor_get_uint8(v_f_3694_, 3);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_f_3694_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v_f_3694_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_dec(v_f_3694_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3704_, 0, v_hardNestedFirstTerm_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3704_, 1, v_sparse_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3704_, 2, v_parenthesize_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3704_, 3, v_respectPseudoAlignment_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object* v_terms_3706_, lean_object* v_format_3707_){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(v_format_3707_);
v___x_3709_ = l_Lean_Fmt_Layouts_application(v_terms_3706_, v___x_3708_);
lean_dec_ref(v___x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl(lean_object* v_x_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_obj_tag_nat(v_x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl___boxed(lean_object* v_x_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___impl(v_x_3712_);
lean_dec_ref(v_x_3712_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(lean_object* v_t_3714_, lean_object* v_k_3715_){
_start:
{
lean_object* v_doc_3716_; lean_object* v___x_3717_; 
v_doc_3716_ = lean_ctor_get(v_t_3714_, 0);
lean_inc_ref(v_doc_3716_);
lean_dec_ref(v_t_3714_);
v___x_3717_ = lean_apply_1(v_k_3715_, v_doc_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(lean_object* v_motive_3718_, lean_object* v_ctorIdx_3719_, lean_object* v_t_3720_, lean_object* v_h_3721_, lean_object* v_k_3722_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3720_, v_k_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___boxed(lean_object* v_motive_3724_, lean_object* v_ctorIdx_3725_, lean_object* v_t_3726_, lean_object* v_h_3727_, lean_object* v_k_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(v_motive_3724_, v_ctorIdx_3725_, v_t_3726_, v_h_3727_, v_k_3728_);
lean_dec(v_ctorIdx_3725_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim___redArg(lean_object* v_t_3730_, lean_object* v_sep_3731_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3730_, v_sep_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim(lean_object* v_motive_3733_, lean_object* v_t_3734_, lean_object* v_h_3735_, lean_object* v_sep_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3734_, v_sep_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim___redArg(lean_object* v_t_3738_, lean_object* v_elems_3739_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3738_, v_elems_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim(lean_object* v_motive_3741_, lean_object* v_t_3742_, lean_object* v_h_3743_, lean_object* v_elems_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3742_, v_elems_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(size_t v_sz_3746_, size_t v_i_3747_, lean_object* v_bs_3748_){
_start:
{
uint8_t v___x_3749_; 
v___x_3749_ = lean_usize_dec_lt(v_i_3747_, v_sz_3746_);
if (v___x_3749_ == 0)
{
return v_bs_3748_;
}
else
{
lean_object* v_v_3750_; lean_object* v___x_3751_; lean_object* v_bs_x27_3752_; lean_object* v___y_3754_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v_v_3750_ = lean_array_uget(v_bs_3748_, v_i_3747_);
v___x_3751_ = lean_unsigned_to_nat(0u);
v_bs_x27_3752_ = lean_array_uset(v_bs_3748_, v_i_3747_, v___x_3751_);
v___x_3759_ = lean_usize_to_nat(v_i_3747_);
v___x_3760_ = lean_unsigned_to_nat(2u);
v___x_3761_ = lean_nat_mod(v___x_3759_, v___x_3760_);
lean_dec(v___x_3759_);
v___x_3762_ = lean_nat_dec_eq(v___x_3761_, v___x_3751_);
lean_dec(v___x_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_v_3750_);
v___y_3754_ = v___x_3763_;
goto v___jp_3753_;
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3764_ = lean_unsigned_to_nat(1u);
v___x_3765_ = lean_mk_empty_array_with_capacity(v___x_3764_);
v___x_3766_ = lean_array_push(v___x_3765_, v_v_3750_);
v___x_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
v___y_3754_ = v___x_3767_;
goto v___jp_3753_;
}
v___jp_3753_:
{
size_t v___x_3755_; size_t v___x_3756_; lean_object* v___x_3757_; 
v___x_3755_ = ((size_t)1ULL);
v___x_3756_ = lean_usize_add(v_i_3747_, v___x_3755_);
v___x_3757_ = lean_array_uset(v_bs_x27_3752_, v_i_3747_, v___y_3754_);
v_i_3747_ = v___x_3756_;
v_bs_3748_ = v___x_3757_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg___boxed(lean_object* v_sz_3768_, lean_object* v_i_3769_, lean_object* v_bs_3770_){
_start:
{
size_t v_sz_boxed_3771_; size_t v_i_boxed_3772_; lean_object* v_res_3773_; 
v_sz_boxed_3771_ = lean_unbox_usize(v_sz_3768_);
lean_dec(v_sz_3768_);
v_i_boxed_3772_ = lean_unbox_usize(v_i_3769_);
lean_dec(v_i_3769_);
v_res_3773_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_boxed_3771_, v_i_boxed_3772_, v_bs_3770_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object* v_elems_3774_){
_start:
{
size_t v_sz_3775_; size_t v___x_3776_; lean_object* v___x_3777_; 
v_sz_3775_ = lean_array_size(v_elems_3774_);
v___x_3776_ = ((size_t)0ULL);
v___x_3777_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3775_, v___x_3776_, v_elems_3774_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(lean_object* v_s_3778_, lean_object* v_elems_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_elems_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___boxed(lean_object* v_s_3781_, lean_object* v_elems_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(v_s_3781_, v_elems_3782_);
lean_dec_ref(v_s_3781_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(lean_object* v_as_3784_, size_t v_sz_3785_, size_t v_i_3786_, lean_object* v_bs_3787_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3785_, v_i_3786_, v_bs_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___boxed(lean_object* v_as_3789_, lean_object* v_sz_3790_, lean_object* v_i_3791_, lean_object* v_bs_3792_){
_start:
{
size_t v_sz_boxed_3793_; size_t v_i_boxed_3794_; lean_object* v_res_3795_; 
v_sz_boxed_3793_ = lean_unbox_usize(v_sz_3790_);
lean_dec(v_sz_3790_);
v_i_boxed_3794_ = lean_unbox_usize(v_i_3791_);
lean_dec(v_i_3791_);
v_res_3795_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(v_as_3789_, v_sz_boxed_3793_, v_i_boxed_3794_, v_bs_3792_);
lean_dec_ref(v_as_3789_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(size_t v_sz_3798_, size_t v_i_3799_, lean_object* v_bs_3800_){
_start:
{
uint8_t v___x_3801_; 
v___x_3801_ = lean_usize_dec_lt(v_i_3799_, v_sz_3798_);
if (v___x_3801_ == 0)
{
return v_bs_3800_;
}
else
{
lean_object* v_v_3802_; lean_object* v___x_3803_; lean_object* v_bs_x27_3804_; lean_object* v___y_3806_; 
v_v_3802_ = lean_array_uget(v_bs_3800_, v_i_3799_);
v___x_3803_ = lean_unsigned_to_nat(0u);
v_bs_x27_3804_ = lean_array_uset(v_bs_3800_, v_i_3799_, v___x_3803_);
if (lean_obj_tag(v_v_3802_) == 0)
{
v___y_3806_ = v_v_3802_;
goto v___jp_3805_;
}
else
{
lean_object* v_docs_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3825_; 
v_docs_3811_ = lean_ctor_get(v_v_3802_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_v_3802_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3813_ = v_v_3802_;
v_isShared_3814_ = v_isSharedCheck_3825_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_docs_3811_);
lean_dec(v_v_3802_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3825_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v___x_3815_ = lean_array_get_size(v_docs_3811_);
v___x_3816_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_3817_ = lean_nat_dec_lt(v___x_3803_, v___x_3815_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; 
lean_del_object(v___x_3813_);
lean_dec_ref(v_docs_3811_);
v___x_3818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_3806_ = v___x_3818_;
goto v___jp_3805_;
}
else
{
size_t v___x_3819_; size_t v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3819_ = ((size_t)0ULL);
v___x_3820_ = lean_usize_of_nat(v___x_3815_);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_docs_3811_, v___x_3819_, v___x_3820_, v___x_3816_);
lean_dec_ref(v_docs_3811_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 0, v___x_3821_);
v___x_3823_ = v___x_3813_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
v___y_3806_ = v___x_3823_;
goto v___jp_3805_;
}
}
}
}
v___jp_3805_:
{
size_t v___x_3807_; size_t v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = ((size_t)1ULL);
v___x_3808_ = lean_usize_add(v_i_3799_, v___x_3807_);
v___x_3809_ = lean_array_uset(v_bs_x27_3804_, v_i_3799_, v___y_3806_);
v_i_3799_ = v___x_3808_;
v_bs_3800_ = v___x_3809_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___boxed(lean_object* v_sz_3826_, lean_object* v_i_3827_, lean_object* v_bs_3828_){
_start:
{
size_t v_sz_boxed_3829_; size_t v_i_boxed_3830_; lean_object* v_res_3831_; 
v_sz_boxed_3829_ = lean_unbox_usize(v_sz_3826_);
lean_dec(v_sz_3826_);
v_i_boxed_3830_ = lean_unbox_usize(v_i_3827_);
lean_dec(v_i_3827_);
v_res_3831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_boxed_3829_, v_i_boxed_3830_, v_bs_3828_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(lean_object* v_as_3832_, lean_object* v_j_3833_){
_start:
{
lean_object* v___x_3838_; uint8_t v___x_3839_; 
v___x_3838_ = lean_array_get_size(v_as_3832_);
v___x_3839_ = lean_nat_dec_lt(v_j_3833_, v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; 
lean_dec(v_j_3833_);
v___x_3840_ = lean_box(0);
return v___x_3840_;
}
else
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_array_fget(v_as_3832_, v_j_3833_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_dec_ref_known(v___x_3841_, 1);
goto v___jp_3834_;
}
else
{
lean_object* v_docs_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3852_; 
v_docs_3842_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3844_ = v___x_3841_;
v_isShared_3845_ = v_isSharedCheck_3852_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_docs_3842_);
lean_dec(v___x_3841_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3852_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v___x_3846_ = lean_array_get_size(v_docs_3842_);
lean_dec_ref(v_docs_3842_);
v___x_3847_ = lean_unsigned_to_nat(0u);
v___x_3848_ = lean_nat_dec_eq(v___x_3846_, v___x_3847_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3850_; 
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v_j_3833_);
v___x_3850_ = v___x_3844_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_j_3833_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
else
{
lean_del_object(v___x_3844_);
goto v___jp_3834_;
}
}
}
}
v___jp_3834_:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = lean_unsigned_to_nat(1u);
v___x_3836_ = lean_nat_add(v_j_3833_, v___x_3835_);
lean_dec(v_j_3833_);
v_j_3833_ = v___x_3836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2___boxed(lean_object* v_as_3853_, lean_object* v_j_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_as_3853_, v_j_3854_);
lean_dec_ref(v_as_3853_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(size_t v_sz_3856_, size_t v_i_3857_, lean_object* v_bs_3858_){
_start:
{
uint8_t v___x_3859_; 
v___x_3859_ = lean_usize_dec_lt(v_i_3857_, v_sz_3856_);
if (v___x_3859_ == 0)
{
return v_bs_3858_;
}
else
{
lean_object* v_v_3860_; lean_object* v___x_3861_; lean_object* v_bs_x27_3862_; lean_object* v___y_3864_; 
v_v_3860_ = lean_array_uget(v_bs_3858_, v_i_3857_);
v___x_3861_ = lean_unsigned_to_nat(0u);
v_bs_x27_3862_ = lean_array_uset(v_bs_3858_, v_i_3857_, v___x_3861_);
if (lean_obj_tag(v_v_3860_) == 0)
{
lean_object* v_doc_3869_; 
v_doc_3869_ = lean_ctor_get(v_v_3860_, 0);
lean_inc_ref(v_doc_3869_);
lean_dec_ref_known(v_v_3860_, 1);
v___y_3864_ = v_doc_3869_;
goto v___jp_3863_;
}
else
{
lean_object* v_docs_3870_; lean_object* v___x_3871_; 
v_docs_3870_ = lean_ctor_get(v_v_3860_, 0);
lean_inc_ref(v_docs_3870_);
lean_dec_ref_known(v_v_3860_, 1);
v___x_3871_ = l_Lean_Fmt_Layouts_fill(v_docs_3870_);
lean_dec_ref(v_docs_3870_);
v___y_3864_ = v___x_3871_;
goto v___jp_3863_;
}
v___jp_3863_:
{
size_t v___x_3865_; size_t v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = ((size_t)1ULL);
v___x_3866_ = lean_usize_add(v_i_3857_, v___x_3865_);
v___x_3867_ = lean_array_uset(v_bs_x27_3862_, v_i_3857_, v___y_3864_);
v_i_3857_ = v___x_3866_;
v_bs_3858_ = v___x_3867_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0___boxed(lean_object* v_sz_3872_, lean_object* v_i_3873_, lean_object* v_bs_3874_){
_start:
{
size_t v_sz_boxed_3875_; size_t v_i_boxed_3876_; lean_object* v_res_3877_; 
v_sz_boxed_3875_ = lean_unbox_usize(v_sz_3872_);
lean_dec(v_sz_3872_);
v_i_boxed_3876_ = lean_unbox_usize(v_i_3873_);
lean_dec(v_i_3873_);
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_boxed_3875_, v_i_boxed_3876_, v_bs_3874_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object* v_lb_3879_, lean_object* v_terms_3880_, lean_object* v_rb_3881_){
_start:
{
lean_object* v_terms_3883_; size_t v_sz_3891_; size_t v___x_3892_; lean_object* v_terms_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; 
v_sz_3891_ = lean_array_size(v_terms_3880_);
v___x_3892_ = ((size_t)0ULL);
v_terms_3893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_3891_, v___x_3892_, v_terms_3880_);
v___x_3894_ = lean_unsigned_to_nat(1u);
v___x_3895_ = lean_array_get_size(v_terms_3893_);
v___x_3896_ = lean_nat_dec_lt(v___x_3894_, v___x_3895_);
if (v___x_3896_ == 0)
{
v_terms_3883_ = v_terms_3893_;
goto v___jp_3882_;
}
else
{
lean_object* v___x_3897_; lean_object* v_firstElemsIdx_x3f_3898_; 
v___x_3897_ = lean_unsigned_to_nat(0u);
v_firstElemsIdx_x3f_3898_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_terms_3893_, v___x_3897_);
if (lean_obj_tag(v_firstElemsIdx_x3f_3898_) == 1)
{
lean_object* v_val_3899_; uint8_t v___x_3900_; 
v_val_3899_ = lean_ctor_get(v_firstElemsIdx_x3f_3898_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v_firstElemsIdx_x3f_3898_, 1);
v___x_3900_ = lean_nat_dec_lt(v_val_3899_, v___x_3895_);
if (v___x_3900_ == 0)
{
lean_dec(v_val_3899_);
v_terms_3883_ = v_terms_3893_;
goto v___jp_3882_;
}
else
{
lean_object* v_v_3901_; lean_object* v___x_3902_; lean_object* v_xs_x27_3903_; lean_object* v___y_3905_; 
v_v_3901_ = lean_array_fget(v_terms_3893_, v_val_3899_);
v___x_3902_ = lean_box(0);
v_xs_x27_3903_ = lean_array_fset(v_terms_3893_, v_val_3899_, v___x_3902_);
if (lean_obj_tag(v_v_3901_) == 0)
{
v___y_3905_ = v_v_3901_;
goto v___jp_3904_;
}
else
{
lean_object* v_docs_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_docs_3907_ = lean_ctor_get(v_v_3901_, 0);
v___x_3908_ = lean_array_get_size(v_docs_3907_);
v___x_3909_ = lean_nat_dec_lt(v___x_3897_, v___x_3908_);
if (v___x_3909_ == 0)
{
v___y_3905_ = v_v_3901_;
goto v___jp_3904_;
}
else
{
lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3920_; 
lean_inc_ref(v_docs_3907_);
v_isSharedCheck_3920_ = !lean_is_exclusive(v_v_3901_);
if (v_isSharedCheck_3920_ == 0)
{
lean_object* v_unused_3921_; 
v_unused_3921_ = lean_ctor_get(v_v_3901_, 0);
lean_dec(v_unused_3921_);
v___x_3911_ = v_v_3901_;
v_isShared_3912_ = v_isSharedCheck_3920_;
goto v_resetjp_3910_;
}
else
{
lean_dec(v_v_3901_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3920_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v_v_3913_; lean_object* v_xs_x27_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
v_v_3913_ = lean_array_fget(v_docs_3907_, v___x_3897_);
v_xs_x27_3914_ = lean_array_fset(v_docs_3907_, v___x_3897_, v___x_3902_);
v___x_3915_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3913_);
v___x_3916_ = lean_array_fset(v_xs_x27_3914_, v___x_3897_, v___x_3915_);
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 0, v___x_3916_);
v___x_3918_ = v___x_3911_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
v___y_3905_ = v___x_3918_;
goto v___jp_3904_;
}
}
}
}
v___jp_3904_:
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_array_fset(v_xs_x27_3903_, v_val_3899_, v___y_3905_);
lean_dec(v_val_3899_);
v_terms_3883_ = v___x_3906_;
goto v___jp_3882_;
}
}
}
else
{
lean_dec(v_firstElemsIdx_x3f_3898_);
v_terms_3883_ = v_terms_3893_;
goto v___jp_3882_;
}
}
v___jp_3882_:
{
lean_object* v___x_3884_; size_t v_sz_3885_; size_t v___x_3886_; lean_object* v_terms_x27_3887_; lean_object* v_terms_x27_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3884_ = ((lean_object*)(l_Lean_Fmt_Layouts_metaApplication___closed__0));
v_sz_3885_ = lean_array_size(v_terms_3883_);
v___x_3886_ = ((size_t)0ULL);
v_terms_x27_3887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_3885_, v___x_3886_, v_terms_3883_);
v_terms_x27_3888_ = l_Lean_Fmt_Layouts_sepFill(v___x_3884_, v_terms_x27_3887_);
lean_dec_ref(v_terms_x27_3887_);
v___x_3889_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_3890_ = l_Lean_Fmt_Layouts_bracketed(v_lb_3879_, v_terms_x27_3888_, v_rb_3881_, v___x_3889_);
return v___x_3890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object* v_chain_3924_){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = ((lean_object*)(l_Lean_Fmt_Layouts_pipeOperator___closed__0));
v___x_3926_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_3924_, v___x_3925_);
return v___x_3926_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0(void){
_start:
{
uint8_t v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3927_ = 1;
v___x_3928_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3929_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set_uint8(v___x_3929_, sizeof(void*)*1, v___x_3927_);
return v___x_3929_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default(void){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = lean_obj_once(&l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0, &l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0);
return v___x_3930_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock(void){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0(lean_object* v_block_3932_){
_start:
{
uint8_t v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = 1;
v___x_3934_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3934_, 0, v_block_3932_);
lean_ctor_set_uint8(v___x_3934_, sizeof(void*)*1, v___x_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(lean_object* v_val_3937_, uint8_t v___x_3938_, lean_object* v___x_3939_, lean_object* v_____r_3940_, lean_object* v_stickyAcc_3941_){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_3937_, v___x_3938_);
v___x_3943_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v___x_3939_, v_stickyAcc_3941_, v___x_3942_);
lean_dec(v___x_3942_);
v___x_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1___boxed(lean_object* v_val_3945_, lean_object* v___x_3946_, lean_object* v___x_3947_, lean_object* v_____r_3948_, lean_object* v_stickyAcc_3949_){
_start:
{
uint8_t v___x_1444__boxed_3950_; lean_object* v_res_3951_; 
v___x_1444__boxed_3950_ = lean_unbox(v___x_3946_);
v_res_3951_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_3945_, v___x_1444__boxed_3950_, v___x_3947_, v_____r_3948_, v_stickyAcc_3949_);
lean_dec_ref(v_val_3945_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(lean_object* v_upperBound_3952_, lean_object* v___y_3953_, lean_object* v___x_3954_, lean_object* v_a_3955_, lean_object* v_b_3956_){
_start:
{
uint8_t v___x_3957_; 
v___x_3957_ = lean_nat_dec_lt(v_a_3955_, v_upperBound_3952_);
if (v___x_3957_ == 0)
{
lean_dec(v_a_3955_);
return v_b_3956_;
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v_block_3960_; uint8_t v_hardNestedIfFirst_3961_; lean_object* v___x_3962_; lean_object* v_a_3964_; lean_object* v___y_3968_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3958_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_3959_ = lean_array_get_borrowed(v___x_3958_, v___y_3953_, v_a_3955_);
v_block_3960_ = lean_ctor_get(v___x_3959_, 0);
v_hardNestedIfFirst_3961_ = lean_ctor_get_uint8(v___x_3959_, sizeof(void*)*1);
v___x_3962_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_b_3956_);
v___x_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3971_, 0, v_b_3956_);
v___x_3972_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_3973_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3971_, v___x_3972_);
v___x_3974_ = lean_box(0);
lean_inc_ref_n(v_block_3960_, 2);
v___x_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3975_, 0, v_block_3960_);
v___x_3976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3974_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
lean_ctor_set(v___x_3976_, 2, v___x_3974_);
v___x_3977_ = lean_unsigned_to_nat(2u);
v___x_3978_ = lean_mk_empty_array_with_capacity(v___x_3977_);
lean_inc_ref(v___x_3978_);
v___x_3979_ = lean_array_push(v___x_3978_, v___x_3973_);
v___x_3980_ = lean_array_push(v___x_3979_, v___x_3976_);
v___x_3981_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3980_);
lean_dec_ref(v___x_3980_);
v___x_3982_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3981_);
v___x_3983_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_block_3960_);
if (lean_obj_tag(v___x_3983_) == 1)
{
lean_object* v_val_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4008_; 
v_val_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_4008_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_val_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4008_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v_stickyVariant_3988_; lean_object* v___x_3989_; lean_object* v___x_3991_; 
v_stickyVariant_3988_ = lean_ctor_get(v_val_3984_, 0);
v___x_3989_ = l_Lean_Fmt_TaggedDoc_flattened(v_b_3956_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_3989_);
v___x_3991_ = v___x_3986_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_4007_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3992_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_3993_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3991_, v___x_3992_);
lean_inc_ref(v_stickyVariant_3988_);
v___x_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3994_, 0, v_stickyVariant_3988_);
v___x_3995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3974_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
lean_ctor_set(v___x_3995_, 2, v___x_3974_);
v___x_3996_ = lean_array_push(v___x_3978_, v___x_3993_);
v___x_3997_ = lean_array_push(v___x_3996_, v___x_3995_);
v___x_3998_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3997_);
lean_dec_ref(v___x_3997_);
if (v_hardNestedIfFirst_3961_ == 0)
{
goto v___jp_3999_;
}
else
{
lean_object* v___x_4002_; uint8_t v___x_4003_; 
v___x_4002_ = lean_nat_sub(v___x_3954_, v___x_3962_);
v___x_4003_ = lean_nat_dec_lt(v_a_3955_, v___x_4002_);
lean_dec(v___x_4002_);
if (v___x_4003_ == 0)
{
goto v___jp_3999_;
}
else
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_3998_);
v___x_4005_ = lean_box(0);
v___x_4006_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_3984_, v___x_3957_, v___x_3982_, v___x_4005_, v___x_4004_);
lean_dec(v_val_3984_);
v___y_3968_ = v___x_4006_;
goto v___jp_3967_;
}
}
v___jp_3999_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_box(0);
v___x_4001_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_3984_, v___x_3957_, v___x_3982_, v___x_4000_, v___x_3998_);
lean_dec(v_val_3984_);
v___y_3968_ = v___x_4001_;
goto v___jp_3967_;
}
}
}
}
else
{
lean_dec(v___x_3983_);
lean_dec_ref(v___x_3978_);
lean_dec_ref(v_b_3956_);
v_a_3964_ = v___x_3982_;
goto v___jp_3963_;
}
v___jp_3963_:
{
lean_object* v___x_3965_; 
v___x_3965_ = lean_nat_add(v_a_3955_, v___x_3962_);
lean_dec(v_a_3955_);
v_a_3955_ = v___x_3965_;
v_b_3956_ = v_a_3964_;
goto _start;
}
v___jp_3967_:
{
if (lean_obj_tag(v___y_3968_) == 0)
{
lean_object* v_a_3969_; 
lean_dec(v_a_3955_);
v_a_3969_ = lean_ctor_get(v___y_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref_known(v___y_3968_, 1);
return v_a_3969_;
}
else
{
lean_object* v_a_3970_; 
v_a_3970_ = lean_ctor_get(v___y_3968_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v___y_3968_, 1);
v_a_3964_ = v_a_3970_;
goto v___jp_3963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___boxed(lean_object* v_upperBound_4009_, lean_object* v___y_4010_, lean_object* v___x_4011_, lean_object* v_a_4012_, lean_object* v_b_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4009_, v___y_4010_, v___x_4011_, v_a_4012_, v_b_4013_);
lean_dec(v___x_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v_upperBound_4009_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(lean_object* v_as_4015_, size_t v_i_4016_, size_t v_stop_4017_, lean_object* v_b_4018_){
_start:
{
lean_object* v___y_4020_; uint8_t v___x_4024_; 
v___x_4024_ = lean_usize_dec_eq(v_i_4016_, v_stop_4017_);
if (v___x_4024_ == 0)
{
lean_object* v___x_4025_; lean_object* v_block_4026_; uint8_t v___x_4027_; 
v___x_4025_ = lean_array_uget_borrowed(v_as_4015_, v_i_4016_);
v_block_4026_ = lean_ctor_get(v___x_4025_, 0);
v___x_4027_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_block_4026_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; 
lean_inc(v___x_4025_);
v___x_4028_ = lean_array_push(v_b_4018_, v___x_4025_);
v___y_4020_ = v___x_4028_;
goto v___jp_4019_;
}
else
{
v___y_4020_ = v_b_4018_;
goto v___jp_4019_;
}
}
else
{
return v_b_4018_;
}
v___jp_4019_:
{
size_t v___x_4021_; size_t v___x_4022_; 
v___x_4021_ = ((size_t)1ULL);
v___x_4022_ = lean_usize_add(v_i_4016_, v___x_4021_);
v_i_4016_ = v___x_4022_;
v_b_4018_ = v___y_4020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1___boxed(lean_object* v_as_4029_, lean_object* v_i_4030_, lean_object* v_stop_4031_, lean_object* v_b_4032_){
_start:
{
size_t v_i_boxed_4033_; size_t v_stop_boxed_4034_; lean_object* v_res_4035_; 
v_i_boxed_4033_ = lean_unbox_usize(v_i_4030_);
lean_dec(v_i_4030_);
v_stop_boxed_4034_ = lean_unbox_usize(v_stop_4031_);
lean_dec(v_stop_4031_);
v_res_4035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_as_4029_, v_i_boxed_4033_, v_stop_boxed_4034_, v_b_4032_);
lean_dec_ref(v_as_4029_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks(lean_object* v_blocks_4038_, uint8_t v_format_4039_){
_start:
{
lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___y_4050_; lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; 
v___x_4047_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4048_ = lean_unsigned_to_nat(0u);
v___x_4060_ = lean_array_get_size(v_blocks_4038_);
v___x_4061_ = ((lean_object*)(l_Lean_Fmt_Layouts_blocks___closed__0));
v___x_4062_ = lean_nat_dec_lt(v___x_4048_, v___x_4060_);
if (v___x_4062_ == 0)
{
v___y_4050_ = v___x_4061_;
goto v___jp_4049_;
}
else
{
size_t v___x_4063_; size_t v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = ((size_t)0ULL);
v___x_4064_ = lean_usize_of_nat(v___x_4060_);
v___x_4065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4038_, v___x_4063_, v___x_4064_, v___x_4061_);
v___y_4050_ = v___x_4065_;
goto v___jp_4049_;
}
v___jp_4040_:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v___y_4041_, v___y_4042_, v___y_4041_, v___y_4043_, v___y_4044_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
if (v_format_4039_ == 0)
{
return v___x_4045_;
}
else
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4045_);
return v___x_4046_;
}
}
v___jp_4049_:
{
lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4051_ = lean_array_get_size(v___y_4050_);
v___x_4052_ = lean_nat_dec_eq(v___x_4051_, v___x_4048_);
if (v___x_4052_ == 0)
{
lean_object* v___x_4053_; lean_object* v_block_4054_; uint8_t v_hardNestedIfFirst_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4053_ = lean_array_get_borrowed(v___x_4047_, v___y_4050_, v___x_4048_);
v_block_4054_ = lean_ctor_get(v___x_4053_, 0);
v_hardNestedIfFirst_4055_ = lean_ctor_get_uint8(v___x_4053_, sizeof(void*)*1);
v___x_4056_ = lean_unsigned_to_nat(1u);
v___x_4057_ = lean_nat_dec_eq(v___x_4051_, v___x_4056_);
if (v___x_4057_ == 0)
{
if (v_hardNestedIfFirst_4055_ == 0)
{
lean_inc_ref(v_block_4054_);
v___y_4041_ = v___x_4051_;
v___y_4042_ = v___y_4050_;
v___y_4043_ = v___x_4056_;
v___y_4044_ = v_block_4054_;
goto v___jp_4040_;
}
else
{
lean_object* v___x_4058_; 
lean_inc_ref(v_block_4054_);
v___x_4058_ = l_Lean_Fmt_TaggedDoc_hardNested(v_block_4054_);
v___y_4041_ = v___x_4051_;
v___y_4042_ = v___y_4050_;
v___y_4043_ = v___x_4056_;
v___y_4044_ = v___x_4058_;
goto v___jp_4040_;
}
}
else
{
lean_inc_ref(v_block_4054_);
lean_dec_ref(v___y_4050_);
return v_block_4054_;
}
}
else
{
lean_object* v___x_4059_; 
lean_dec_ref(v___y_4050_);
v___x_4059_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_4059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks___boxed(lean_object* v_blocks_4066_, lean_object* v_format_4067_){
_start:
{
uint8_t v_format_boxed_4068_; lean_object* v_res_4069_; 
v_format_boxed_4068_ = lean_unbox(v_format_4067_);
v_res_4069_ = l_Lean_Fmt_Layouts_blocks(v_blocks_4066_, v_format_boxed_4068_);
lean_dec_ref(v_blocks_4066_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(lean_object* v_upperBound_4070_, lean_object* v___y_4071_, lean_object* v___x_4072_, lean_object* v_inst_4073_, lean_object* v_R_4074_, lean_object* v_a_4075_, lean_object* v_b_4076_, lean_object* v_c_4077_){
_start:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4070_, v___y_4071_, v___x_4072_, v_a_4075_, v_b_4076_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___boxed(lean_object* v_upperBound_4079_, lean_object* v___y_4080_, lean_object* v___x_4081_, lean_object* v_inst_4082_, lean_object* v_R_4083_, lean_object* v_a_4084_, lean_object* v_b_4085_, lean_object* v_c_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(v_upperBound_4079_, v___y_4080_, v___x_4081_, v_inst_4082_, v_R_4083_, v_a_4084_, v_b_4085_, v_c_4086_);
lean_dec(v___x_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v_upperBound_4079_);
return v_res_4087_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_tuple___closed__0(void){
_start:
{
uint8_t v___x_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4088_ = 0;
v___x_4089_ = 1;
v___x_4090_ = l_Lean_Fmt_TaggedDoc_break;
v___x_4091_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*1, v___x_4089_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*1 + 1, v___x_4088_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple(lean_object* v_sep_4092_, lean_object* v_lb_4093_, lean_object* v_fields_4094_, lean_object* v_rb_4095_){
_start:
{
uint8_t v___x_4096_; lean_object* v_fields_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; 
v___x_4096_ = 1;
lean_inc_ref(v_sep_4092_);
v_fields_4097_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4092_, v_fields_4094_, v___x_4096_);
v___x_4098_ = lean_array_get_size(v_fields_4097_);
v___x_4099_ = lean_unsigned_to_nat(1u);
v___x_4100_ = lean_nat_dec_eq(v___x_4098_, v___x_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; lean_object* v_fields_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4101_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v_fields_4102_ = l_Lean_Fmt_Layouts_sepArray(v_sep_4092_, v_fields_4097_, v___x_4101_);
lean_dec_ref(v_fields_4097_);
v___x_4103_ = lean_obj_once(&l_Lean_Fmt_Layouts_tuple___closed__0, &l_Lean_Fmt_Layouts_tuple___closed__0_once, _init_l_Lean_Fmt_Layouts_tuple___closed__0);
v___x_4104_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4093_, v_fields_4102_, v_rb_4095_, v___x_4103_);
return v___x_4104_;
}
else
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
lean_dec_ref(v_sep_4092_);
v___x_4105_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4106_ = lean_unsigned_to_nat(0u);
v___x_4107_ = lean_array_get(v___x_4105_, v_fields_4097_, v___x_4106_);
lean_dec_ref(v_fields_4097_);
v___x_4108_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_4109_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4093_, v___x_4107_, v_rb_4095_, v___x_4108_);
return v___x_4109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple___boxed(lean_object* v_sep_4110_, lean_object* v_lb_4111_, lean_object* v_fields_4112_, lean_object* v_rb_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l_Lean_Fmt_Layouts_tuple(v_sep_4110_, v_lb_4111_, v_fields_4112_, v_rb_4113_);
lean_dec_ref(v_fields_4112_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection(lean_object* v_sep_4115_, lean_object* v_lb_4116_, lean_object* v_elems_4117_, lean_object* v_rb_4118_, lean_object* v_format_4119_){
_start:
{
lean_object* v___y_4121_; uint8_t v___x_4128_; lean_object* v_elems_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v___x_4128_ = 1;
lean_inc_ref(v_sep_4115_);
v_elems_4129_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4115_, v_elems_4117_, v___x_4128_);
v___x_4130_ = lean_unsigned_to_nat(1u);
v___x_4131_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_elems_4129_);
v___x_4132_ = lean_nat_dec_lt(v___x_4130_, v___x_4131_);
lean_dec(v___x_4131_);
if (v___x_4132_ == 0)
{
v___y_4121_ = v_elems_4129_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4133_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4133_ = lean_unsigned_to_nat(0u);
v___x_4134_ = lean_array_get_size(v_elems_4129_);
v___x_4135_ = lean_nat_dec_lt(v___x_4133_, v___x_4134_);
if (v___x_4135_ == 0)
{
v___y_4121_ = v_elems_4129_;
goto v___jp_4120_;
}
else
{
lean_object* v_v_4136_; lean_object* v___x_4137_; lean_object* v_xs_x27_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v_v_4136_ = lean_array_fget(v_elems_4129_, v___x_4133_);
v___x_4137_ = lean_box(0);
v_xs_x27_4138_ = lean_array_fset(v_elems_4129_, v___x_4133_, v___x_4137_);
v___x_4139_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4136_);
v___x_4140_ = lean_array_fset(v_xs_x27_4138_, v___x_4133_, v___x_4139_);
v___y_4121_ = v___x_4140_;
goto v___jp_4120_;
}
}
v___jp_4120_:
{
uint8_t v_spacing_4122_; lean_object* v_fields_4123_; lean_object* v___x_4124_; lean_object* v_doc_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; 
v_spacing_4122_ = lean_ctor_get_uint8(v_format_4119_, 0);
v_fields_4123_ = l_Lean_Fmt_Layouts_sepFill(v_sep_4115_, v___y_4121_);
lean_dec_ref(v___y_4121_);
v___x_4124_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_4124_, 0, v_spacing_4122_);
v_doc_4125_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4116_, v_fields_4123_, v_rb_4118_, v___x_4124_);
v___x_4126_ = 1;
lean_inc_ref(v_doc_4125_);
v___x_4127_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4125_, v_doc_4125_, v___x_4126_);
return v___x_4127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection___boxed(lean_object* v_sep_4141_, lean_object* v_lb_4142_, lean_object* v_elems_4143_, lean_object* v_rb_4144_, lean_object* v_format_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Fmt_Layouts_collection(v_sep_4141_, v_lb_4142_, v_elems_4143_, v_rb_4144_, v_format_4145_);
lean_dec_ref(v_format_4145_);
lean_dec_ref(v_elems_4143_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0(lean_object* v_keyword_4147_, lean_object* v_collection_4148_){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4149_ = lean_unsigned_to_nat(2u);
v___x_4150_ = lean_mk_empty_array_with_capacity(v___x_4149_);
v___x_4151_ = lean_array_push(v___x_4150_, v_keyword_4147_);
v___x_4152_ = lean_array_push(v___x_4151_, v_collection_4148_);
v___x_4153_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4152_);
lean_dec_ref(v___x_4152_);
v___x_4154_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4153_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object* v_sep_4155_, lean_object* v_keyword_4156_, lean_object* v_lb_4157_, lean_object* v_elems_4158_, lean_object* v_rb_4159_, lean_object* v_format_4160_){
_start:
{
lean_object* v___f_4161_; lean_object* v_collection_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___f_4161_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0), 2, 1);
lean_closure_set(v___f_4161_, 0, v_keyword_4156_);
v_collection_4162_ = l_Lean_Fmt_Layouts_collection(v_sep_4155_, v_lb_4157_, v_elems_4158_, v_rb_4159_, v_format_4160_);
v___x_4163_ = lean_box(0);
v___x_4164_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_collection_4162_, v___f_4161_, v___x_4163_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___boxed(lean_object* v_sep_4165_, lean_object* v_keyword_4166_, lean_object* v_lb_4167_, lean_object* v_elems_4168_, lean_object* v_rb_4169_, lean_object* v_format_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Fmt_Layouts_keywordPrefixedCollection(v_sep_4165_, v_keyword_4166_, v_lb_4167_, v_elems_4168_, v_rb_4169_, v_format_4170_);
lean_dec_ref(v_format_4170_);
lean_dec_ref(v_elems_4168_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl(lean_object* v_x_4172_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = lean_obj_tag_nat(v_x_4172_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl___boxed(lean_object* v_x_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___impl(v_x_4174_);
lean_dec(v_x_4174_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object* v_t_4176_, lean_object* v_k_4177_){
_start:
{
if (lean_obj_tag(v_t_4176_) == 0)
{
uint8_t v_respectPseudoAlignment_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v_respectPseudoAlignment_4178_ = lean_ctor_get_uint8(v_t_4176_, 0);
v___x_4179_ = lean_box(v_respectPseudoAlignment_4178_);
v___x_4180_ = lean_apply_1(v_k_4177_, v___x_4179_);
return v___x_4180_;
}
else
{
return v_k_4177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object* v_t_4181_, lean_object* v_k_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4181_, v_k_4182_);
lean_dec(v_t_4181_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object* v_motive_4184_, lean_object* v_ctorIdx_4185_, lean_object* v_t_4186_, lean_object* v_h_4187_, lean_object* v_k_4188_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4186_, v_k_4188_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object* v_motive_4190_, lean_object* v_ctorIdx_4191_, lean_object* v_t_4192_, lean_object* v_h_4193_, lean_object* v_k_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(v_motive_4190_, v_ctorIdx_4191_, v_t_4192_, v_h_4193_, v_k_4194_);
lean_dec(v_t_4192_);
lean_dec(v_ctorIdx_4191_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object* v_t_4196_, lean_object* v_local_4197_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4196_, v_local_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object* v_t_4199_, lean_object* v_local_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(v_t_4199_, v_local_4200_);
lean_dec(v_t_4199_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object* v_motive_4202_, lean_object* v_t_4203_, lean_object* v_h_4204_, lean_object* v_local_4205_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4203_, v_local_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object* v_motive_4207_, lean_object* v_t_4208_, lean_object* v_h_4209_, lean_object* v_local_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(v_motive_4207_, v_t_4208_, v_h_4209_, v_local_4210_);
lean_dec(v_t_4208_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object* v_t_4212_, lean_object* v_global_4213_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4212_, v_global_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object* v_t_4215_, lean_object* v_global_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(v_t_4215_, v_global_4216_);
lean_dec(v_t_4215_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object* v_motive_4218_, lean_object* v_t_4219_, lean_object* v_h_4220_, lean_object* v_global_4221_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4219_, v_global_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object* v_motive_4223_, lean_object* v_t_4224_, lean_object* v_h_4225_, lean_object* v_global_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(v_motive_4223_, v_t_4224_, v_h_4225_, v_global_4226_);
lean_dec(v_t_4224_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(lean_object* v_as_4228_, size_t v_i_4229_, size_t v_stop_4230_, lean_object* v_b_4231_){
_start:
{
lean_object* v___y_4233_; uint8_t v___x_4237_; 
v___x_4237_ = lean_usize_dec_eq(v_i_4229_, v_stop_4230_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = lean_array_uget_borrowed(v_as_4228_, v_i_4229_);
v___x_4239_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_4238_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; 
lean_inc(v___x_4238_);
v___x_4240_ = lean_array_push(v_b_4231_, v___x_4238_);
v___y_4233_ = v___x_4240_;
goto v___jp_4232_;
}
else
{
v___y_4233_ = v_b_4231_;
goto v___jp_4232_;
}
}
else
{
return v_b_4231_;
}
v___jp_4232_:
{
size_t v___x_4234_; size_t v___x_4235_; lean_object* v___x_4236_; 
v___x_4234_ = ((size_t)1ULL);
v___x_4235_ = lean_usize_add(v_i_4229_, v___x_4234_);
v___x_4236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_as_4228_, v___x_4235_, v_stop_4230_, v___y_4233_);
return v___x_4236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object* v_as_4241_, lean_object* v_i_4242_, lean_object* v_stop_4243_, lean_object* v_b_4244_){
_start:
{
size_t v_i_boxed_4245_; size_t v_stop_boxed_4246_; lean_object* v_res_4247_; 
v_i_boxed_4245_ = lean_unbox_usize(v_i_4242_);
lean_dec(v_i_4242_);
v_stop_boxed_4246_ = lean_unbox_usize(v_stop_4243_);
lean_dec(v_stop_4243_);
v_res_4247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_as_4241_, v_i_boxed_4245_, v_stop_boxed_4246_, v_b_4244_);
lean_dec_ref(v_as_4241_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(size_t v_sz_4248_, size_t v_i_4249_, lean_object* v_bs_4250_){
_start:
{
uint8_t v___x_4251_; 
v___x_4251_ = lean_usize_dec_lt(v_i_4249_, v_sz_4248_);
if (v___x_4251_ == 0)
{
return v_bs_4250_;
}
else
{
lean_object* v_v_4252_; lean_object* v___x_4253_; lean_object* v_bs_x27_4254_; lean_object* v___x_4255_; size_t v___x_4256_; size_t v___x_4257_; lean_object* v___x_4258_; 
v_v_4252_ = lean_array_uget(v_bs_4250_, v_i_4249_);
v___x_4253_ = lean_unsigned_to_nat(0u);
v_bs_x27_4254_ = lean_array_uset(v_bs_4250_, v_i_4249_, v___x_4253_);
v___x_4255_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(v_v_4252_);
v___x_4256_ = ((size_t)1ULL);
v___x_4257_ = lean_usize_add(v_i_4249_, v___x_4256_);
v___x_4258_ = lean_array_uset(v_bs_x27_4254_, v_i_4249_, v___x_4255_);
v_i_4249_ = v___x_4257_;
v_bs_4250_ = v___x_4258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3___boxed(lean_object* v_sz_4260_, lean_object* v_i_4261_, lean_object* v_bs_4262_){
_start:
{
size_t v_sz_boxed_4263_; size_t v_i_boxed_4264_; lean_object* v_res_4265_; 
v_sz_boxed_4263_ = lean_unbox_usize(v_sz_4260_);
lean_dec(v_sz_4260_);
v_i_boxed_4264_ = lean_unbox_usize(v_i_4261_);
lean_dec(v_i_4261_);
v_res_4265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(v_sz_boxed_4263_, v_i_boxed_4264_, v_bs_4262_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(lean_object* v_as_4266_, size_t v_i_4267_, size_t v_stop_4268_, lean_object* v_b_4269_){
_start:
{
lean_object* v___y_4271_; uint8_t v___x_4275_; 
v___x_4275_ = lean_usize_dec_eq(v_i_4267_, v_stop_4268_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; lean_object* v___y_4278_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; 
v___x_4276_ = lean_unsigned_to_nat(0u);
v___x_4282_ = lean_array_uget_borrowed(v_as_4266_, v_i_4267_);
v___x_4283_ = lean_array_get_size(v___x_4282_);
v___x_4284_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4285_ = lean_nat_dec_lt(v___x_4276_, v___x_4283_);
if (v___x_4285_ == 0)
{
v___y_4278_ = v___x_4284_;
goto v___jp_4277_;
}
else
{
size_t v___x_4286_; size_t v___x_4287_; lean_object* v___x_4288_; 
v___x_4286_ = ((size_t)0ULL);
v___x_4287_ = lean_usize_of_nat(v___x_4283_);
v___x_4288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v___x_4282_, v___x_4286_, v___x_4287_, v___x_4284_);
v___y_4278_ = v___x_4288_;
goto v___jp_4277_;
}
v___jp_4277_:
{
lean_object* v___x_4279_; uint8_t v___x_4280_; 
v___x_4279_ = lean_array_get_size(v___y_4278_);
v___x_4280_ = lean_nat_dec_eq(v___x_4279_, v___x_4276_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_array_push(v_b_4269_, v___y_4278_);
v___y_4271_ = v___x_4281_;
goto v___jp_4270_;
}
else
{
lean_dec_ref(v___y_4278_);
v___y_4271_ = v_b_4269_;
goto v___jp_4270_;
}
}
}
else
{
return v_b_4269_;
}
v___jp_4270_:
{
size_t v___x_4272_; size_t v___x_4273_; 
v___x_4272_ = ((size_t)1ULL);
v___x_4273_ = lean_usize_add(v_i_4267_, v___x_4272_);
v_i_4267_ = v___x_4273_;
v_b_4269_ = v___y_4271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1___boxed(lean_object* v_as_4289_, lean_object* v_i_4290_, lean_object* v_stop_4291_, lean_object* v_b_4292_){
_start:
{
size_t v_i_boxed_4293_; size_t v_stop_boxed_4294_; lean_object* v_res_4295_; 
v_i_boxed_4293_ = lean_unbox_usize(v_i_4290_);
lean_dec(v_i_4290_);
v_stop_boxed_4294_ = lean_unbox_usize(v_stop_4291_);
lean_dec(v_stop_4291_);
v_res_4295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4289_, v_i_boxed_4293_, v_stop_boxed_4294_, v_b_4292_);
lean_dec_ref(v_as_4289_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(lean_object* v_as_4298_, lean_object* v_start_4299_, lean_object* v_stop_4300_){
_start:
{
lean_object* v___x_4301_; uint8_t v___x_4302_; 
v___x_4301_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0));
v___x_4302_ = lean_nat_dec_lt(v_start_4299_, v_stop_4300_);
if (v___x_4302_ == 0)
{
return v___x_4301_;
}
else
{
lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4303_ = lean_array_get_size(v_as_4298_);
v___x_4304_ = lean_nat_dec_le(v_stop_4300_, v___x_4303_);
if (v___x_4304_ == 0)
{
uint8_t v___x_4305_; 
v___x_4305_ = lean_nat_dec_lt(v_start_4299_, v___x_4303_);
if (v___x_4305_ == 0)
{
return v___x_4301_;
}
else
{
size_t v___x_4306_; size_t v___x_4307_; lean_object* v___x_4308_; 
v___x_4306_ = lean_usize_of_nat(v_start_4299_);
v___x_4307_ = lean_usize_of_nat(v___x_4303_);
v___x_4308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4298_, v___x_4306_, v___x_4307_, v___x_4301_);
return v___x_4308_;
}
}
else
{
size_t v___x_4309_; size_t v___x_4310_; lean_object* v___x_4311_; 
v___x_4309_ = lean_usize_of_nat(v_start_4299_);
v___x_4310_ = lean_usize_of_nat(v_stop_4300_);
v___x_4311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4298_, v___x_4309_, v___x_4310_, v___x_4301_);
return v___x_4311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___boxed(lean_object* v_as_4312_, lean_object* v_start_4313_, lean_object* v_stop_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v_as_4312_, v_start_4313_, v_stop_4314_);
lean_dec(v_stop_4314_);
lean_dec(v_start_4313_);
lean_dec_ref(v_as_4312_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(lean_object* v_as_4316_, size_t v_i_4317_, size_t v_stop_4318_, lean_object* v_b_4319_){
_start:
{
lean_object* v___y_4321_; uint8_t v___x_4325_; 
v___x_4325_ = lean_usize_dec_eq(v_i_4317_, v_stop_4318_);
if (v___x_4325_ == 0)
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v_group_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4326_ = lean_unsigned_to_nat(0u);
v___x_4327_ = lean_array_uget_borrowed(v_as_4316_, v_i_4317_);
v___x_4328_ = lean_array_get_size(v___x_4327_);
v_group_4329_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v___x_4327_, v___x_4326_, v___x_4328_);
v___x_4330_ = lean_array_get_size(v_group_4329_);
v___x_4331_ = lean_nat_dec_eq(v___x_4330_, v___x_4326_);
if (v___x_4331_ == 0)
{
lean_object* v___x_4332_; 
v___x_4332_ = lean_array_push(v_b_4319_, v_group_4329_);
v___y_4321_ = v___x_4332_;
goto v___jp_4320_;
}
else
{
lean_dec_ref(v_group_4329_);
v___y_4321_ = v_b_4319_;
goto v___jp_4320_;
}
}
else
{
return v_b_4319_;
}
v___jp_4320_:
{
size_t v___x_4322_; size_t v___x_4323_; 
v___x_4322_ = ((size_t)1ULL);
v___x_4323_ = lean_usize_add(v_i_4317_, v___x_4322_);
v_i_4317_ = v___x_4323_;
v_b_4319_ = v___y_4321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3___boxed(lean_object* v_as_4333_, lean_object* v_i_4334_, lean_object* v_stop_4335_, lean_object* v_b_4336_){
_start:
{
size_t v_i_boxed_4337_; size_t v_stop_boxed_4338_; lean_object* v_res_4339_; 
v_i_boxed_4337_ = lean_unbox_usize(v_i_4334_);
lean_dec(v_i_4334_);
v_stop_boxed_4338_ = lean_unbox_usize(v_stop_4335_);
lean_dec(v_stop_4335_);
v_res_4339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4333_, v_i_boxed_4337_, v_stop_boxed_4338_, v_b_4336_);
lean_dec_ref(v_as_4333_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(lean_object* v_as_4342_, lean_object* v_start_4343_, lean_object* v_stop_4344_){
_start:
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4345_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___closed__0));
v___x_4346_ = lean_nat_dec_lt(v_start_4343_, v_stop_4344_);
if (v___x_4346_ == 0)
{
return v___x_4345_;
}
else
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = lean_array_get_size(v_as_4342_);
v___x_4348_ = lean_nat_dec_le(v_stop_4344_, v___x_4347_);
if (v___x_4348_ == 0)
{
uint8_t v___x_4349_; 
v___x_4349_ = lean_nat_dec_lt(v_start_4343_, v___x_4347_);
if (v___x_4349_ == 0)
{
return v___x_4345_;
}
else
{
size_t v___x_4350_; size_t v___x_4351_; lean_object* v___x_4352_; 
v___x_4350_ = lean_usize_of_nat(v_start_4343_);
v___x_4351_ = lean_usize_of_nat(v___x_4347_);
v___x_4352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4342_, v___x_4350_, v___x_4351_, v___x_4345_);
return v___x_4352_;
}
}
else
{
size_t v___x_4353_; size_t v___x_4354_; lean_object* v___x_4355_; 
v___x_4353_ = lean_usize_of_nat(v_start_4343_);
v___x_4354_ = lean_usize_of_nat(v_stop_4344_);
v___x_4355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4342_, v___x_4353_, v___x_4354_, v___x_4345_);
return v___x_4355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___boxed(lean_object* v_as_4356_, lean_object* v_start_4357_, lean_object* v_stop_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_as_4356_, v_start_4357_, v_stop_4358_);
lean_dec(v_stop_4358_);
lean_dec(v_start_4357_);
lean_dec_ref(v_as_4356_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object* v_lvals_4360_, lean_object* v_binderGroups_4361_, lean_object* v_typeAscriptionTk_4362_, lean_object* v_type_4363_, lean_object* v_kind_4364_, lean_object* v_lvalsLayout_4365_){
_start:
{
lean_object* v___y_4367_; uint8_t v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; uint8_t v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___x_4392_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4405_; lean_object* v___x_4415_; lean_object* v___x_4416_; uint8_t v___x_4417_; 
v___x_4392_ = lean_unsigned_to_nat(0u);
v___x_4415_ = lean_array_get_size(v_lvals_4360_);
v___x_4416_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4417_ = lean_nat_dec_lt(v___x_4392_, v___x_4415_);
if (v___x_4417_ == 0)
{
v___y_4405_ = v___x_4416_;
goto v___jp_4404_;
}
else
{
size_t v___x_4418_; size_t v___x_4419_; lean_object* v___x_4420_; 
v___x_4418_ = ((size_t)0ULL);
v___x_4419_ = lean_usize_of_nat(v___x_4415_);
v___x_4420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_lvals_4360_, v___x_4418_, v___x_4419_, v___x_4416_);
v___y_4405_ = v___x_4420_;
goto v___jp_4404_;
}
v___jp_4366_:
{
size_t v_sz_4371_; size_t v___x_4372_; lean_object* v___x_4373_; lean_object* v_binderGroups_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v_sz_4371_ = lean_array_size(v___y_4369_);
v___x_4372_ = ((size_t)0ULL);
v___x_4373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(v_sz_4371_, v___x_4372_, v___y_4369_);
v_binderGroups_4374_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4373_, v___y_4368_);
lean_dec_ref(v___x_4373_);
v___x_4375_ = lean_apply_1(v_lvalsLayout_4365_, v___y_4367_);
v___x_4376_ = lean_unsigned_to_nat(2u);
v___x_4377_ = lean_mk_empty_array_with_capacity(v___x_4376_);
v___x_4378_ = lean_array_push(v___x_4377_, v___x_4375_);
v___x_4379_ = lean_array_push(v___x_4378_, v_binderGroups_4374_);
v___x_4380_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4379_, v___y_4368_);
lean_dec_ref(v___x_4379_);
v___x_4381_ = l_Lean_Fmt_Layouts_typeAscription(v___x_4380_, v_typeAscriptionTk_4362_, v_type_4363_, v___y_4370_);
lean_dec_ref(v___y_4370_);
v___x_4382_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4381_);
return v___x_4382_;
}
v___jp_4383_:
{
if (lean_obj_tag(v_kind_4364_) == 0)
{
uint8_t v_respectPseudoAlignment_4387_; uint8_t v___x_4388_; lean_object* v___x_4389_; 
v_respectPseudoAlignment_4387_ = lean_ctor_get_uint8(v_kind_4364_, 0);
v___x_4388_ = 0;
v___x_4389_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4389_, 0, v___x_4388_);
lean_ctor_set_uint8(v___x_4389_, 1, v___x_4388_);
lean_ctor_set_uint8(v___x_4389_, 2, v___y_4384_);
lean_ctor_set_uint8(v___x_4389_, 3, v_respectPseudoAlignment_4387_);
v___y_4367_ = v___y_4386_;
v___y_4368_ = v___y_4384_;
v___y_4369_ = v___y_4385_;
v___y_4370_ = v___x_4389_;
goto v___jp_4366_;
}
else
{
uint8_t v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = 0;
v___x_4391_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_4391_, 0, v___x_4390_);
lean_ctor_set_uint8(v___x_4391_, 1, v___x_4390_);
lean_ctor_set_uint8(v___x_4391_, 2, v___y_4384_);
lean_ctor_set_uint8(v___x_4391_, 3, v___x_4390_);
lean_ctor_set_uint8(v___x_4391_, 4, v___x_4390_);
v___y_4367_ = v___y_4386_;
v___y_4368_ = v___y_4384_;
v___y_4369_ = v___y_4385_;
v___y_4370_ = v___x_4391_;
goto v___jp_4366_;
}
}
v___jp_4393_:
{
uint8_t v___x_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4396_ = 1;
v___x_4397_ = lean_array_get_size(v___y_4394_);
v___x_4398_ = lean_nat_dec_lt(v___x_4392_, v___x_4397_);
if (v___x_4398_ == 0)
{
v___y_4384_ = v___x_4396_;
v___y_4385_ = v___y_4395_;
v___y_4386_ = v___y_4394_;
goto v___jp_4383_;
}
else
{
lean_object* v_v_4399_; lean_object* v___x_4400_; lean_object* v_xs_x27_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v_v_4399_ = lean_array_fget(v___y_4394_, v___x_4392_);
v___x_4400_ = lean_box(0);
v_xs_x27_4401_ = lean_array_fset(v___y_4394_, v___x_4392_, v___x_4400_);
v___x_4402_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4399_);
v___x_4403_ = lean_array_fset(v_xs_x27_4401_, v___x_4392_, v___x_4402_);
v___y_4384_ = v___x_4396_;
v___y_4385_ = v___y_4395_;
v___y_4386_ = v___x_4403_;
goto v___jp_4383_;
}
}
v___jp_4404_:
{
lean_object* v___x_4406_; lean_object* v_binderGroups_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; uint8_t v___x_4410_; 
v___x_4406_ = lean_array_get_size(v_binderGroups_4361_);
v_binderGroups_4407_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_binderGroups_4361_, v___x_4392_, v___x_4406_);
v___x_4408_ = lean_array_get_size(v___y_4405_);
v___x_4409_ = lean_unsigned_to_nat(1u);
v___x_4410_ = lean_nat_dec_le(v___x_4408_, v___x_4409_);
if (v___x_4410_ == 0)
{
v___y_4394_ = v___y_4405_;
v___y_4395_ = v_binderGroups_4407_;
goto v___jp_4393_;
}
else
{
uint8_t v___x_4411_; 
v___x_4411_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_type_4363_);
if (v___x_4411_ == 0)
{
v___y_4394_ = v___y_4405_;
v___y_4395_ = v_binderGroups_4407_;
goto v___jp_4393_;
}
else
{
uint8_t v___x_4412_; 
v___x_4412_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_typeAscriptionTk_4362_);
if (v___x_4412_ == 0)
{
v___y_4394_ = v___y_4405_;
v___y_4395_ = v_binderGroups_4407_;
goto v___jp_4393_;
}
else
{
lean_object* v___x_4413_; uint8_t v___x_4414_; 
v___x_4413_ = lean_array_get_size(v_binderGroups_4407_);
v___x_4414_ = lean_nat_dec_eq(v___x_4413_, v___x_4392_);
if (v___x_4414_ == 0)
{
v___y_4394_ = v___y_4405_;
v___y_4395_ = v_binderGroups_4407_;
goto v___jp_4393_;
}
else
{
v___y_4384_ = v___x_4412_;
v___y_4385_ = v_binderGroups_4407_;
v___y_4386_ = v___y_4405_;
goto v___jp_4383_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object* v_lvals_4421_, lean_object* v_binderGroups_4422_, lean_object* v_typeAscriptionTk_4423_, lean_object* v_type_4424_, lean_object* v_kind_4425_, lean_object* v_lvalsLayout_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4421_, v_binderGroups_4422_, v_typeAscriptionTk_4423_, v_type_4424_, v_kind_4425_, v_lvalsLayout_4426_);
lean_dec(v_kind_4425_);
lean_dec_ref(v_binderGroups_4422_);
lean_dec_ref(v_lvals_4421_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(uint8_t v___x_4428_, lean_object* v_terms_4429_){
_start:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4429_, v___x_4428_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object* v___x_4431_, lean_object* v_terms_4432_){
_start:
{
uint8_t v___x_9__boxed_4433_; lean_object* v_res_4434_; 
v___x_9__boxed_4433_ = lean_unbox(v___x_4431_);
v_res_4434_ = l_Lean_Fmt_Layouts_localSignature___lam__0(v___x_9__boxed_4433_, v_terms_4432_);
lean_dec_ref(v_terms_4432_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object* v_lvals_4440_, lean_object* v_binderGroups_4441_, lean_object* v_typeAscriptionTk_4442_, lean_object* v_type_4443_){
_start:
{
lean_object* v___f_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___f_4444_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__0));
v___x_4445_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__1));
v___x_4446_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4440_, v_binderGroups_4441_, v_typeAscriptionTk_4442_, v_type_4443_, v___x_4445_, v___f_4444_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object* v_lvals_4447_, lean_object* v_binderGroups_4448_, lean_object* v_typeAscriptionTk_4449_, lean_object* v_type_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Lean_Fmt_Layouts_localSignature(v_lvals_4447_, v_binderGroups_4448_, v_typeAscriptionTk_4449_, v_type_4450_);
lean_dec_ref(v_binderGroups_4448_);
lean_dec_ref(v_lvals_4447_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0(lean_object* v_terms_4452_){
_start:
{
uint8_t v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = 1;
v___x_4454_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4452_, v___x_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0___boxed(lean_object* v_terms_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l_Lean_Fmt_Layouts_globalSignature___lam__0(v_terms_4455_);
lean_dec_ref(v_terms_4455_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object* v_lvals_4458_, lean_object* v_binderGroups_4459_, lean_object* v_typeAscriptionTk_4460_, lean_object* v_type_4461_){
_start:
{
lean_object* v___f_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___f_4462_ = ((lean_object*)(l_Lean_Fmt_Layouts_globalSignature___closed__0));
v___x_4463_ = lean_box(1);
v___x_4464_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4458_, v_binderGroups_4459_, v_typeAscriptionTk_4460_, v_type_4461_, v___x_4463_, v___f_4462_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object* v_lvals_4465_, lean_object* v_binderGroups_4466_, lean_object* v_typeAscriptionTk_4467_, lean_object* v_type_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Lean_Fmt_Layouts_globalSignature(v_lvals_4465_, v_binderGroups_4466_, v_typeAscriptionTk_4467_, v_type_4468_);
lean_dec_ref(v_binderGroups_4466_);
lean_dec_ref(v_lvals_4465_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object* v_signature_4470_, lean_object* v_separationTk_4471_, lean_object* v_body_4472_, uint8_t v_sticky_4473_){
_start:
{
lean_object* v___y_4475_; lean_object* v___y_4476_; uint8_t v___y_4477_; lean_object* v___y_4478_; uint8_t v___y_4479_; uint8_t v___y_4483_; lean_object* v___y_4484_; uint8_t v___x_4523_; 
v___x_4523_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_separationTk_4471_);
if (v___x_4523_ == 0)
{
goto v___jp_4507_;
}
else
{
uint8_t v___x_4524_; 
v___x_4524_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4472_);
if (v___x_4524_ == 0)
{
goto v___jp_4507_;
}
else
{
lean_inc_ref(v_signature_4470_);
v___y_4483_ = v___x_4523_;
v___y_4484_ = v_signature_4470_;
goto v___jp_4482_;
}
}
v___jp_4474_:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
lean_inc_ref(v___y_4475_);
v___x_4480_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___y_4476_, v___y_4475_, v_body_4472_, v___y_4479_);
v___x_4481_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_4478_, v___x_4480_, v___y_4477_);
return v___x_4481_;
}
v___jp_4482_:
{
lean_object* v_doc_4485_; 
v_doc_4485_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___y_4484_);
if (v_sticky_4473_ == 0)
{
lean_dec_ref(v_body_4472_);
lean_dec_ref(v_separationTk_4471_);
lean_dec_ref(v_signature_4470_);
return v_doc_4485_;
}
else
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v_lhs_4497_; lean_object* v___x_4498_; 
v___x_4486_ = l_Lean_Fmt_TaggedDoc_flattened(v_signature_4470_);
v___x_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
v___x_4488_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1);
v___x_4489_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4487_, v___x_4488_);
v___x_4490_ = lean_box(0);
v___x_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4491_, 0, v_separationTk_4471_);
v___x_4492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4490_);
lean_ctor_set(v___x_4492_, 1, v___x_4491_);
lean_ctor_set(v___x_4492_, 2, v___x_4490_);
v___x_4493_ = lean_unsigned_to_nat(2u);
v___x_4494_ = lean_mk_empty_array_with_capacity(v___x_4493_);
v___x_4495_ = lean_array_push(v___x_4494_, v___x_4489_);
v___x_4496_ = lean_array_push(v___x_4495_, v___x_4492_);
v_lhs_4497_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4496_);
lean_dec_ref(v___x_4496_);
lean_inc_ref(v_body_4472_);
v___x_4498_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_body_4472_);
if (lean_obj_tag(v___x_4498_) == 1)
{
lean_object* v_val_4499_; uint8_t v_kind_4500_; lean_object* v___x_4501_; 
v_val_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_val_4499_);
lean_dec_ref_known(v___x_4498_, 1);
v_kind_4500_ = lean_ctor_get_uint8(v_val_4499_, sizeof(void*)*1);
lean_dec(v_val_4499_);
v___x_4501_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
if (v_kind_4500_ == 1)
{
uint8_t v___x_4502_; 
v___x_4502_ = 0;
v___y_4475_ = v___x_4501_;
v___y_4476_ = v_lhs_4497_;
v___y_4477_ = v_kind_4500_;
v___y_4478_ = v_doc_4485_;
v___y_4479_ = v___x_4502_;
goto v___jp_4474_;
}
else
{
v___y_4475_ = v___x_4501_;
v___y_4476_ = v_lhs_4497_;
v___y_4477_ = v_kind_4500_;
v___y_4478_ = v_doc_4485_;
v___y_4479_ = v_sticky_4473_;
goto v___jp_4474_;
}
}
else
{
lean_object* v___x_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; lean_object* v___x_4506_; 
lean_dec(v___x_4498_);
v___x_4503_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4504_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4497_, v___x_4503_, v_body_4472_, v___y_4483_);
v___x_4505_ = 0;
v___x_4506_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4485_, v___x_4504_, v___x_4505_);
return v___x_4506_;
}
}
}
v___jp_4507_:
{
uint8_t v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v_lhs_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4508_ = 1;
lean_inc_ref(v_signature_4470_);
v___x_4509_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4470_);
v___x_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
v___x_4511_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__1);
v___x_4512_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4510_, v___x_4511_);
v___x_4513_ = lean_box(0);
lean_inc_ref(v_separationTk_4471_);
v___x_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4514_, 0, v_separationTk_4471_);
v___x_4515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4513_);
lean_ctor_set(v___x_4515_, 1, v___x_4514_);
lean_ctor_set(v___x_4515_, 2, v___x_4513_);
v___x_4516_ = lean_unsigned_to_nat(2u);
v___x_4517_ = lean_mk_empty_array_with_capacity(v___x_4516_);
v___x_4518_ = lean_array_push(v___x_4517_, v___x_4512_);
v___x_4519_ = lean_array_push(v___x_4518_, v___x_4515_);
v_lhs_4520_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4519_);
lean_dec_ref(v___x_4519_);
v___x_4521_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_body_4472_);
v___x_4522_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4520_, v___x_4521_, v_body_4472_, v___x_4508_);
v___y_4483_ = v___x_4508_;
v___y_4484_ = v___x_4522_;
goto v___jp_4482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object* v_signature_4525_, lean_object* v_separationTk_4526_, lean_object* v_body_4527_, lean_object* v_sticky_4528_){
_start:
{
uint8_t v_sticky_boxed_4529_; lean_object* v_res_4530_; 
v_sticky_boxed_4529_ = lean_unbox(v_sticky_4528_);
v_res_4530_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_signature_4525_, v_separationTk_4526_, v_body_4527_, v_sticky_boxed_4529_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object* v_signature_4531_, lean_object* v_matchAlts_4532_){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4533_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4531_);
v___x_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
v___x_4535_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4536_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4534_, v___x_4535_);
v___x_4537_ = lean_box(0);
v___x_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4538_, 0, v_matchAlts_4532_);
v___x_4539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4537_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
lean_ctor_set(v___x_4539_, 2, v___x_4537_);
v___x_4540_ = lean_unsigned_to_nat(2u);
v___x_4541_ = lean_mk_empty_array_with_capacity(v___x_4540_);
v___x_4542_ = lean_array_push(v___x_4541_, v___x_4536_);
v___x_4543_ = lean_array_push(v___x_4542_, v___x_4539_);
v___x_4544_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4543_);
lean_dec_ref(v___x_4543_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object* v_signature_4548_, lean_object* v_whereTk_4549_, lean_object* v_body_4550_){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4551_ = ((lean_object*)(l_Lean_Fmt_Layouts_whereDeclaration___closed__0));
v___x_4552_ = l_Lean_Fmt_Layouts_keywordSeparated(v_signature_4548_, v_whereTk_4549_, v_body_4550_, v___x_4551_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object* v_lbs_4554_, lean_object* v_lhses_4555_, lean_object* v_subBinderGroups_4556_, lean_object* v_typeAscriptionTk_x3f_4557_, lean_object* v_type_x3f_4558_, lean_object* v_colonEqTk_x3f_4559_, lean_object* v_default_x3f_4560_, lean_object* v_rbs_4561_, lean_object* v_kind_4562_){
_start:
{
lean_object* v_lbs_4563_; lean_object* v___x_4564_; lean_object* v_binderSignature_4565_; uint8_t v___x_4566_; lean_object* v_simpleBinder_4567_; lean_object* v_rbs_4568_; lean_object* v___x_4569_; 
v_lbs_4563_ = l_Lean_Fmt_Layouts_atomic(v_lbs_4554_);
v___x_4564_ = ((lean_object*)(l_Lean_Fmt_Layouts_binder___closed__0));
v_binderSignature_4565_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lhses_4555_, v_subBinderGroups_4556_, v_typeAscriptionTk_x3f_4557_, v_type_x3f_4558_, v_kind_4562_, v___x_4564_);
v___x_4566_ = 0;
v_simpleBinder_4567_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_binderSignature_4565_, v_colonEqTk_x3f_4559_, v_default_x3f_4560_, v___x_4566_);
v_rbs_4568_ = l_Lean_Fmt_Layouts_atomic(v_rbs_4561_);
v___x_4569_ = l_Lean_Fmt_Layouts_parens(v_lbs_4563_, v_simpleBinder_4567_, v_rbs_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder___boxed(lean_object* v_lbs_4570_, lean_object* v_lhses_4571_, lean_object* v_subBinderGroups_4572_, lean_object* v_typeAscriptionTk_x3f_4573_, lean_object* v_type_x3f_4574_, lean_object* v_colonEqTk_x3f_4575_, lean_object* v_default_x3f_4576_, lean_object* v_rbs_4577_, lean_object* v_kind_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l_Lean_Fmt_Layouts_binder(v_lbs_4570_, v_lhses_4571_, v_subBinderGroups_4572_, v_typeAscriptionTk_x3f_4573_, v_type_x3f_4574_, v_colonEqTk_x3f_4575_, v_default_x3f_4576_, v_rbs_4577_, v_kind_4578_);
lean_dec(v_kind_4578_);
lean_dec_ref(v_rbs_4577_);
lean_dec_ref(v_subBinderGroups_4572_);
lean_dec_ref(v_lhses_4571_);
lean_dec_ref(v_lbs_4570_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object* v_keywordTk_4583_, lean_object* v_config_4584_, lean_object* v_decl_4585_, uint8_t v_format_4586_){
_start:
{
lean_object* v___f_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v_signature_4593_; lean_object* v___y_4595_; 
v___f_4587_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0));
v___x_4588_ = lean_unsigned_to_nat(2u);
v___x_4589_ = lean_mk_empty_array_with_capacity(v___x_4588_);
lean_inc_ref(v___x_4589_);
v___x_4590_ = lean_array_push(v___x_4589_, v_keywordTk_4583_);
v___x_4591_ = lean_array_push(v___x_4590_, v_config_4584_);
v___x_4592_ = ((lean_object*)(l_Lean_Fmt_Layouts_letDecl___closed__0));
v_signature_4593_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4591_, v___x_4592_);
if (v_format_4586_ == 0)
{
lean_object* v___x_4607_; 
v___x_4607_ = l_Lean_Fmt_TaggedDoc_space;
v___y_4595_ = v___x_4607_;
goto v___jp_4594_;
}
else
{
lean_object* v___x_4608_; 
v___x_4608_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4595_ = v___x_4608_;
goto v___jp_4594_;
}
v___jp_4594_:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4596_, 0, v_signature_4593_);
lean_inc_ref(v___y_4595_);
v___x_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4597_, 0, v___y_4595_);
lean_ctor_set(v___x_4597_, 1, v___f_4587_);
v___x_4598_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4596_, v___x_4597_);
v___x_4599_ = lean_box(0);
v___x_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4600_, 0, v_decl_4585_);
v___x_4601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4599_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
lean_ctor_set(v___x_4601_, 2, v___x_4599_);
v___x_4602_ = lean_array_push(v___x_4589_, v___x_4598_);
v___x_4603_ = lean_array_push(v___x_4602_, v___x_4601_);
v___x_4604_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4603_);
lean_dec_ref(v___x_4603_);
v___x_4605_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4604_);
v___x_4606_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4605_);
return v___x_4606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl___boxed(lean_object* v_keywordTk_4609_, lean_object* v_config_4610_, lean_object* v_decl_4611_, lean_object* v_format_4612_){
_start:
{
uint8_t v_format_boxed_4613_; lean_object* v_res_4614_; 
v_format_boxed_4613_ = lean_unbox(v_format_4612_);
v_res_4614_ = l_Lean_Fmt_Layouts_letDecl(v_keywordTk_4609_, v_config_4610_, v_decl_4611_, v_format_boxed_4613_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(size_t v_sz_4615_, size_t v_i_4616_, lean_object* v_bs_4617_){
_start:
{
uint8_t v___x_4618_; 
v___x_4618_ = lean_usize_dec_lt(v_i_4616_, v_sz_4615_);
if (v___x_4618_ == 0)
{
return v_bs_4617_;
}
else
{
lean_object* v_v_4619_; lean_object* v_quantifier_4620_; lean_object* v_binderGroups_4621_; lean_object* v_typeAscriptionTk_x3f_4622_; lean_object* v_type_x3f_4623_; lean_object* v_separationTk_4624_; lean_object* v___x_4625_; lean_object* v_bs_x27_4626_; lean_object* v___x_4627_; lean_object* v_signature_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; lean_object* v___x_4635_; size_t v___x_4636_; size_t v___x_4637_; lean_object* v___x_4638_; 
v_v_4619_ = lean_array_uget_borrowed(v_bs_4617_, v_i_4616_);
v_quantifier_4620_ = lean_ctor_get(v_v_4619_, 0);
lean_inc_ref(v_quantifier_4620_);
v_binderGroups_4621_ = lean_ctor_get(v_v_4619_, 1);
lean_inc_ref(v_binderGroups_4621_);
v_typeAscriptionTk_x3f_4622_ = lean_ctor_get(v_v_4619_, 2);
lean_inc_ref(v_typeAscriptionTk_x3f_4622_);
v_type_x3f_4623_ = lean_ctor_get(v_v_4619_, 3);
lean_inc_ref(v_type_x3f_4623_);
v_separationTk_4624_ = lean_ctor_get(v_v_4619_, 4);
lean_inc_ref(v_separationTk_4624_);
v___x_4625_ = lean_unsigned_to_nat(0u);
v_bs_x27_4626_ = lean_array_uset(v_bs_4617_, v_i_4616_, v___x_4625_);
v___x_4627_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v_signature_4628_ = l_Lean_Fmt_Layouts_localSignature(v___x_4627_, v_binderGroups_4621_, v_typeAscriptionTk_x3f_4622_, v_type_x3f_4623_);
lean_dec_ref(v_binderGroups_4621_);
v___x_4629_ = lean_unsigned_to_nat(2u);
v___x_4630_ = lean_mk_empty_array_with_capacity(v___x_4629_);
v___x_4631_ = lean_array_push(v___x_4630_, v_signature_4628_);
v___x_4632_ = lean_array_push(v___x_4631_, v_separationTk_4624_);
v___x_4633_ = l_Lean_Fmt_Layouts_atomic(v___x_4632_);
lean_dec_ref(v___x_4632_);
v___x_4634_ = 2;
v___x_4635_ = l_Lean_Fmt_Layouts_prefixOperator(v_quantifier_4620_, v___x_4633_, v___x_4634_);
v___x_4636_ = ((size_t)1ULL);
v___x_4637_ = lean_usize_add(v_i_4616_, v___x_4636_);
v___x_4638_ = lean_array_uset(v_bs_x27_4626_, v_i_4616_, v___x_4635_);
v_i_4616_ = v___x_4637_;
v_bs_4617_ = v___x_4638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0___boxed(lean_object* v_sz_4640_, lean_object* v_i_4641_, lean_object* v_bs_4642_){
_start:
{
size_t v_sz_boxed_4643_; size_t v_i_boxed_4644_; lean_object* v_res_4645_; 
v_sz_boxed_4643_ = lean_unbox_usize(v_sz_4640_);
lean_dec(v_sz_4640_);
v_i_boxed_4644_ = lean_unbox_usize(v_i_4641_);
lean_dec(v_i_4641_);
v_res_4645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_boxed_4643_, v_i_boxed_4644_, v_bs_4642_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(size_t v_sz_4646_, size_t v_i_4647_, lean_object* v_bs_4648_){
_start:
{
uint8_t v___x_4649_; 
v___x_4649_ = lean_usize_dec_lt(v_i_4647_, v_sz_4646_);
if (v___x_4649_ == 0)
{
return v_bs_4648_;
}
else
{
lean_object* v_v_4650_; lean_object* v___x_4651_; lean_object* v_bs_x27_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; size_t v___x_4655_; size_t v___x_4656_; lean_object* v___x_4657_; 
v_v_4650_ = lean_array_uget(v_bs_4648_, v_i_4647_);
v___x_4651_ = lean_unsigned_to_nat(0u);
v_bs_x27_4652_ = lean_array_uset(v_bs_4648_, v_i_4647_, v___x_4651_);
v___x_4653_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4650_);
v___x_4654_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4654_, 0, v___x_4653_);
lean_ctor_set_uint8(v___x_4654_, sizeof(void*)*1, v___x_4649_);
v___x_4655_ = ((size_t)1ULL);
v___x_4656_ = lean_usize_add(v_i_4647_, v___x_4655_);
v___x_4657_ = lean_array_uset(v_bs_x27_4652_, v_i_4647_, v___x_4654_);
v_i_4647_ = v___x_4656_;
v_bs_4648_ = v___x_4657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1___boxed(lean_object* v_sz_4659_, lean_object* v_i_4660_, lean_object* v_bs_4661_){
_start:
{
size_t v_sz_boxed_4662_; size_t v_i_boxed_4663_; lean_object* v_res_4664_; 
v_sz_boxed_4662_ = lean_unbox_usize(v_sz_4659_);
lean_dec(v_sz_4659_);
v_i_boxed_4663_ = lean_unbox_usize(v_i_4660_);
lean_dec(v_i_4660_);
v_res_4664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_boxed_4662_, v_i_boxed_4663_, v_bs_4661_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_quantified(lean_object* v_quantifierHeads_4665_, lean_object* v_body_4666_){
_start:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; 
v___x_4667_ = lean_array_get_size(v_quantifierHeads_4665_);
v___x_4668_ = lean_unsigned_to_nat(0u);
v___x_4669_ = lean_nat_dec_eq(v___x_4667_, v___x_4668_);
if (v___x_4669_ == 0)
{
size_t v_sz_4670_; size_t v___x_4671_; lean_object* v_quantifierHeads_4672_; size_t v_sz_4673_; lean_object* v_quantifierHeads_4674_; lean_object* v___x_4675_; lean_object* v_components_4676_; lean_object* v___x_4677_; lean_object* v_quantifiers_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v_sz_4670_ = lean_array_size(v_quantifierHeads_4665_);
v___x_4671_ = ((size_t)0ULL);
v_quantifierHeads_4672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_4670_, v___x_4671_, v_quantifierHeads_4665_);
v_sz_4673_ = lean_array_size(v_quantifierHeads_4672_);
v_quantifierHeads_4674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_4673_, v___x_4671_, v_quantifierHeads_4672_);
v___x_4675_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4675_, 0, v_body_4666_);
lean_ctor_set_uint8(v___x_4675_, sizeof(void*)*1, v___x_4669_);
v_components_4676_ = lean_array_push(v_quantifierHeads_4674_, v___x_4675_);
v___x_4677_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_quantifiers_4678_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(v_components_4676_, v___x_4677_);
v___x_4679_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_quantifiers_4678_);
v___x_4680_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4679_);
return v___x_4680_;
}
else
{
lean_dec_ref(v_quantifierHeads_4665_);
return v_body_4666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_subtype(lean_object* v_lbTk_4684_, lean_object* v_lhs_4685_, lean_object* v_sepTk_4686_, lean_object* v_rhs_4687_, lean_object* v_rbTk_4688_, lean_object* v_format_4689_){
_start:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v_body_4697_; lean_object* v___x_4698_; 
v___x_4690_ = lean_unsigned_to_nat(3u);
v___x_4691_ = lean_mk_empty_array_with_capacity(v___x_4690_);
v___x_4692_ = lean_array_push(v___x_4691_, v_lhs_4685_);
v___x_4693_ = lean_array_push(v___x_4692_, v_sepTk_4686_);
v___x_4694_ = lean_array_push(v___x_4693_, v_rhs_4687_);
v___x_4695_ = ((lean_object*)(l_Lean_Fmt_Layouts_subtype___closed__0));
v___x_4696_ = l_Lean_Fmt_Layouts_infixOperator(v___x_4694_, v___x_4695_);
v_body_4697_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4696_);
v___x_4698_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_4684_, v_body_4697_, v_rbTk_4688_, v_format_4689_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(lean_object* v_tk_4699_, lean_object* v_block_4700_, uint8_t v_allowFlattening_4701_){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; 
v___x_4702_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4703_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_tk_4699_, v___x_4702_, v_block_4700_, v_allowFlattening_4701_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken___boxed(lean_object* v_tk_4704_, lean_object* v_block_4705_, lean_object* v_allowFlattening_4706_){
_start:
{
uint8_t v_allowFlattening_boxed_4707_; lean_object* v_res_4708_; 
v_allowFlattening_boxed_4707_ = lean_unbox(v_allowFlattening_4706_);
v_res_4708_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_tk_4704_, v_block_4705_, v_allowFlattening_boxed_4707_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(uint8_t v_allowFlattening_4709_, size_t v_sz_4710_, size_t v_i_4711_, lean_object* v_bs_4712_){
_start:
{
uint8_t v___x_4713_; 
v___x_4713_ = lean_usize_dec_lt(v_i_4711_, v_sz_4710_);
if (v___x_4713_ == 0)
{
return v_bs_4712_;
}
else
{
lean_object* v_v_4714_; lean_object* v_elseTk_4715_; lean_object* v_ifTk_4716_; lean_object* v_cond_4717_; lean_object* v_thenTk_4718_; lean_object* v_thenBlock_4719_; lean_object* v___x_4720_; lean_object* v_bs_x27_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v_tk_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; lean_object* v___x_4730_; lean_object* v_head_4731_; lean_object* v_then_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v_trailingThen_4742_; size_t v___x_4743_; size_t v___x_4744_; lean_object* v___x_4745_; 
v_v_4714_ = lean_array_uget_borrowed(v_bs_4712_, v_i_4711_);
v_elseTk_4715_ = lean_ctor_get(v_v_4714_, 0);
lean_inc_ref(v_elseTk_4715_);
v_ifTk_4716_ = lean_ctor_get(v_v_4714_, 1);
lean_inc_ref(v_ifTk_4716_);
v_cond_4717_ = lean_ctor_get(v_v_4714_, 2);
lean_inc_ref(v_cond_4717_);
v_thenTk_4718_ = lean_ctor_get(v_v_4714_, 3);
lean_inc_ref(v_thenTk_4718_);
v_thenBlock_4719_ = lean_ctor_get(v_v_4714_, 4);
lean_inc_ref(v_thenBlock_4719_);
v___x_4720_ = lean_unsigned_to_nat(0u);
v_bs_x27_4721_ = lean_array_uset(v_bs_4712_, v_i_4711_, v___x_4720_);
v___x_4722_ = lean_unsigned_to_nat(2u);
v___x_4723_ = lean_mk_empty_array_with_capacity(v___x_4722_);
lean_inc_ref_n(v___x_4723_, 2);
v___x_4724_ = lean_array_push(v___x_4723_, v_elseTk_4715_);
v___x_4725_ = lean_array_push(v___x_4724_, v_ifTk_4716_);
v_tk_4726_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4725_);
lean_dec_ref(v___x_4725_);
v___x_4727_ = lean_array_push(v___x_4723_, v_tk_4726_);
v___x_4728_ = lean_array_push(v___x_4727_, v_cond_4717_);
v___x_4729_ = 0;
v___x_4730_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4730_, 0, v___x_4713_);
lean_ctor_set_uint8(v___x_4730_, 1, v___x_4729_);
lean_ctor_set_uint8(v___x_4730_, 2, v___x_4729_);
lean_ctor_set_uint8(v___x_4730_, 3, v___x_4729_);
v_head_4731_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4728_, v___x_4730_);
v_then_4732_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_thenTk_4718_, v_thenBlock_4719_, v_allowFlattening_4709_);
v___x_4733_ = l_Lean_Fmt_TaggedDoc_hardNested(v_head_4731_);
v___x_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
v___x_4735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4736_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4734_, v___x_4735_);
v___x_4737_ = lean_box(0);
v___x_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4738_, 0, v_then_4732_);
v___x_4739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4737_);
lean_ctor_set(v___x_4739_, 1, v___x_4738_);
lean_ctor_set(v___x_4739_, 2, v___x_4737_);
v___x_4740_ = lean_array_push(v___x_4723_, v___x_4736_);
v___x_4741_ = lean_array_push(v___x_4740_, v___x_4739_);
v_trailingThen_4742_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4741_);
lean_dec_ref(v___x_4741_);
v___x_4743_ = ((size_t)1ULL);
v___x_4744_ = lean_usize_add(v_i_4711_, v___x_4743_);
v___x_4745_ = lean_array_uset(v_bs_x27_4721_, v_i_4711_, v_trailingThen_4742_);
v_i_4711_ = v___x_4744_;
v_bs_4712_ = v___x_4745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0___boxed(lean_object* v_allowFlattening_4747_, lean_object* v_sz_4748_, lean_object* v_i_4749_, lean_object* v_bs_4750_){
_start:
{
uint8_t v_allowFlattening_boxed_4751_; size_t v_sz_boxed_4752_; size_t v_i_boxed_4753_; lean_object* v_res_4754_; 
v_allowFlattening_boxed_4751_ = lean_unbox(v_allowFlattening_4747_);
v_sz_boxed_4752_ = lean_unbox_usize(v_sz_4748_);
lean_dec(v_sz_4748_);
v_i_boxed_4753_ = lean_unbox_usize(v_i_4749_);
lean_dec(v_i_4749_);
v_res_4754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_boxed_4751_, v_sz_boxed_4752_, v_i_boxed_4753_, v_bs_4750_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(lean_object* v_elseIfs_4755_, lean_object* v_elseTk_4756_, lean_object* v_elseBlock_4757_, uint8_t v_allowFlattening_4758_){
_start:
{
size_t v_sz_4759_; size_t v___x_4760_; lean_object* v_elseIfs_4761_; lean_object* v_else_4762_; lean_object* v_blocks_4763_; size_t v_sz_4764_; lean_object* v_blocks_4765_; lean_object* v_conditional_4766_; lean_object* v___x_4767_; 
v_sz_4759_ = lean_array_size(v_elseIfs_4755_);
v___x_4760_ = ((size_t)0ULL);
v_elseIfs_4761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_4758_, v_sz_4759_, v___x_4760_, v_elseIfs_4755_);
v_else_4762_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_elseTk_4756_, v_elseBlock_4757_, v_allowFlattening_4758_);
v_blocks_4763_ = lean_array_push(v_elseIfs_4761_, v_else_4762_);
v_sz_4764_ = lean_array_size(v_blocks_4763_);
v_blocks_4765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_4764_, v___x_4760_, v_blocks_4763_);
v_conditional_4766_ = l_Lean_Fmt_TaggedDoc_combine(v_blocks_4765_);
lean_dec_ref(v_blocks_4765_);
v___x_4767_ = l_Lean_Fmt_TaggedDoc_aligned(v_conditional_4766_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk___boxed(lean_object* v_elseIfs_4768_, lean_object* v_elseTk_4769_, lean_object* v_elseBlock_4770_, lean_object* v_allowFlattening_4771_){
_start:
{
uint8_t v_allowFlattening_boxed_4772_; lean_object* v_res_4773_; 
v_allowFlattening_boxed_4772_ = lean_unbox(v_allowFlattening_4771_);
v_res_4773_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4768_, v_elseTk_4769_, v_elseBlock_4770_, v_allowFlattening_boxed_4772_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(lean_object* v_as_4774_, size_t v_i_4775_, size_t v_stop_4776_, lean_object* v_b_4777_){
_start:
{
lean_object* v___y_4779_; uint8_t v___x_4783_; 
v___x_4783_ = lean_usize_dec_eq(v_i_4775_, v_stop_4776_);
if (v___x_4783_ == 0)
{
lean_object* v___x_4784_; lean_object* v_elseTk_4785_; lean_object* v_ifTk_4786_; lean_object* v_cond_4787_; lean_object* v_thenTk_4788_; lean_object* v_thenBlock_4789_; uint8_t v___x_4790_; 
v___x_4784_ = lean_array_uget_borrowed(v_as_4774_, v_i_4775_);
v_elseTk_4785_ = lean_ctor_get(v___x_4784_, 0);
v_ifTk_4786_ = lean_ctor_get(v___x_4784_, 1);
v_cond_4787_ = lean_ctor_get(v___x_4784_, 2);
v_thenTk_4788_ = lean_ctor_get(v___x_4784_, 3);
v_thenBlock_4789_ = lean_ctor_get(v___x_4784_, 4);
v___x_4790_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_elseTk_4785_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; 
lean_inc(v___x_4784_);
v___x_4791_ = lean_array_push(v_b_4777_, v___x_4784_);
v___y_4779_ = v___x_4791_;
goto v___jp_4778_;
}
else
{
uint8_t v___x_4792_; 
v___x_4792_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_ifTk_4786_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; 
lean_inc(v___x_4784_);
v___x_4793_ = lean_array_push(v_b_4777_, v___x_4784_);
v___y_4779_ = v___x_4793_;
goto v___jp_4778_;
}
else
{
uint8_t v___x_4794_; 
v___x_4794_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_cond_4787_);
if (v___x_4794_ == 0)
{
lean_object* v___x_4795_; 
lean_inc(v___x_4784_);
v___x_4795_ = lean_array_push(v_b_4777_, v___x_4784_);
v___y_4779_ = v___x_4795_;
goto v___jp_4778_;
}
else
{
uint8_t v___x_4796_; 
v___x_4796_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenTk_4788_);
if (v___x_4796_ == 0)
{
lean_object* v___x_4797_; 
lean_inc(v___x_4784_);
v___x_4797_ = lean_array_push(v_b_4777_, v___x_4784_);
v___y_4779_ = v___x_4797_;
goto v___jp_4778_;
}
else
{
uint8_t v___x_4798_; 
v___x_4798_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenBlock_4789_);
if (v___x_4798_ == 0)
{
lean_object* v___x_4799_; 
lean_inc(v___x_4784_);
v___x_4799_ = lean_array_push(v_b_4777_, v___x_4784_);
v___y_4779_ = v___x_4799_;
goto v___jp_4778_;
}
else
{
v___y_4779_ = v_b_4777_;
goto v___jp_4778_;
}
}
}
}
}
}
else
{
return v_b_4777_;
}
v___jp_4778_:
{
size_t v___x_4780_; size_t v___x_4781_; 
v___x_4780_ = ((size_t)1ULL);
v___x_4781_ = lean_usize_add(v_i_4775_, v___x_4780_);
v_i_4775_ = v___x_4781_;
v_b_4777_ = v___y_4779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0___boxed(lean_object* v_as_4800_, lean_object* v_i_4801_, lean_object* v_stop_4802_, lean_object* v_b_4803_){
_start:
{
size_t v_i_boxed_4804_; size_t v_stop_boxed_4805_; lean_object* v_res_4806_; 
v_i_boxed_4804_ = lean_unbox_usize(v_i_4801_);
lean_dec(v_i_4801_);
v_stop_boxed_4805_ = lean_unbox_usize(v_stop_4802_);
lean_dec(v_stop_4802_);
v_res_4806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_as_4800_, v_i_boxed_4804_, v_stop_boxed_4805_, v_b_4803_);
lean_dec_ref(v_as_4800_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional(lean_object* v_ifTk_4809_, lean_object* v_cond_4810_, lean_object* v_thenTk_4811_, lean_object* v_thenBlock_4812_, lean_object* v_elseIfs_4813_, lean_object* v_elseTk_4814_, lean_object* v_elseBlock_4815_, uint8_t v_allowFlattening_4816_){
_start:
{
lean_object* v___y_4818_; uint8_t v___y_4819_; lean_object* v___y_4838_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; uint8_t v___x_4845_; 
v___x_4842_ = lean_unsigned_to_nat(0u);
v___x_4843_ = lean_array_get_size(v_elseIfs_4813_);
v___x_4844_ = ((lean_object*)(l_Lean_Fmt_Layouts_conditional___closed__0));
v___x_4845_ = lean_nat_dec_lt(v___x_4842_, v___x_4843_);
if (v___x_4845_ == 0)
{
v___y_4838_ = v___x_4844_;
goto v___jp_4837_;
}
else
{
size_t v___x_4846_; size_t v___x_4847_; lean_object* v___x_4848_; 
v___x_4846_ = ((size_t)0ULL);
v___x_4847_ = lean_usize_of_nat(v___x_4843_);
v___x_4848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_4813_, v___x_4846_, v___x_4847_, v___x_4844_);
v___y_4838_ = v___x_4848_;
goto v___jp_4837_;
}
v___jp_4817_:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v_elseIfs_4825_; 
v___x_4820_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_4821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
lean_ctor_set(v___x_4821_, 1, v_ifTk_4809_);
lean_ctor_set(v___x_4821_, 2, v_cond_4810_);
lean_ctor_set(v___x_4821_, 3, v_thenTk_4811_);
lean_ctor_set(v___x_4821_, 4, v_thenBlock_4812_);
v___x_4822_ = lean_unsigned_to_nat(1u);
v___x_4823_ = lean_mk_empty_array_with_capacity(v___x_4822_);
v___x_4824_ = lean_array_push(v___x_4823_, v___x_4821_);
v_elseIfs_4825_ = l_Array_append___redArg(v___x_4824_, v___y_4818_);
lean_dec_ref(v___y_4818_);
if (v___y_4819_ == 0)
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4825_, v_elseTk_4814_, v_elseBlock_4815_, v___y_4819_);
v___x_4827_ = l_Lean_Fmt_TaggedDoc_unflattenable(v___x_4826_);
return v___x_4827_;
}
else
{
lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
lean_inc_ref(v_elseBlock_4815_);
lean_inc_ref(v_elseTk_4814_);
lean_inc_ref(v_elseIfs_4825_);
v___x_4828_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4825_, v_elseTk_4814_, v_elseBlock_4815_, v___y_4819_);
v___x_4829_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_4828_);
v___x_4830_ = 0;
v___x_4831_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4825_, v_elseTk_4814_, v_elseBlock_4815_, v___x_4830_);
v___x_4832_ = lean_unsigned_to_nat(2u);
v___x_4833_ = lean_mk_empty_array_with_capacity(v___x_4832_);
v___x_4834_ = lean_array_push(v___x_4833_, v___x_4829_);
v___x_4835_ = lean_array_push(v___x_4834_, v___x_4831_);
v___x_4836_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_4835_);
return v___x_4836_;
}
}
v___jp_4837_:
{
if (v_allowFlattening_4816_ == 0)
{
v___y_4818_ = v___y_4838_;
v___y_4819_ = v_allowFlattening_4816_;
goto v___jp_4817_;
}
else
{
lean_object* v___x_4839_; lean_object* v___x_4840_; uint8_t v___x_4841_; 
v___x_4839_ = lean_array_get_size(v___y_4838_);
v___x_4840_ = lean_unsigned_to_nat(0u);
v___x_4841_ = lean_nat_dec_eq(v___x_4839_, v___x_4840_);
v___y_4818_ = v___y_4838_;
v___y_4819_ = v___x_4841_;
goto v___jp_4817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional___boxed(lean_object* v_ifTk_4849_, lean_object* v_cond_4850_, lean_object* v_thenTk_4851_, lean_object* v_thenBlock_4852_, lean_object* v_elseIfs_4853_, lean_object* v_elseTk_4854_, lean_object* v_elseBlock_4855_, lean_object* v_allowFlattening_4856_){
_start:
{
uint8_t v_allowFlattening_boxed_4857_; lean_object* v_res_4858_; 
v_allowFlattening_boxed_4857_ = lean_unbox(v_allowFlattening_4856_);
v_res_4858_ = l_Lean_Fmt_Layouts_conditional(v_ifTk_4849_, v_cond_4850_, v_thenTk_4851_, v_thenBlock_4852_, v_elseIfs_4853_, v_elseTk_4854_, v_elseBlock_4855_, v_allowFlattening_boxed_4857_);
lean_dec_ref(v_elseIfs_4853_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_strLit(lean_object* v_prefix_4859_, lean_object* v_str_4860_){
_start:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; uint8_t v___x_4866_; lean_object* v___x_4867_; 
v___x_4861_ = lean_unsigned_to_nat(2u);
v___x_4862_ = lean_mk_empty_array_with_capacity(v___x_4861_);
v___x_4863_ = lean_array_push(v___x_4862_, v_prefix_4859_);
v___x_4864_ = lean_array_push(v___x_4863_, v_str_4860_);
v___x_4865_ = l_Lean_Fmt_Layouts_atomic(v___x_4864_);
lean_dec_ref(v___x_4864_);
v___x_4866_ = 0;
v___x_4867_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_4865_, v___x_4866_);
return v___x_4867_;
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
