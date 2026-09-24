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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_keywordSeparated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_keywordSeparated___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_keywordSeparated___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_keywordSeparated___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx(v_x_8_);
lean_dec(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
if (lean_obj_tag(v_t_10_) == 3)
{
uint8_t v_allowFlattening_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_allowFlattening_12_ = lean_ctor_get_uint8(v_t_10_, 0);
v___x_13_ = lean_box(v_allowFlattening_12_);
v___x_14_ = lean_apply_1(v_k_11_, v___x_13_);
return v___x_14_;
}
else
{
return v_k_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg___boxed(lean_object* v_t_15_, lean_object* v_k_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_15_, v_k_16_);
lean_dec(v_t_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_t_26_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(lean_object* v_t_30_, lean_object* v_join_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_30_, v_join_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg___boxed(lean_object* v_t_33_, lean_object* v_join_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(v_t_33_, v_join_34_);
lean_dec(v_t_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_join_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_37_, v_join_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___boxed(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_join_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(v_motive_41_, v_t_42_, v_h_43_, v_join_44_);
lean_dec(v_t_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(lean_object* v_t_46_, lean_object* v_joinUsingSpace_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_46_, v_joinUsingSpace_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg___boxed(lean_object* v_t_49_, lean_object* v_joinUsingSpace_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(v_t_49_, v_joinUsingSpace_50_);
lean_dec(v_t_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_joinUsingSpace_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_53_, v_joinUsingSpace_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___boxed(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_joinUsingSpace_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(v_motive_57_, v_t_58_, v_h_59_, v_joinUsingSpace_60_);
lean_dec(v_t_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg(lean_object* v_t_62_, lean_object* v_joinUsingSoftSpace_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_62_, v_joinUsingSoftSpace_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg___boxed(lean_object* v_t_65_, lean_object* v_joinUsingSoftSpace_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg(v_t_65_, v_joinUsingSoftSpace_66_);
lean_dec(v_t_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_joinUsingSoftSpace_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_69_, v_joinUsingSoftSpace_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___boxed(lean_object* v_motive_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_joinUsingSoftSpace_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim(v_motive_73_, v_t_74_, v_h_75_, v_joinUsingSoftSpace_76_);
lean_dec(v_t_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(lean_object* v_t_78_, lean_object* v_joinUsingNl_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_78_, v_joinUsingNl_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg___boxed(lean_object* v_t_81_, lean_object* v_joinUsingNl_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(v_t_81_, v_joinUsingNl_82_);
lean_dec(v_t_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_joinUsingNl_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_85_, v_joinUsingNl_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___boxed(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_joinUsingNl_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(v_motive_89_, v_t_90_, v_h_91_, v_joinUsingNl_92_);
lean_dec(v_t_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(lean_object* v_t_94_, lean_object* v_joinUsingBreak_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_94_, v_joinUsingBreak_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg___boxed(lean_object* v_t_97_, lean_object* v_joinUsingBreak_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(v_t_97_, v_joinUsingBreak_98_);
lean_dec(v_t_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_joinUsingBreak_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_101_, v_joinUsingBreak_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___boxed(lean_object* v_motive_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_joinUsingBreak_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(v_motive_105_, v_t_106_, v_h_107_, v_joinUsingBreak_108_);
lean_dec(v_t_106_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(lean_object* v_t_110_, lean_object* v_fill_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_110_, v_fill_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg___boxed(lean_object* v_t_113_, lean_object* v_fill_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(v_t_113_, v_fill_114_);
lean_dec(v_t_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_fill_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_117_, v_fill_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___boxed(lean_object* v_motive_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_fill_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(v_motive_121_, v_t_122_, v_h_123_, v_fill_124_);
lean_dec(v_t_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(lean_object* v___y_126_){
_start:
{
lean_inc_ref(v___y_126_);
return v___y_126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0___boxed(lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(v___y_127_);
lean_dec_ref(v___y_127_);
return v_res_128_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1(void){
_start:
{
lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___f_130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_131_ = l_Lean_Fmt_TaggedDoc_space;
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___f_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(size_t v_sz_133_, size_t v_i_134_, lean_object* v_bs_135_){
_start:
{
uint8_t v___x_136_; 
v___x_136_ = lean_usize_dec_lt(v_i_134_, v_sz_133_);
if (v___x_136_ == 0)
{
return v_bs_135_;
}
else
{
lean_object* v_v_137_; lean_object* v___x_138_; lean_object* v_bs_x27_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; 
v_v_137_ = lean_array_uget(v_bs_135_, v_i_134_);
v___x_138_ = lean_unsigned_to_nat(0u);
v_bs_x27_139_ = lean_array_uset(v_bs_135_, v_i_134_, v___x_138_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_v_137_);
v___x_141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_142_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_140_, v___x_141_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_add(v_i_134_, v___x_143_);
v___x_145_ = lean_array_uset(v_bs_x27_139_, v_i_134_, v___x_142_);
v_i_134_ = v___x_144_;
v_bs_135_ = v___x_145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___boxed(lean_object* v_sz_147_, lean_object* v_i_148_, lean_object* v_bs_149_){
_start:
{
size_t v_sz_boxed_150_; size_t v_i_boxed_151_; lean_object* v_res_152_; 
v_sz_boxed_150_ = lean_unbox_usize(v_sz_147_);
lean_dec(v_sz_147_);
v_i_boxed_151_ = lean_unbox_usize(v_i_148_);
lean_dec(v_i_148_);
v_res_152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(v_sz_boxed_150_, v_i_boxed_151_, v_bs_149_);
return v_res_152_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0(void){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___f_153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_154_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___f_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(size_t v_sz_156_, size_t v_i_157_, lean_object* v_bs_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_usize_dec_lt(v_i_157_, v_sz_156_);
if (v___x_159_ == 0)
{
return v_bs_158_;
}
else
{
lean_object* v_v_160_; lean_object* v___x_161_; lean_object* v_bs_x27_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v_v_160_ = lean_array_uget(v_bs_158_, v_i_157_);
v___x_161_ = lean_unsigned_to_nat(0u);
v_bs_x27_162_ = lean_array_uset(v_bs_158_, v_i_157_, v___x_161_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v_v_160_);
v___x_164_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0);
v___x_165_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_163_, v___x_164_);
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_add(v_i_157_, v___x_166_);
v___x_168_ = lean_array_uset(v_bs_x27_162_, v_i_157_, v___x_165_);
v_i_157_ = v___x_167_;
v_bs_158_ = v___x_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___boxed(lean_object* v_sz_170_, lean_object* v_i_171_, lean_object* v_bs_172_){
_start:
{
size_t v_sz_boxed_173_; size_t v_i_boxed_174_; lean_object* v_res_175_; 
v_sz_boxed_173_ = lean_unbox_usize(v_sz_170_);
lean_dec(v_sz_170_);
v_i_boxed_174_ = lean_unbox_usize(v_i_171_);
lean_dec(v_i_171_);
v_res_175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(v_sz_boxed_173_, v_i_boxed_174_, v_bs_172_);
return v_res_175_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0(void){
_start:
{
lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___f_176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_177_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___f_176_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(size_t v_sz_179_, size_t v_i_180_, lean_object* v_bs_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = lean_usize_dec_lt(v_i_180_, v_sz_179_);
if (v___x_182_ == 0)
{
return v_bs_181_;
}
else
{
lean_object* v_v_183_; lean_object* v___x_184_; lean_object* v_bs_x27_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; size_t v___x_189_; size_t v___x_190_; lean_object* v___x_191_; 
v_v_183_ = lean_array_uget(v_bs_181_, v_i_180_);
v___x_184_ = lean_unsigned_to_nat(0u);
v_bs_x27_185_ = lean_array_uset(v_bs_181_, v_i_180_, v___x_184_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_v_183_);
v___x_187_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0);
v___x_188_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_186_, v___x_187_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_add(v_i_180_, v___x_189_);
v___x_191_ = lean_array_uset(v_bs_x27_185_, v_i_180_, v___x_188_);
v_i_180_ = v___x_190_;
v_bs_181_ = v___x_191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___boxed(lean_object* v_sz_193_, lean_object* v_i_194_, lean_object* v_bs_195_){
_start:
{
size_t v_sz_boxed_196_; size_t v_i_boxed_197_; lean_object* v_res_198_; 
v_sz_boxed_196_ = lean_unbox_usize(v_sz_193_);
lean_dec(v_sz_193_);
v_i_boxed_197_ = lean_unbox_usize(v_i_194_);
lean_dec(v_i_194_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(v_sz_boxed_196_, v_i_boxed_197_, v_bs_195_);
return v_res_198_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0(void){
_start:
{
lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___f_199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_200_ = l_Lean_Fmt_TaggedDoc_break;
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___f_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(size_t v_sz_202_, size_t v_i_203_, lean_object* v_bs_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = lean_usize_dec_lt(v_i_203_, v_sz_202_);
if (v___x_205_ == 0)
{
return v_bs_204_;
}
else
{
lean_object* v_v_206_; lean_object* v___x_207_; lean_object* v_bs_x27_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; 
v_v_206_ = lean_array_uget(v_bs_204_, v_i_203_);
v___x_207_ = lean_unsigned_to_nat(0u);
v_bs_x27_208_ = lean_array_uset(v_bs_204_, v_i_203_, v___x_207_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v_v_206_);
v___x_210_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0);
v___x_211_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_209_, v___x_210_);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_add(v_i_203_, v___x_212_);
v___x_214_ = lean_array_uset(v_bs_x27_208_, v_i_203_, v___x_211_);
v_i_203_ = v___x_213_;
v_bs_204_ = v___x_214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___boxed(lean_object* v_sz_216_, lean_object* v_i_217_, lean_object* v_bs_218_){
_start:
{
size_t v_sz_boxed_219_; size_t v_i_boxed_220_; lean_object* v_res_221_; 
v_sz_boxed_219_ = lean_unbox_usize(v_sz_216_);
lean_dec(v_sz_216_);
v_i_boxed_220_ = lean_unbox_usize(v_i_217_);
lean_dec(v_i_217_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(v_sz_boxed_219_, v_i_boxed_220_, v_bs_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(lean_object* v_as_222_, size_t v_i_223_, size_t v_stop_224_, lean_object* v_b_225_){
_start:
{
lean_object* v___y_227_; uint8_t v___x_231_; 
v___x_231_ = lean_usize_dec_eq(v_i_223_, v_stop_224_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_array_uget_borrowed(v_as_222_, v_i_223_);
v___x_233_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
lean_inc(v___x_232_);
v___x_234_ = lean_array_push(v_b_225_, v___x_232_);
v___y_227_ = v___x_234_;
goto v___jp_226_;
}
else
{
v___y_227_ = v_b_225_;
goto v___jp_226_;
}
}
else
{
return v_b_225_;
}
v___jp_226_:
{
size_t v___x_228_; size_t v___x_229_; 
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_223_, v___x_228_);
v_i_223_ = v___x_229_;
v_b_225_ = v___y_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6___boxed(lean_object* v_as_235_, lean_object* v_i_236_, lean_object* v_stop_237_, lean_object* v_b_238_){
_start:
{
size_t v_i_boxed_239_; size_t v_stop_boxed_240_; lean_object* v_res_241_; 
v_i_boxed_239_ = lean_unbox_usize(v_i_236_);
lean_dec(v_i_236_);
v_stop_boxed_240_ = lean_unbox_usize(v_stop_237_);
lean_dec(v_stop_237_);
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_as_235_, v_i_boxed_239_, v_stop_boxed_240_, v_b_238_);
lean_dec_ref(v_as_235_);
return v_res_241_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0(void){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___f_242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_243_ = l_Lean_Fmt_TaggedDoc_softSpace;
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___f_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(size_t v_sz_245_, size_t v_i_246_, lean_object* v_bs_247_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = lean_usize_dec_lt(v_i_246_, v_sz_245_);
if (v___x_248_ == 0)
{
return v_bs_247_;
}
else
{
lean_object* v_v_249_; lean_object* v___x_250_; lean_object* v_bs_x27_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; 
v_v_249_ = lean_array_uget(v_bs_247_, v_i_246_);
v___x_250_ = lean_unsigned_to_nat(0u);
v_bs_x27_251_ = lean_array_uset(v_bs_247_, v_i_246_, v___x_250_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v_v_249_);
v___x_253_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0);
v___x_254_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_252_, v___x_253_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_add(v_i_246_, v___x_255_);
v___x_257_ = lean_array_uset(v_bs_x27_251_, v_i_246_, v___x_254_);
v_i_246_ = v___x_256_;
v_bs_247_ = v___x_257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___boxed(lean_object* v_sz_259_, lean_object* v_i_260_, lean_object* v_bs_261_){
_start:
{
size_t v_sz_boxed_262_; size_t v_i_boxed_263_; lean_object* v_res_264_; 
v_sz_boxed_262_ = lean_unbox_usize(v_sz_259_);
lean_dec(v_sz_259_);
v_i_boxed_263_ = lean_unbox_usize(v_i_260_);
lean_dec(v_i_260_);
v_res_264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(v_sz_boxed_262_, v_i_boxed_263_, v_bs_261_);
return v_res_264_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0(void){
_start:
{
lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___f_265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_266_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___f_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(size_t v_sz_268_, size_t v_i_269_, lean_object* v_bs_270_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = lean_usize_dec_lt(v_i_269_, v_sz_268_);
if (v___x_271_ == 0)
{
return v_bs_270_;
}
else
{
lean_object* v_v_272_; lean_object* v___x_273_; lean_object* v_bs_x27_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v_v_272_ = lean_array_uget(v_bs_270_, v_i_269_);
v___x_273_ = lean_unsigned_to_nat(0u);
v_bs_x27_274_ = lean_array_uset(v_bs_270_, v_i_269_, v___x_273_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_v_272_);
v___x_276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_277_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_275_, v___x_276_);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_add(v_i_269_, v___x_278_);
v___x_280_ = lean_array_uset(v_bs_x27_274_, v_i_269_, v___x_277_);
v_i_269_ = v___x_279_;
v_bs_270_ = v___x_280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___boxed(lean_object* v_sz_282_, lean_object* v_i_283_, lean_object* v_bs_284_){
_start:
{
size_t v_sz_boxed_285_; size_t v_i_boxed_286_; lean_object* v_res_287_; 
v_sz_boxed_285_ = lean_unbox_usize(v_sz_282_);
lean_dec(v_sz_282_);
v_i_boxed_286_ = lean_unbox_usize(v_i_283_);
lean_dec(v_i_283_);
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_boxed_285_, v_i_boxed_286_, v_bs_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array(lean_object* v_array_290_, lean_object* v_format_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___y_295_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_292_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_array_get_size(v_array_290_);
v___x_331_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_332_ = lean_nat_dec_lt(v___x_293_, v___x_330_);
if (v___x_332_ == 0)
{
v___y_295_ = v___x_331_;
goto v___jp_294_;
}
else
{
uint8_t v___x_333_; 
v___x_333_ = lean_nat_dec_le(v___x_330_, v___x_330_);
if (v___x_333_ == 0)
{
if (v___x_332_ == 0)
{
v___y_295_ = v___x_331_;
goto v___jp_294_;
}
else
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((size_t)0ULL);
v___x_335_ = lean_usize_of_nat(v___x_330_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_array_290_, v___x_334_, v___x_335_, v___x_331_);
v___y_295_ = v___x_336_;
goto v___jp_294_;
}
}
else
{
size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((size_t)0ULL);
v___x_338_ = lean_usize_of_nat(v___x_330_);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_array_290_, v___x_337_, v___x_338_, v___x_331_);
v___y_295_ = v___x_339_;
goto v___jp_294_;
}
}
v___jp_294_:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_array_get_size(v___y_295_);
v___x_297_ = lean_nat_dec_eq(v___x_296_, v___x_293_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_dec_eq(v___x_296_, v___x_298_);
if (v___x_299_ == 0)
{
switch(lean_obj_tag(v_format_291_))
{
case 0:
{
size_t v_sz_300_; size_t v___x_301_; lean_object* v_terms_302_; lean_object* v___x_303_; 
v_sz_300_ = lean_array_size(v___y_295_);
v___x_301_ = ((size_t)0ULL);
v_terms_302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(v_sz_300_, v___x_301_, v___y_295_);
v___x_303_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_302_);
lean_dec_ref(v_terms_302_);
return v___x_303_;
}
case 1:
{
size_t v_sz_304_; size_t v___x_305_; lean_object* v_terms_306_; lean_object* v___x_307_; 
v_sz_304_ = lean_array_size(v___y_295_);
v___x_305_ = ((size_t)0ULL);
v_terms_306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(v_sz_304_, v___x_305_, v___y_295_);
v___x_307_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_306_);
lean_dec_ref(v_terms_306_);
return v___x_307_;
}
case 2:
{
size_t v_sz_308_; size_t v___x_309_; lean_object* v_terms_310_; lean_object* v___x_311_; 
v_sz_308_ = lean_array_size(v___y_295_);
v___x_309_ = ((size_t)0ULL);
v_terms_310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(v_sz_308_, v___x_309_, v___y_295_);
v___x_311_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_310_);
lean_dec_ref(v_terms_310_);
return v___x_311_;
}
case 3:
{
uint8_t v_allowFlattening_312_; 
v_allowFlattening_312_ = lean_ctor_get_uint8(v_format_291_, 0);
if (v_allowFlattening_312_ == 0)
{
size_t v_sz_313_; size_t v___x_314_; lean_object* v_terms_315_; lean_object* v___x_316_; 
v_sz_313_ = lean_array_size(v___y_295_);
v___x_314_ = ((size_t)0ULL);
v_terms_315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(v_sz_313_, v___x_314_, v___y_295_);
v___x_316_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_315_);
lean_dec_ref(v_terms_315_);
return v___x_316_;
}
else
{
size_t v_sz_317_; size_t v___x_318_; lean_object* v_terms_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_sz_317_ = lean_array_size(v___y_295_);
v___x_318_ = ((size_t)0ULL);
v_terms_319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_317_, v___x_318_, v___y_295_);
v___x_320_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_319_);
lean_dec_ref(v_terms_319_);
v___x_321_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_320_);
return v___x_321_;
}
}
case 4:
{
size_t v_sz_322_; size_t v___x_323_; lean_object* v_terms_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_sz_322_ = lean_array_size(v___y_295_);
v___x_323_ = ((size_t)0ULL);
v_terms_324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(v_sz_322_, v___x_323_, v___y_295_);
v___x_325_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_324_);
lean_dec_ref(v_terms_324_);
v___x_326_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_325_);
return v___x_326_;
}
default: 
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___y_295_);
return v___x_327_;
}
}
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_array_get(v___x_292_, v___y_295_, v___x_293_);
lean_dec_ref(v___y_295_);
return v___x_328_;
}
}
else
{
lean_object* v___x_329_; 
lean_dec_ref(v___y_295_);
v___x_329_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array___boxed(lean_object* v_array_340_, lean_object* v_format_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Fmt_Layouts_array(v_array_340_, v_format_341_);
lean_dec(v_format_341_);
lean_dec_ref(v_array_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines(lean_object* v_lines_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_Fmt_Layouts_lines___closed__0));
v___x_347_ = l_Lean_Fmt_Layouts_array(v_lines_345_, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines___boxed(lean_object* v_lines_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Fmt_Layouts_lines(v_lines_348_);
lean_dec_ref(v_lines_348_);
return v_res_349_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_351_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(size_t v_sz_352_, size_t v_i_353_, lean_object* v_bs_354_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_usize_dec_lt(v_i_353_, v_sz_352_);
if (v___x_355_ == 0)
{
return v_bs_354_;
}
else
{
lean_object* v___f_356_; lean_object* v_v_357_; lean_object* v___x_358_; lean_object* v_bs_x27_359_; lean_object* v___x_360_; lean_object* v___y_362_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___f_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v_v_357_ = lean_array_uget(v_bs_354_, v_i_353_);
v___x_358_ = lean_unsigned_to_nat(0u);
v_bs_x27_359_ = lean_array_uset(v_bs_354_, v_i_353_, v___x_358_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v_v_357_);
v___x_369_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_370_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0);
if (v___x_370_ == 0)
{
if (v___x_370_ == 0)
{
lean_object* v_doc_371_; uint8_t v___x_372_; 
v_doc_371_ = lean_ctor_get(v___x_369_, 0);
v___x_372_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_371_);
if (v___x_372_ == 0)
{
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_inc_n(v_doc_371_, 2);
v___x_373_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_371_, v_doc_371_);
v___x_374_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_373_);
v___y_362_ = v___x_374_;
goto v___jp_361_;
}
else
{
lean_object* v___x_375_; 
lean_inc(v_doc_371_);
v___x_375_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_371_);
v___y_362_ = v___x_375_;
goto v___jp_361_;
}
}
else
{
lean_object* v___x_376_; 
lean_inc(v_doc_371_);
v___x_376_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_371_);
v___y_362_ = v___x_376_;
goto v___jp_361_;
}
}
else
{
v___y_362_ = v___x_369_;
goto v___jp_361_;
}
}
else
{
v___y_362_ = v___x_369_;
goto v___jp_361_;
}
v___jp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; size_t v___x_365_; size_t v___x_366_; lean_object* v___x_367_; 
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___y_362_);
lean_ctor_set(v___x_363_, 1, v___f_356_);
v___x_364_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_360_, v___x_363_);
v___x_365_ = ((size_t)1ULL);
v___x_366_ = lean_usize_add(v_i_353_, v___x_365_);
v___x_367_ = lean_array_uset(v_bs_x27_359_, v_i_353_, v___x_364_);
v_i_353_ = v___x_366_;
v_bs_354_ = v___x_367_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___boxed(lean_object* v_sz_377_, lean_object* v_i_378_, lean_object* v_bs_379_){
_start:
{
size_t v_sz_boxed_380_; size_t v_i_boxed_381_; lean_object* v_res_382_; 
v_sz_boxed_380_ = lean_unbox_usize(v_sz_377_);
lean_dec(v_sz_377_);
v_i_boxed_381_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(v_sz_boxed_380_, v_i_boxed_381_, v_bs_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedLines(lean_object* v_lines_383_){
_start:
{
size_t v_sz_384_; size_t v___x_385_; lean_object* v_lines_386_; lean_object* v___x_387_; 
v_sz_384_ = lean_array_size(v_lines_383_);
v___x_385_ = ((size_t)0ULL);
v_lines_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(v_sz_384_, v___x_385_, v_lines_383_);
v___x_387_ = l_Lean_Fmt_TaggedDoc_combine(v_lines_386_);
lean_dec_ref(v_lines_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic(lean_object* v_terms_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_box(0);
v___x_390_ = l_Lean_Fmt_Layouts_array(v_terms_388_, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic___boxed(lean_object* v_terms_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Fmt_Layouts_atomic(v_terms_391_);
lean_dec_ref(v_terms_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object* v_terms_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___y_397_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_394_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_array_get_size(v_terms_393_);
v___x_405_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_406_ = lean_nat_dec_lt(v___x_395_, v___x_404_);
if (v___x_406_ == 0)
{
v___y_397_ = v___x_405_;
goto v___jp_396_;
}
else
{
uint8_t v___x_407_; 
v___x_407_ = lean_nat_dec_le(v___x_404_, v___x_404_);
if (v___x_407_ == 0)
{
if (v___x_406_ == 0)
{
v___y_397_ = v___x_405_;
goto v___jp_396_;
}
else
{
size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; 
v___x_408_ = ((size_t)0ULL);
v___x_409_ = lean_usize_of_nat(v___x_404_);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_terms_393_, v___x_408_, v___x_409_, v___x_405_);
v___y_397_ = v___x_410_;
goto v___jp_396_;
}
}
else
{
size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((size_t)0ULL);
v___x_412_ = lean_usize_of_nat(v___x_404_);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_terms_393_, v___x_411_, v___x_412_, v___x_405_);
v___y_397_ = v___x_413_;
goto v___jp_396_;
}
}
v___jp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_398_ = lean_array_get_size(v___y_397_);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_nat_dec_eq(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = l_Lean_Fmt_Layouts_atomic(v___y_397_);
lean_dec_ref(v___y_397_);
v___x_402_ = l_Lean_Fmt_TaggedDoc_nested(v___x_401_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; 
v___x_403_ = lean_array_get(v___x_394_, v___y_397_, v___x_395_);
lean_dec_ref(v___y_397_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator___boxed(lean_object* v_terms_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Fmt_Layouts_atomicInfixOperator(v_terms_414_);
lean_dec_ref(v_terms_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object* v_terms_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_box(1);
v___x_418_ = l_Lean_Fmt_Layouts_array(v_terms_416_, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic___boxed(lean_object* v_terms_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Fmt_Layouts_spacedAtomic(v_terms_419_);
lean_dec_ref(v_terms_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object* v_terms_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_box(2);
v___x_423_ = l_Lean_Fmt_Layouts_array(v_terms_421_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic___boxed(lean_object* v_terms_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v_terms_424_);
lean_dec_ref(v_terms_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill(lean_object* v_terms_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_box(5);
v___x_428_ = l_Lean_Fmt_Layouts_array(v_terms_426_, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill___boxed(lean_object* v_terms_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Fmt_Layouts_fill(v_terms_429_);
lean_dec_ref(v_terms_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object* v_terms_431_, uint8_t v_spacing_432_){
_start:
{
if (v_spacing_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_box(4);
v___x_434_ = l_Lean_Fmt_Layouts_array(v_terms_431_, v___x_433_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_alloc_ctor(3, 0, 1);
lean_ctor_set_uint8(v___x_435_, 0, v_spacing_432_);
v___x_436_ = l_Lean_Fmt_Layouts_array(v_terms_431_, v___x_435_);
lean_dec_ref_known(v___x_435_, 0);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical___boxed(lean_object* v_terms_437_, lean_object* v_spacing_438_){
_start:
{
uint8_t v_spacing_boxed_439_; lean_object* v_res_440_; 
v_spacing_boxed_439_ = lean_unbox(v_spacing_438_);
v_res_440_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_437_, v_spacing_boxed_439_);
lean_dec_ref(v_terms_437_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx(uint8_t v_x_441_){
_start:
{
switch(v_x_441_)
{
case 0:
{
lean_object* v___x_442_; 
v___x_442_ = lean_unsigned_to_nat(0u);
return v___x_442_;
}
case 1:
{
lean_object* v___x_443_; 
v___x_443_ = lean_unsigned_to_nat(1u);
return v___x_443_;
}
default: 
{
lean_object* v___x_444_; 
v___x_444_ = lean_unsigned_to_nat(2u);
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___boxed(lean_object* v_x_445_){
_start:
{
uint8_t v_x_boxed_446_; lean_object* v_res_447_; 
v_x_boxed_446_ = lean_unbox(v_x_445_);
v_res_447_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx(v_x_boxed_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(lean_object* v_k_448_){
_start:
{
lean_inc(v_k_448_);
return v_k_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg___boxed(lean_object* v_k_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(v_k_449_);
lean_dec(v_k_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(lean_object* v_motive_451_, lean_object* v_ctorIdx_452_, uint8_t v_t_453_, lean_object* v_h_454_, lean_object* v_k_455_){
_start:
{
lean_inc(v_k_455_);
return v_k_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___boxed(lean_object* v_motive_456_, lean_object* v_ctorIdx_457_, lean_object* v_t_458_, lean_object* v_h_459_, lean_object* v_k_460_){
_start:
{
uint8_t v_t_boxed_461_; lean_object* v_res_462_; 
v_t_boxed_461_ = lean_unbox(v_t_458_);
v_res_462_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(v_motive_456_, v_ctorIdx_457_, v_t_boxed_461_, v_h_459_, v_k_460_);
lean_dec(v_k_460_);
lean_dec(v_ctorIdx_457_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(lean_object* v_includeTrailingSep_463_){
_start:
{
lean_inc(v_includeTrailingSep_463_);
return v_includeTrailingSep_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg___boxed(lean_object* v_includeTrailingSep_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(v_includeTrailingSep_464_);
lean_dec(v_includeTrailingSep_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(lean_object* v_motive_466_, uint8_t v_t_467_, lean_object* v_h_468_, lean_object* v_includeTrailingSep_469_){
_start:
{
lean_inc(v_includeTrailingSep_469_);
return v_includeTrailingSep_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___boxed(lean_object* v_motive_470_, lean_object* v_t_471_, lean_object* v_h_472_, lean_object* v_includeTrailingSep_473_){
_start:
{
uint8_t v_t_boxed_474_; lean_object* v_res_475_; 
v_t_boxed_474_ = lean_unbox(v_t_471_);
v_res_475_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(v_motive_470_, v_t_boxed_474_, v_h_472_, v_includeTrailingSep_473_);
lean_dec(v_includeTrailingSep_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(lean_object* v_excludeTrailingSep_476_){
_start:
{
lean_inc(v_excludeTrailingSep_476_);
return v_excludeTrailingSep_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg___boxed(lean_object* v_excludeTrailingSep_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(v_excludeTrailingSep_477_);
lean_dec(v_excludeTrailingSep_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(lean_object* v_motive_479_, uint8_t v_t_480_, lean_object* v_h_481_, lean_object* v_excludeTrailingSep_482_){
_start:
{
lean_inc(v_excludeTrailingSep_482_);
return v_excludeTrailingSep_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___boxed(lean_object* v_motive_483_, lean_object* v_t_484_, lean_object* v_h_485_, lean_object* v_excludeTrailingSep_486_){
_start:
{
uint8_t v_t_boxed_487_; lean_object* v_res_488_; 
v_t_boxed_487_ = lean_unbox(v_t_484_);
v_res_488_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(v_motive_483_, v_t_boxed_487_, v_h_485_, v_excludeTrailingSep_486_);
lean_dec(v_excludeTrailingSep_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(lean_object* v_retainTrailingSep_489_){
_start:
{
lean_inc(v_retainTrailingSep_489_);
return v_retainTrailingSep_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg___boxed(lean_object* v_retainTrailingSep_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(v_retainTrailingSep_490_);
lean_dec(v_retainTrailingSep_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(lean_object* v_motive_492_, uint8_t v_t_493_, lean_object* v_h_494_, lean_object* v_retainTrailingSep_495_){
_start:
{
lean_inc(v_retainTrailingSep_495_);
return v_retainTrailingSep_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___boxed(lean_object* v_motive_496_, lean_object* v_t_497_, lean_object* v_h_498_, lean_object* v_retainTrailingSep_499_){
_start:
{
uint8_t v_t_boxed_500_; lean_object* v_res_501_; 
v_t_boxed_500_ = lean_unbox(v_t_497_);
v_res_501_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(v_motive_496_, v_t_boxed_500_, v_h_498_, v_retainTrailingSep_499_);
lean_dec(v_retainTrailingSep_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx(lean_object* v_x_502_){
_start:
{
switch(lean_obj_tag(v_x_502_))
{
case 0:
{
lean_object* v___x_503_; 
v___x_503_ = lean_unsigned_to_nat(0u);
return v___x_503_;
}
case 1:
{
lean_object* v___x_504_; 
v___x_504_ = lean_unsigned_to_nat(1u);
return v___x_504_;
}
case 2:
{
lean_object* v___x_505_; 
v___x_505_ = lean_unsigned_to_nat(2u);
return v___x_505_;
}
default: 
{
lean_object* v___x_506_; 
v___x_506_ = lean_unsigned_to_nat(3u);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___boxed(lean_object* v_x_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx(v_x_507_);
lean_dec_ref(v_x_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(lean_object* v_t_509_, lean_object* v_k_510_){
_start:
{
switch(lean_obj_tag(v_t_509_))
{
case 1:
{
uint8_t v_allowFlattening_511_; lean_object* v_afterElem_x3f_512_; uint8_t v_trailingSep_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_allowFlattening_511_ = lean_ctor_get_uint8(v_t_509_, sizeof(void*)*1);
v_afterElem_x3f_512_ = lean_ctor_get(v_t_509_, 0);
lean_inc(v_afterElem_x3f_512_);
v_trailingSep_513_ = lean_ctor_get_uint8(v_t_509_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_509_, 1);
v___x_514_ = lean_box(v_allowFlattening_511_);
v___x_515_ = lean_box(v_trailingSep_513_);
v___x_516_ = lean_apply_3(v_k_510_, v___x_514_, v_afterElem_x3f_512_, v___x_515_);
return v___x_516_;
}
case 3:
{
lean_object* v_afterElem_x3f_517_; uint8_t v_trailingSep_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_afterElem_x3f_517_ = lean_ctor_get(v_t_509_, 0);
lean_inc(v_afterElem_x3f_517_);
v_trailingSep_518_ = lean_ctor_get_uint8(v_t_509_, sizeof(void*)*1);
lean_dec_ref_known(v_t_509_, 1);
v___x_519_ = lean_box(v_trailingSep_518_);
v___x_520_ = lean_apply_2(v_k_510_, v_afterElem_x3f_517_, v___x_519_);
return v___x_520_;
}
default: 
{
lean_object* v_afterElem_x3f_521_; lean_object* v_afterSep_x3f_522_; uint8_t v_trailingSep_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_afterElem_x3f_521_ = lean_ctor_get(v_t_509_, 0);
lean_inc(v_afterElem_x3f_521_);
v_afterSep_x3f_522_ = lean_ctor_get(v_t_509_, 1);
lean_inc(v_afterSep_x3f_522_);
v_trailingSep_523_ = lean_ctor_get_uint8(v_t_509_, sizeof(void*)*2);
lean_dec_ref(v_t_509_);
v___x_524_ = lean_box(v_trailingSep_523_);
v___x_525_ = lean_apply_3(v_k_510_, v_afterElem_x3f_521_, v_afterSep_x3f_522_, v___x_524_);
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(lean_object* v_motive_526_, lean_object* v_ctorIdx_527_, lean_object* v_t_528_, lean_object* v_h_529_, lean_object* v_k_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_528_, v_k_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___boxed(lean_object* v_motive_532_, lean_object* v_ctorIdx_533_, lean_object* v_t_534_, lean_object* v_h_535_, lean_object* v_k_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(v_motive_532_, v_ctorIdx_533_, v_t_534_, v_h_535_, v_k_536_);
lean_dec(v_ctorIdx_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim___redArg(lean_object* v_t_538_, lean_object* v_joinUsingSep_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_538_, v_joinUsingSep_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim(lean_object* v_motive_541_, lean_object* v_t_542_, lean_object* v_h_543_, lean_object* v_joinUsingSep_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_542_, v_joinUsingSep_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim___redArg(lean_object* v_t_546_, lean_object* v_joinUsingNl_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_546_, v_joinUsingNl_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim(lean_object* v_motive_549_, lean_object* v_t_550_, lean_object* v_h_551_, lean_object* v_joinUsingNl_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_550_, v_joinUsingNl_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim___redArg(lean_object* v_t_554_, lean_object* v_fillUsingSep_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_554_, v_fillUsingSep_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim(lean_object* v_motive_557_, lean_object* v_t_558_, lean_object* v_h_559_, lean_object* v_fillUsingSep_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_558_, v_fillUsingSep_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim___redArg(lean_object* v_t_562_, lean_object* v_fillUsingSpacedSep_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_562_, v_fillUsingSpacedSep_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim(lean_object* v_motive_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_fillUsingSpacedSep_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_566_, v_fillUsingSpacedSep_568_);
return v___x_569_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(lean_object* v_x_570_){
_start:
{
switch(lean_obj_tag(v_x_570_))
{
case 1:
{
uint8_t v_trailingSep_571_; 
v_trailingSep_571_ = lean_ctor_get_uint8(v_x_570_, sizeof(void*)*1 + 1);
return v_trailingSep_571_;
}
case 3:
{
uint8_t v_trailingSep_572_; 
v_trailingSep_572_ = lean_ctor_get_uint8(v_x_570_, sizeof(void*)*1);
return v_trailingSep_572_;
}
default: 
{
uint8_t v_trailingSep_573_; 
v_trailingSep_573_ = lean_ctor_get_uint8(v_x_570_, sizeof(void*)*2);
return v_trailingSep_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep___boxed(lean_object* v_x_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(v_x_574_);
lean_dec_ref(v_x_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(lean_object* v_sepArray_577_, lean_object* v_sep_578_, lean_object* v___x_579_, uint8_t v_trailingSep_580_, lean_object* v_a_581_, lean_object* v_b_582_){
_start:
{
lean_object* v_inner_583_; lean_object* v_next_584_; 
v_inner_583_ = lean_ctor_get(v_a_581_, 2);
lean_inc(v_inner_583_);
v_next_584_ = lean_ctor_get(v_inner_583_, 0);
lean_inc(v_next_584_);
if (lean_obj_tag(v_next_584_) == 0)
{
lean_dec(v_inner_583_);
lean_dec_ref(v_a_581_);
lean_dec_ref(v_sep_578_);
return v_b_582_;
}
else
{
lean_object* v_nextIdx_585_; lean_object* v_n_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_637_; 
v_nextIdx_585_ = lean_ctor_get(v_a_581_, 0);
v_n_586_ = lean_ctor_get(v_a_581_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_a_581_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v_a_581_, 2);
lean_dec(v_unused_638_);
v___x_588_ = v_a_581_;
v_isShared_589_ = v_isSharedCheck_637_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_n_586_);
lean_inc(v_nextIdx_585_);
lean_dec(v_a_581_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_637_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_upperBound_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_635_; 
v_upperBound_590_ = lean_ctor_get(v_inner_583_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_inner_583_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_inner_583_, 0);
lean_dec(v_unused_636_);
v___x_592_ = v_inner_583_;
v_isShared_593_ = v_isSharedCheck_635_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_upperBound_590_);
lean_dec(v_inner_583_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_635_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_634_; 
v_val_594_ = lean_ctor_get(v_next_584_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_next_584_);
if (v_isSharedCheck_634_ == 0)
{
v___x_596_ = v_next_584_;
v_isShared_597_ = v_isSharedCheck_634_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_dec(v_next_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_634_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_nat_add(v_val_594_, v_nextIdx_585_);
lean_dec(v_nextIdx_585_);
lean_dec(v_val_594_);
v___x_599_ = lean_nat_dec_lt(v___x_598_, v_upperBound_590_);
if (v___x_599_ == 0)
{
lean_dec(v___x_598_);
lean_del_object(v___x_596_);
lean_del_object(v___x_592_);
lean_dec(v_upperBound_590_);
lean_del_object(v___x_588_);
lean_dec(v_n_586_);
lean_dec_ref(v_sep_578_);
return v_b_582_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_600_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_add(v___x_598_, v___x_601_);
lean_inc(v___x_602_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_602_);
v___x_604_ = v___x_596_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_633_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_604_);
v___x_606_ = v___x_592_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_upperBound_590_);
v___x_606_ = v_reuseFailAlloc_632_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
lean_inc(v_n_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 2, v___x_606_);
lean_ctor_set(v___x_588_, 0, v_n_586_);
v___x_608_ = v___x_588_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_n_586_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_n_586_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v___x_606_);
v___x_608_ = v_reuseFailAlloc_631_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_array_get_borrowed(v___x_600_, v_sepArray_577_, v___x_598_);
v___x_610_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___y_613_; lean_object* v___y_617_; uint8_t v___y_622_; 
lean_inc(v___x_609_);
v___x_611_ = lean_array_push(v_b_582_, v___x_609_);
if (v_trailingSep_580_ == 2)
{
goto v___jp_627_;
}
else
{
if (v___x_610_ == 0)
{
lean_dec(v___x_598_);
v___y_622_ = v___x_610_;
goto v___jp_621_;
}
else
{
goto v___jp_627_;
}
}
v___jp_612_:
{
lean_object* v___x_614_; 
v___x_614_ = lean_array_push(v___x_611_, v___y_613_);
v_a_581_ = v___x_608_;
v_b_582_ = v___x_614_;
goto _start;
}
v___jp_616_:
{
uint8_t v___x_618_; 
v___x_618_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_617_);
if (v___x_618_ == 0)
{
v___y_613_ = v___y_617_;
goto v___jp_612_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec_ref(v___y_617_);
lean_inc_ref(v_sep_578_);
v___x_619_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_578_);
v___x_620_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_619_);
v___y_613_ = v___x_620_;
goto v___jp_612_;
}
}
v___jp_621_:
{
if (v___y_622_ == 0)
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_array_get_size(v_sepArray_577_);
v___x_624_ = lean_nat_dec_lt(v___x_602_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; 
lean_dec(v___x_602_);
v___x_625_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_617_ = v___x_625_;
goto v___jp_616_;
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_array_fget_borrowed(v_sepArray_577_, v___x_602_);
lean_dec(v___x_602_);
lean_inc(v___x_626_);
v___y_617_ = v___x_626_;
goto v___jp_616_;
}
}
else
{
lean_dec_ref(v___x_608_);
lean_dec(v___x_602_);
lean_dec_ref(v_sep_578_);
return v___x_611_;
}
}
v___jp_627_:
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_nat_sub(v___x_579_, v___x_601_);
v___x_629_ = lean_nat_dec_eq(v___x_598_, v___x_628_);
lean_dec(v___x_628_);
lean_dec(v___x_598_);
v___y_622_ = v___x_629_;
goto v___jp_621_;
}
}
else
{
lean_dec(v___x_602_);
lean_dec(v___x_598_);
v_a_581_ = v___x_608_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg___boxed(lean_object* v_sepArray_639_, lean_object* v_sep_640_, lean_object* v___x_641_, lean_object* v_trailingSep_642_, lean_object* v_a_643_, lean_object* v_b_644_){
_start:
{
uint8_t v_trailingSep_boxed_645_; lean_object* v_res_646_; 
v_trailingSep_boxed_645_ = lean_unbox(v_trailingSep_642_);
v_res_646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_639_, v_sep_640_, v___x_641_, v_trailingSep_boxed_645_, v_a_643_, v_b_644_);
lean_dec(v___x_641_);
lean_dec_ref(v_sepArray_639_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(lean_object* v_sep_649_, lean_object* v_sepArray_650_, uint8_t v_trailingSep_651_){
_start:
{
lean_object* v___x_652_; lean_object* v_r_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v_r_653_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_654_ = lean_array_get_size(v_sepArray_650_);
v___x_655_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0));
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v___x_654_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_658_, 0, v___x_652_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
lean_ctor_set(v___x_658_, 2, v___x_656_);
v___x_659_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_650_, v_sep_649_, v___x_654_, v_trailingSep_651_, v___x_658_, v_r_653_);
if (v_trailingSep_651_ == 1)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_660_ = lean_unsigned_to_nat(2u);
v___x_661_ = lean_array_get_size(v___x_659_);
v___x_662_ = lean_nat_mod(v___x_661_, v___x_660_);
v___x_663_ = lean_nat_dec_eq(v___x_662_, v___x_652_);
lean_dec(v___x_662_);
if (v___x_663_ == 0)
{
return v___x_659_;
}
else
{
lean_object* v___x_664_; 
v___x_664_ = lean_array_pop(v___x_659_);
return v___x_664_;
}
}
else
{
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___boxed(lean_object* v_sep_665_, lean_object* v_sepArray_666_, lean_object* v_trailingSep_667_){
_start:
{
uint8_t v_trailingSep_boxed_668_; lean_object* v_res_669_; 
v_trailingSep_boxed_668_ = lean_unbox(v_trailingSep_667_);
v_res_669_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_665_, v_sepArray_666_, v_trailingSep_boxed_668_);
lean_dec_ref(v_sepArray_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(lean_object* v_sepArray_670_, lean_object* v_sep_671_, lean_object* v___x_672_, uint8_t v_trailingSep_673_, lean_object* v_inst_674_, lean_object* v_R_675_, lean_object* v_a_676_, lean_object* v_b_677_, lean_object* v_c_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_670_, v_sep_671_, v___x_672_, v_trailingSep_673_, v_a_676_, v_b_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___boxed(lean_object* v_sepArray_680_, lean_object* v_sep_681_, lean_object* v___x_682_, lean_object* v_trailingSep_683_, lean_object* v_inst_684_, lean_object* v_R_685_, lean_object* v_a_686_, lean_object* v_b_687_, lean_object* v_c_688_){
_start:
{
uint8_t v_trailingSep_boxed_689_; lean_object* v_res_690_; 
v_trailingSep_boxed_689_ = lean_unbox(v_trailingSep_683_);
v_res_690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(v_sepArray_680_, v_sep_681_, v___x_682_, v_trailingSep_boxed_689_, v_inst_684_, v_R_685_, v_a_686_, v_b_687_, v_c_688_);
lean_dec(v___x_682_);
lean_dec_ref(v_sepArray_680_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(lean_object* v_sepArray_691_, lean_object* v_sep_692_, lean_object* v_afterSep_x3f_693_, lean_object* v_afterElem_x3f_694_, size_t v_sz_695_, size_t v_i_696_, lean_object* v_bs_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = lean_usize_dec_lt(v_i_696_, v_sz_695_);
if (v___x_698_ == 0)
{
lean_dec(v_afterElem_x3f_694_);
lean_dec(v_afterSep_x3f_693_);
lean_dec_ref(v_sep_692_);
return v_bs_697_;
}
else
{
lean_object* v_v_699_; lean_object* v___x_700_; lean_object* v_bs_x27_701_; lean_object* v___y_703_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_v_699_ = lean_array_uget(v_bs_697_, v_i_696_);
v___x_700_ = lean_unsigned_to_nat(0u);
v_bs_x27_701_ = lean_array_uset(v_bs_697_, v_i_696_, v___x_700_);
v___x_722_ = lean_usize_to_nat(v_i_696_);
v___x_723_ = lean_array_get_size(v_sepArray_691_);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_sub(v___x_723_, v___x_724_);
v___x_726_ = lean_nat_dec_eq(v___x_722_, v___x_725_);
lean_dec(v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v_isElem_729_; lean_object* v___y_731_; 
v___x_727_ = lean_unsigned_to_nat(2u);
v___x_728_ = lean_nat_mod(v___x_722_, v___x_727_);
lean_dec(v___x_722_);
v_isElem_729_ = lean_nat_dec_eq(v___x_728_, v___x_700_);
lean_dec(v___x_728_);
if (v_isElem_729_ == 0)
{
lean_inc(v_afterSep_x3f_693_);
v___y_731_ = v_afterSep_x3f_693_;
goto v___jp_730_;
}
else
{
lean_inc(v_afterElem_x3f_694_);
v___y_731_ = v_afterElem_x3f_694_;
goto v___jp_730_;
}
v___jp_730_:
{
if (v_isElem_729_ == 0)
{
uint8_t v___x_732_; 
v___x_732_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_699_);
if (v___x_732_ == 0)
{
v___y_709_ = v___y_731_;
v___y_710_ = v_v_699_;
goto v___jp_708_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec(v_v_699_);
lean_inc_ref(v_sep_692_);
v___x_733_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_692_);
v___x_734_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_733_);
v___y_709_ = v___y_731_;
v___y_710_ = v___x_734_;
goto v___jp_708_;
}
}
else
{
v___y_709_ = v___y_731_;
v___y_710_ = v_v_699_;
goto v___jp_708_;
}
}
}
else
{
lean_dec(v___x_722_);
v___y_703_ = v_v_699_;
goto v___jp_702_;
}
v___jp_702_:
{
size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_add(v_i_696_, v___x_704_);
v___x_706_ = lean_array_uset(v_bs_x27_701_, v_i_696_, v___y_703_);
v_i_696_ = v___x_705_;
v_bs_697_ = v___x_706_;
goto _start;
}
v___jp_708_:
{
if (lean_obj_tag(v___y_709_) == 1)
{
lean_object* v_val_711_; uint8_t v___x_712_; 
v_val_711_ = lean_ctor_get(v___y_709_, 0);
lean_inc(v_val_711_);
lean_dec_ref_known(v___y_709_, 1);
v___x_712_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_710_);
if (v___x_712_ == 0)
{
uint8_t v___x_713_; 
v___x_713_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_711_);
if (v___x_713_ == 0)
{
lean_object* v_doc_714_; lean_object* v_doc_715_; uint8_t v___x_716_; 
v_doc_714_ = lean_ctor_get(v___y_710_, 0);
lean_inc(v_doc_714_);
lean_dec_ref(v___y_710_);
v_doc_715_ = lean_ctor_get(v_val_711_, 0);
lean_inc(v_doc_715_);
lean_dec(v_val_711_);
v___x_716_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_714_);
if (v___x_716_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_715_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_714_, v_doc_715_);
v___x_719_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_718_);
v___y_703_ = v___x_719_;
goto v___jp_702_;
}
else
{
lean_object* v___x_720_; 
lean_dec(v_doc_715_);
v___x_720_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_714_);
v___y_703_ = v___x_720_;
goto v___jp_702_;
}
}
else
{
lean_object* v___x_721_; 
lean_dec(v_doc_714_);
v___x_721_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_715_);
v___y_703_ = v___x_721_;
goto v___jp_702_;
}
}
else
{
lean_dec(v_val_711_);
v___y_703_ = v___y_710_;
goto v___jp_702_;
}
}
else
{
lean_dec_ref(v___y_710_);
v___y_703_ = v_val_711_;
goto v___jp_702_;
}
}
else
{
lean_dec(v___y_709_);
v___y_703_ = v___y_710_;
goto v___jp_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg___boxed(lean_object* v_sepArray_735_, lean_object* v_sep_736_, lean_object* v_afterSep_x3f_737_, lean_object* v_afterElem_x3f_738_, lean_object* v_sz_739_, lean_object* v_i_740_, lean_object* v_bs_741_){
_start:
{
size_t v_sz_boxed_742_; size_t v_i_boxed_743_; lean_object* v_res_744_; 
v_sz_boxed_742_ = lean_unbox_usize(v_sz_739_);
lean_dec(v_sz_739_);
v_i_boxed_743_ = lean_unbox_usize(v_i_740_);
lean_dec(v_i_740_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_735_, v_sep_736_, v_afterSep_x3f_737_, v_afterElem_x3f_738_, v_sz_boxed_742_, v_i_boxed_743_, v_bs_741_);
lean_dec_ref(v_sepArray_735_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(lean_object* v_sep_745_, lean_object* v_sepArray_746_, lean_object* v_afterElem_x3f_747_, lean_object* v_afterSep_x3f_748_){
_start:
{
size_t v_sz_749_; size_t v___x_750_; lean_object* v_docs_751_; lean_object* v___x_752_; 
v_sz_749_ = lean_array_size(v_sepArray_746_);
v___x_750_ = ((size_t)0ULL);
lean_inc_ref(v_sepArray_746_);
v_docs_751_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_746_, v_sep_745_, v_afterSep_x3f_748_, v_afterElem_x3f_747_, v_sz_749_, v___x_750_, v_sepArray_746_);
lean_dec_ref(v_sepArray_746_);
v___x_752_ = l_Lean_Fmt_TaggedDoc_join(v_docs_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(lean_object* v_sepArray_753_, lean_object* v_sep_754_, lean_object* v_afterSep_x3f_755_, lean_object* v_afterElem_x3f_756_, lean_object* v_as_757_, size_t v_sz_758_, size_t v_i_759_, lean_object* v_bs_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_753_, v_sep_754_, v_afterSep_x3f_755_, v_afterElem_x3f_756_, v_sz_758_, v_i_759_, v_bs_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___boxed(lean_object* v_sepArray_762_, lean_object* v_sep_763_, lean_object* v_afterSep_x3f_764_, lean_object* v_afterElem_x3f_765_, lean_object* v_as_766_, lean_object* v_sz_767_, lean_object* v_i_768_, lean_object* v_bs_769_){
_start:
{
size_t v_sz_boxed_770_; size_t v_i_boxed_771_; lean_object* v_res_772_; 
v_sz_boxed_770_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_771_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(v_sepArray_762_, v_sep_763_, v_afterSep_x3f_764_, v_afterElem_x3f_765_, v_as_766_, v_sz_boxed_770_, v_i_boxed_771_, v_bs_769_);
lean_dec_ref(v_as_766_);
lean_dec_ref(v_sepArray_762_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(lean_object* v_upperBound_773_, lean_object* v___x_774_, lean_object* v_sep_775_, lean_object* v_a_776_, lean_object* v_b_777_){
_start:
{
lean_object* v_a_779_; uint8_t v___x_783_; 
v___x_783_ = lean_nat_dec_lt(v_a_776_, v_upperBound_773_);
if (v___x_783_ == 0)
{
lean_dec(v_a_776_);
lean_dec_ref(v_sep_775_);
return v_b_777_;
}
else
{
lean_object* v_fst_784_; lean_object* v_snd_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_805_; 
v_fst_784_ = lean_ctor_get(v_b_777_, 0);
v_snd_785_ = lean_ctor_get(v_b_777_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_b_777_);
if (v_isSharedCheck_805_ == 0)
{
v___x_787_ = v_b_777_;
v_isShared_788_ = v_isSharedCheck_805_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_snd_785_);
lean_inc(v_fst_784_);
lean_dec(v_b_777_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_805_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___y_790_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_array_fget_borrowed(v___x_774_, v_a_776_);
v___x_797_ = lean_unsigned_to_nat(2u);
v___x_798_ = lean_nat_mod(v_a_776_, v___x_797_);
v___x_799_ = lean_nat_dec_eq(v___x_798_, v___x_795_);
lean_dec(v___x_798_);
if (v___x_799_ == 0)
{
uint8_t v___x_800_; 
v___x_800_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_796_);
if (v___x_800_ == 0)
{
lean_inc(v___x_796_);
v___y_790_ = v___x_796_;
goto v___jp_789_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_inc_ref(v_sep_775_);
v___x_801_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_775_);
v___x_802_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_801_);
v___y_790_ = v___x_802_;
goto v___jp_789_;
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_del_object(v___x_787_);
lean_inc(v___x_796_);
v___x_803_ = lean_array_push(v_fst_784_, v___x_796_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v_snd_785_);
v_a_779_ = v___x_804_;
goto v___jp_778_;
}
v___jp_789_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_array_push(v_snd_785_, v___y_790_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_791_);
v___x_793_ = v___x_787_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_fst_784_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
v_a_779_ = v___x_793_;
goto v___jp_778_;
}
}
}
}
v___jp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_a_776_, v___x_780_);
lean_dec(v_a_776_);
v_a_776_ = v___x_781_;
v_b_777_ = v_a_779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg___boxed(lean_object* v_upperBound_806_, lean_object* v___x_807_, lean_object* v_sep_808_, lean_object* v_a_809_, lean_object* v_b_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v_upperBound_806_, v___x_807_, v_sep_808_, v_a_809_, v_b_810_);
lean_dec_ref(v___x_807_);
lean_dec(v_upperBound_806_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(lean_object* v_sep_814_, lean_object* v_sepArray_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_fst_820_; lean_object* v_snd_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = lean_array_get_size(v_sepArray_815_);
v___x_818_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0));
v___x_819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v___x_817_, v_sepArray_815_, v_sep_814_, v___x_816_, v___x_818_);
v_fst_820_ = lean_ctor_get(v___x_819_, 0);
v_snd_821_ = lean_ctor_get(v___x_819_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_819_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_snd_821_);
lean_inc(v_fst_820_);
lean_dec(v___x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_fst_820_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_snd_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___boxed(lean_object* v_sep_829_, lean_object* v_sepArray_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_829_, v_sepArray_830_);
lean_dec_ref(v_sepArray_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(lean_object* v_upperBound_832_, lean_object* v___x_833_, lean_object* v_sep_834_, lean_object* v_inst_835_, lean_object* v_R_836_, lean_object* v_a_837_, lean_object* v_b_838_, lean_object* v_c_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v_upperBound_832_, v___x_833_, v_sep_834_, v_a_837_, v_b_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___boxed(lean_object* v_upperBound_841_, lean_object* v___x_842_, lean_object* v_sep_843_, lean_object* v_inst_844_, lean_object* v_R_845_, lean_object* v_a_846_, lean_object* v_b_847_, lean_object* v_c_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(v_upperBound_841_, v___x_842_, v_sep_843_, v_inst_844_, v_R_845_, v_a_846_, v_b_847_, v_c_848_);
lean_dec_ref(v___x_842_);
lean_dec(v_upperBound_841_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(lean_object* v_fst_850_, lean_object* v_val_851_, size_t v_sz_852_, size_t v_i_853_, lean_object* v_bs_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_lt(v_i_853_, v_sz_852_);
if (v___x_855_ == 0)
{
lean_dec_ref(v_val_851_);
return v_bs_854_;
}
else
{
lean_object* v_v_856_; lean_object* v___x_857_; lean_object* v_bs_x27_858_; lean_object* v___y_860_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_v_856_ = lean_array_uget(v_bs_854_, v_i_853_);
v___x_857_ = lean_unsigned_to_nat(0u);
v_bs_x27_858_ = lean_array_uset(v_bs_854_, v_i_853_, v___x_857_);
v___x_865_ = lean_usize_to_nat(v_i_853_);
v___x_866_ = lean_array_get_size(v_fst_850_);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_sub(v___x_866_, v___x_867_);
v___x_869_ = lean_nat_dec_eq(v___x_865_, v___x_868_);
lean_dec(v___x_868_);
lean_dec(v___x_865_);
if (v___x_869_ == 0)
{
uint8_t v___x_870_; 
v___x_870_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_856_);
if (v___x_870_ == 0)
{
uint8_t v___x_871_; 
v___x_871_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_851_);
if (v___x_871_ == 0)
{
lean_object* v_doc_872_; lean_object* v_doc_873_; uint8_t v___x_874_; 
v_doc_872_ = lean_ctor_get(v_v_856_, 0);
lean_inc(v_doc_872_);
lean_dec(v_v_856_);
v_doc_873_ = lean_ctor_get(v_val_851_, 0);
v___x_874_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_872_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_873_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
lean_inc(v_doc_873_);
v___x_876_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_872_, v_doc_873_);
v___x_877_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_876_);
v___y_860_ = v___x_877_;
goto v___jp_859_;
}
else
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_872_);
v___y_860_ = v___x_878_;
goto v___jp_859_;
}
}
else
{
lean_object* v___x_879_; 
lean_dec(v_doc_872_);
lean_inc(v_doc_873_);
v___x_879_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_873_);
v___y_860_ = v___x_879_;
goto v___jp_859_;
}
}
else
{
v___y_860_ = v_v_856_;
goto v___jp_859_;
}
}
else
{
lean_dec(v_v_856_);
lean_inc_ref(v_val_851_);
v___y_860_ = v_val_851_;
goto v___jp_859_;
}
}
else
{
v___y_860_ = v_v_856_;
goto v___jp_859_;
}
v___jp_859_:
{
size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((size_t)1ULL);
v___x_862_ = lean_usize_add(v_i_853_, v___x_861_);
v___x_863_ = lean_array_uset(v_bs_x27_858_, v_i_853_, v___y_860_);
v_i_853_ = v___x_862_;
v_bs_854_ = v___x_863_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg___boxed(lean_object* v_fst_880_, lean_object* v_val_881_, lean_object* v_sz_882_, lean_object* v_i_883_, lean_object* v_bs_884_){
_start:
{
size_t v_sz_boxed_885_; size_t v_i_boxed_886_; lean_object* v_res_887_; 
v_sz_boxed_885_ = lean_unbox_usize(v_sz_882_);
lean_dec(v_sz_882_);
v_i_boxed_886_ = lean_unbox_usize(v_i_883_);
lean_dec(v_i_883_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_880_, v_val_881_, v_sz_boxed_885_, v_i_boxed_886_, v_bs_884_);
lean_dec_ref(v_fst_880_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(lean_object* v_sep_888_, lean_object* v_sepArray_889_, lean_object* v_afterElem_x3f_890_){
_start:
{
lean_object* v_elems_892_; lean_object* v___x_895_; 
v___x_895_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_888_, v_sepArray_889_);
if (lean_obj_tag(v_afterElem_x3f_890_) == 1)
{
lean_object* v_fst_896_; lean_object* v_val_897_; size_t v_sz_898_; size_t v___x_899_; lean_object* v_elems_900_; 
v_fst_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_n(v_fst_896_, 2);
lean_dec_ref(v___x_895_);
v_val_897_ = lean_ctor_get(v_afterElem_x3f_890_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v_afterElem_x3f_890_, 1);
v_sz_898_ = lean_array_size(v_fst_896_);
v___x_899_ = ((size_t)0ULL);
v_elems_900_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_896_, v_val_897_, v_sz_898_, v___x_899_, v_fst_896_);
lean_dec(v_fst_896_);
v_elems_892_ = v_elems_900_;
goto v___jp_891_;
}
else
{
lean_object* v_fst_901_; 
lean_dec(v_afterElem_x3f_890_);
v_fst_901_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_fst_901_);
lean_dec_ref(v___x_895_);
v_elems_892_ = v_fst_901_;
goto v___jp_891_;
}
v___jp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_894_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_893_, v_elems_892_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl___boxed(lean_object* v_sep_902_, lean_object* v_sepArray_903_, lean_object* v_afterElem_x3f_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(v_sep_902_, v_sepArray_903_, v_afterElem_x3f_904_);
lean_dec_ref(v_sepArray_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(lean_object* v_fst_906_, lean_object* v_val_907_, lean_object* v_as_908_, size_t v_sz_909_, size_t v_i_910_, lean_object* v_bs_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_906_, v_val_907_, v_sz_909_, v_i_910_, v_bs_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___boxed(lean_object* v_fst_913_, lean_object* v_val_914_, lean_object* v_as_915_, lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_bs_918_){
_start:
{
size_t v_sz_boxed_919_; size_t v_i_boxed_920_; lean_object* v_res_921_; 
v_sz_boxed_919_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_920_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(v_fst_913_, v_val_914_, v_as_915_, v_sz_boxed_919_, v_i_boxed_920_, v_bs_918_);
lean_dec_ref(v_as_915_);
lean_dec_ref(v_fst_913_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep(lean_object* v_sep_922_, lean_object* v_sepArray_923_, lean_object* v_afterElem_924_){
_start:
{
lean_object* v___x_925_; lean_object* v_fst_926_; lean_object* v_snd_927_; lean_object* v___y_929_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_925_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_922_, v_sepArray_923_);
v_fst_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_fst_926_);
v_snd_927_ = lean_ctor_get(v___x_925_, 1);
lean_inc(v_snd_927_);
v___x_932_ = lean_array_get_size(v_snd_927_);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_nat_dec_eq(v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_array_get_size(v_fst_926_);
v___x_936_ = lean_nat_dec_eq(v___x_932_, v___x_935_);
if (v___x_936_ == 0)
{
lean_dec(v_snd_927_);
lean_dec(v_fst_926_);
lean_dec_ref(v_afterElem_924_);
return v___x_925_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
lean_dec_ref(v___x_925_);
v___x_937_ = lean_unsigned_to_nat(1u);
v___x_938_ = lean_nat_sub(v___x_935_, v___x_937_);
v___x_939_ = lean_nat_dec_lt(v___x_938_, v___x_935_);
if (v___x_939_ == 0)
{
lean_dec(v___x_938_);
lean_dec_ref(v_afterElem_924_);
v___y_929_ = v_fst_926_;
goto v___jp_928_;
}
else
{
lean_object* v___x_940_; lean_object* v_v_941_; lean_object* v___x_942_; lean_object* v_xs_x27_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_940_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_v_941_ = lean_array_fget(v_fst_926_, v___x_938_);
v___x_942_ = lean_box(0);
v_xs_x27_943_ = lean_array_fset(v_fst_926_, v___x_938_, v___x_942_);
v___x_944_ = lean_nat_sub(v___x_932_, v___x_937_);
v___x_945_ = lean_array_get_borrowed(v___x_940_, v_snd_927_, v___x_944_);
lean_dec(v___x_944_);
v___x_946_ = lean_unsigned_to_nat(3u);
v___x_947_ = lean_mk_empty_array_with_capacity(v___x_946_);
v___x_948_ = lean_array_push(v___x_947_, v_v_941_);
v___x_949_ = lean_array_push(v___x_948_, v_afterElem_924_);
lean_inc(v___x_945_);
v___x_950_ = lean_array_push(v___x_949_, v___x_945_);
v___x_951_ = l_Lean_Fmt_TaggedDoc_join(v___x_950_);
v___x_952_ = lean_array_fset(v_xs_x27_943_, v___x_938_, v___x_951_);
lean_dec(v___x_938_);
v___y_929_ = v___x_952_;
goto v___jp_928_;
}
}
}
else
{
lean_dec(v_snd_927_);
lean_dec(v_fst_926_);
lean_dec_ref(v_afterElem_924_);
return v___x_925_;
}
v___jp_928_:
{
lean_object* v_seps_930_; lean_object* v___x_931_; 
v_seps_930_ = lean_array_pop(v_snd_927_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___y_929_);
lean_ctor_set(v___x_931_, 1, v_seps_930_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep___boxed(lean_object* v_sep_953_, lean_object* v_sepArray_954_, lean_object* v_afterElem_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep(v_sep_953_, v_sepArray_954_, v_afterElem_955_);
lean_dec_ref(v_sepArray_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0(lean_object* v___x_957_, lean_object* v_snd_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v_i_961_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_sep_968_; lean_object* v___x_969_; 
v___x_962_ = lean_array_get_borrowed(v___x_957_, v_snd_958_, v_i_961_);
v___x_963_ = lean_unsigned_to_nat(3u);
v___x_964_ = lean_mk_empty_array_with_capacity(v___x_963_);
v___x_965_ = lean_array_push(v___x_964_, v___y_959_);
lean_inc(v___x_962_);
v___x_966_ = lean_array_push(v___x_965_, v___x_962_);
v___x_967_ = lean_array_push(v___x_966_, v___y_960_);
v_sep_968_ = l_Lean_Fmt_TaggedDoc_join(v___x_967_);
lean_inc_ref(v_sep_968_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v_sep_968_);
lean_ctor_set(v___x_969_, 1, v_sep_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0___boxed(lean_object* v___x_970_, lean_object* v_snd_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v_i_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0(v___x_970_, v_snd_971_, v___y_972_, v___y_973_, v_i_974_);
lean_dec(v_i_974_);
lean_dec_ref(v_snd_971_);
lean_dec_ref(v___x_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(lean_object* v_sep_976_, lean_object* v_sepArray_977_, lean_object* v_afterElem_x3f_978_, lean_object* v_afterSep_x3f_979_){
_start:
{
lean_object* v___x_980_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_990_; 
v___x_980_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (lean_obj_tag(v_afterElem_x3f_978_) == 0)
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_990_ = v___x_993_;
goto v___jp_989_;
}
else
{
lean_object* v_val_994_; 
v_val_994_ = lean_ctor_get(v_afterElem_x3f_978_, 0);
lean_inc(v_val_994_);
lean_dec_ref_known(v_afterElem_x3f_978_, 1);
v___y_990_ = v_val_994_;
goto v___jp_989_;
}
v___jp_981_:
{
lean_object* v___x_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___f_987_; lean_object* v___x_988_; 
lean_inc_ref(v___y_982_);
v___x_984_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep(v_sep_976_, v_sepArray_977_, v___y_982_);
v_fst_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_fst_985_);
v_snd_986_ = lean_ctor_get(v___x_984_, 1);
lean_inc(v_snd_986_);
lean_dec_ref(v___x_984_);
v___f_987_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___lam__0___boxed), 5, 4);
lean_closure_set(v___f_987_, 0, v___x_980_);
lean_closure_set(v___f_987_, 1, v_snd_986_);
lean_closure_set(v___f_987_, 2, v___y_982_);
lean_closure_set(v___f_987_, 3, v___y_983_);
v___x_988_ = l_Lean_Fmt_TaggedDoc_fillWith(v_fst_985_, v___f_987_);
return v___x_988_;
}
v___jp_989_:
{
if (lean_obj_tag(v_afterSep_x3f_979_) == 0)
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_982_ = v___y_990_;
v___y_983_ = v___x_991_;
goto v___jp_981_;
}
else
{
lean_object* v_val_992_; 
v_val_992_ = lean_ctor_get(v_afterSep_x3f_979_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v_afterSep_x3f_979_, 1);
v___y_982_ = v___y_990_;
v___y_983_ = v_val_992_;
goto v___jp_981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___boxed(lean_object* v_sep_995_, lean_object* v_sepArray_996_, lean_object* v_afterElem_x3f_997_, lean_object* v_afterSep_x3f_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(v_sep_995_, v_sepArray_996_, v_afterElem_x3f_997_, v_afterSep_x3f_998_);
lean_dec_ref(v_sepArray_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0(lean_object* v___x_1000_, lean_object* v_snd_1001_, lean_object* v___y_1002_, lean_object* v_i_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_sep_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1004_ = lean_array_get_borrowed(v___x_1000_, v_snd_1001_, v_i_1003_);
v___x_1005_ = lean_unsigned_to_nat(2u);
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_1005_);
lean_inc_ref(v___x_1006_);
v___x_1007_ = lean_array_push(v___x_1006_, v___y_1002_);
lean_inc(v___x_1004_);
v___x_1008_ = lean_array_push(v___x_1007_, v___x_1004_);
v_sep_1009_ = l_Lean_Fmt_TaggedDoc_join(v___x_1008_);
v___x_1010_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v_sep_1009_);
v___x_1011_ = lean_array_push(v___x_1006_, v_sep_1009_);
v___x_1012_ = lean_array_push(v___x_1011_, v___x_1010_);
v___x_1013_ = l_Lean_Fmt_TaggedDoc_join(v___x_1012_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_sep_1009_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0___boxed(lean_object* v___x_1015_, lean_object* v_snd_1016_, lean_object* v___y_1017_, lean_object* v_i_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0(v___x_1015_, v_snd_1016_, v___y_1017_, v_i_1018_);
lean_dec(v_i_1018_);
lean_dec_ref(v_snd_1016_);
lean_dec_ref(v___x_1015_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(lean_object* v_sep_1020_, lean_object* v_sepArray_1021_, lean_object* v_afterElem_x3f_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___y_1025_; 
v___x_1023_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (lean_obj_tag(v_afterElem_x3f_1022_) == 0)
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1025_ = v___x_1031_;
goto v___jp_1024_;
}
else
{
lean_object* v_val_1032_; 
v_val_1032_ = lean_ctor_get(v_afterElem_x3f_1022_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v_afterElem_x3f_1022_, 1);
v___y_1025_ = v_val_1032_;
goto v___jp_1024_;
}
v___jp_1024_:
{
lean_object* v___x_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; 
lean_inc_ref(v___y_1025_);
v___x_1026_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_splitAttachingTrailingSep(v_sep_1020_, v_sepArray_1021_, v___y_1025_);
v_fst_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_fst_1027_);
v_snd_1028_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_snd_1028_);
lean_dec_ref(v___x_1026_);
v___f_1029_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1029_, 0, v___x_1023_);
lean_closure_set(v___f_1029_, 1, v_snd_1028_);
lean_closure_set(v___f_1029_, 2, v___y_1025_);
v___x_1030_ = l_Lean_Fmt_TaggedDoc_fillWith(v_fst_1027_, v___f_1029_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___boxed(lean_object* v_sep_1033_, lean_object* v_sepArray_1034_, lean_object* v_afterElem_x3f_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(v_sep_1033_, v_sepArray_1034_, v_afterElem_x3f_1035_);
lean_dec_ref(v_sepArray_1034_);
return v_res_1036_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepArray___closed__0(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = l_Lean_Fmt_TaggedDoc_space;
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object* v_sep_1039_, lean_object* v_sepArray_1040_, lean_object* v_format_1041_){
_start:
{
lean_object* v___x_1042_; uint8_t v___y_1044_; 
v___x_1042_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
switch(lean_obj_tag(v_format_1041_))
{
case 1:
{
uint8_t v_trailingSep_1072_; 
v_trailingSep_1072_ = lean_ctor_get_uint8(v_format_1041_, sizeof(void*)*1 + 1);
v___y_1044_ = v_trailingSep_1072_;
goto v___jp_1043_;
}
case 3:
{
uint8_t v_trailingSep_1073_; 
v_trailingSep_1073_ = lean_ctor_get_uint8(v_format_1041_, sizeof(void*)*1);
v___y_1044_ = v_trailingSep_1073_;
goto v___jp_1043_;
}
default: 
{
uint8_t v_trailingSep_1074_; 
v_trailingSep_1074_ = lean_ctor_get_uint8(v_format_1041_, sizeof(void*)*2);
v___y_1044_ = v_trailingSep_1074_;
goto v___jp_1043_;
}
}
v___jp_1043_:
{
lean_object* v_sepArray_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
lean_inc_ref(v_sep_1039_);
v_sepArray_1045_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_1039_, v_sepArray_1040_, v___y_1044_);
v___x_1046_ = lean_array_get_size(v_sepArray_1045_);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = lean_nat_dec_eq(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = lean_nat_dec_eq(v___x_1046_, v___x_1049_);
if (v___x_1050_ == 0)
{
switch(lean_obj_tag(v_format_1041_))
{
case 0:
{
lean_object* v_afterElem_x3f_1051_; lean_object* v_afterSep_x3f_1052_; lean_object* v___x_1053_; 
v_afterElem_x3f_1051_ = lean_ctor_get(v_format_1041_, 0);
lean_inc(v_afterElem_x3f_1051_);
v_afterSep_x3f_1052_ = lean_ctor_get(v_format_1041_, 1);
lean_inc(v_afterSep_x3f_1052_);
lean_dec_ref_known(v_format_1041_, 2);
v___x_1053_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(v_sep_1039_, v_sepArray_1045_, v_afterElem_x3f_1051_, v_afterSep_x3f_1052_);
return v___x_1053_;
}
case 1:
{
uint8_t v_allowFlattening_1054_; lean_object* v_afterElem_x3f_1055_; lean_object* v_joinedUsingNl_1056_; 
v_allowFlattening_1054_ = lean_ctor_get_uint8(v_format_1041_, sizeof(void*)*1);
v_afterElem_x3f_1055_ = lean_ctor_get(v_format_1041_, 0);
lean_inc_n(v_afterElem_x3f_1055_, 2);
lean_dec_ref_known(v_format_1041_, 1);
lean_inc_ref(v_sep_1039_);
v_joinedUsingNl_1056_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(v_sep_1039_, v_sepArray_1045_, v_afterElem_x3f_1055_);
if (v_allowFlattening_1054_ == 0)
{
lean_dec(v_afterElem_x3f_1055_);
lean_dec_ref(v_sepArray_1045_);
lean_dec_ref(v_sep_1039_);
return v_joinedUsingNl_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1057_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepArray___closed__0, &l_Lean_Fmt_Layouts_sepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_sepArray___closed__0);
v___x_1058_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(v_sep_1039_, v_sepArray_1045_, v_afterElem_x3f_1055_, v___x_1057_);
v___x_1059_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1058_);
v___x_1060_ = lean_unsigned_to_nat(2u);
v___x_1061_ = lean_mk_empty_array_with_capacity(v___x_1060_);
v___x_1062_ = lean_array_push(v___x_1061_, v___x_1059_);
v___x_1063_ = lean_array_push(v___x_1062_, v_joinedUsingNl_1056_);
v___x_1064_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1063_);
return v___x_1064_;
}
}
case 2:
{
lean_object* v_afterElem_x3f_1065_; lean_object* v_afterSep_x3f_1066_; lean_object* v___x_1067_; 
v_afterElem_x3f_1065_ = lean_ctor_get(v_format_1041_, 0);
lean_inc(v_afterElem_x3f_1065_);
v_afterSep_x3f_1066_ = lean_ctor_get(v_format_1041_, 1);
lean_inc(v_afterSep_x3f_1066_);
lean_dec_ref_known(v_format_1041_, 2);
v___x_1067_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(v_sep_1039_, v_sepArray_1045_, v_afterElem_x3f_1065_, v_afterSep_x3f_1066_);
lean_dec_ref(v_sepArray_1045_);
return v___x_1067_;
}
default: 
{
lean_object* v_afterElem_x3f_1068_; lean_object* v___x_1069_; 
v_afterElem_x3f_1068_ = lean_ctor_get(v_format_1041_, 0);
lean_inc(v_afterElem_x3f_1068_);
lean_dec_ref_known(v_format_1041_, 1);
v___x_1069_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(v_sep_1039_, v_sepArray_1045_, v_afterElem_x3f_1068_);
lean_dec_ref(v_sepArray_1045_);
return v___x_1069_;
}
}
}
else
{
lean_object* v___x_1070_; 
lean_dec_ref(v_format_1041_);
lean_dec_ref(v_sep_1039_);
v___x_1070_ = lean_array_get(v___x_1042_, v_sepArray_1045_, v___x_1047_);
lean_dec_ref(v_sepArray_1045_);
return v___x_1070_;
}
}
else
{
lean_object* v___x_1071_; 
lean_dec_ref(v_sepArray_1045_);
lean_dec_ref(v_format_1041_);
lean_dec_ref(v_sep_1039_);
v___x_1071_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray___boxed(lean_object* v_sep_1075_, lean_object* v_sepArray_1076_, lean_object* v_format_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1075_, v_sepArray_1076_, v_format_1077_);
lean_dec_ref(v_sepArray_1076_);
return v_res_1078_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepLines___closed__0(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepLines___closed__1(void){
_start:
{
uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1081_ = 1;
v___x_1082_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepLines___closed__0, &l_Lean_Fmt_Layouts_sepLines___closed__0_once, _init_l_Lean_Fmt_Layouts_sepLines___closed__0);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1082_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*2, v___x_1081_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines(lean_object* v_sep_1085_, lean_object* v_lines_1086_, uint8_t v_includeSeps_1087_){
_start:
{
if (v_includeSeps_1087_ == 0)
{
lean_object* v___x_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = 1;
v___x_1090_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*1, v_includeSeps_1087_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*1 + 1, v___x_1089_);
v___x_1091_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1085_, v_lines_1086_, v___x_1090_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepLines___closed__1, &l_Lean_Fmt_Layouts_sepLines___closed__1_once, _init_l_Lean_Fmt_Layouts_sepLines___closed__1);
v___x_1093_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1085_, v_lines_1086_, v___x_1092_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines___boxed(lean_object* v_sep_1094_, lean_object* v_lines_1095_, lean_object* v_includeSeps_1096_){
_start:
{
uint8_t v_includeSeps_boxed_1097_; lean_object* v_res_1098_; 
v_includeSeps_boxed_1097_ = lean_unbox(v_includeSeps_1096_);
v_res_1098_ = l_Lean_Fmt_Layouts_sepLines(v_sep_1094_, v_lines_1095_, v_includeSeps_boxed_1097_);
lean_dec_ref(v_lines_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object* v_sep_1102_, lean_object* v_elems_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_Fmt_Layouts_sepFill___closed__0));
v___x_1105_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1102_, v_elems_1103_, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill___boxed(lean_object* v_sep_1106_, lean_object* v_elems_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Fmt_Layouts_sepFill(v_sep_1106_, v_elems_1107_);
lean_dec_ref(v_elems_1107_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2(void){
_start:
{
uint8_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = 1;
v___x_1116_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1);
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v___x_1116_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*2, v___x_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical(lean_object* v_sep_1119_, lean_object* v_elems_1120_, uint8_t v_includeSeps_1121_){
_start:
{
uint8_t v___x_1122_; lean_object* v_elems_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1122_ = 1;
lean_inc_ref(v_sep_1119_);
v_elems_1123_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_1119_, v_elems_1120_, v___x_1122_);
v___x_1124_ = lean_array_get_size(v_elems_1123_);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_dec_eq(v___x_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
if (v_includeSeps_1121_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0));
v___x_1128_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1119_, v_elems_1123_, v___x_1127_);
lean_dec_ref(v_elems_1123_);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v___x_1130_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1119_, v_elems_1123_, v___x_1129_);
lean_dec_ref(v_elems_1123_);
v___x_1131_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_1130_);
return v___x_1131_;
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v_sep_1119_);
v___x_1132_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get(v___x_1132_, v_elems_1123_, v___x_1133_);
lean_dec_ref(v_elems_1123_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___boxed(lean_object* v_sep_1135_, lean_object* v_elems_1136_, lean_object* v_includeSeps_1137_){
_start:
{
uint8_t v_includeSeps_boxed_1138_; lean_object* v_res_1139_; 
v_includeSeps_boxed_1138_ = lean_unbox(v_includeSeps_1137_);
v_res_1139_ = l_Lean_Fmt_Layouts_sepHorizontalOrVertical(v_sep_1135_, v_elems_1136_, v_includeSeps_boxed_1138_);
lean_dec_ref(v_elems_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(lean_object* v___x_1140_, lean_object* v_docsWithIntermediateWhitespace_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_fst_1143_; lean_object* v_snd_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1173_; 
v_fst_1143_ = lean_ctor_get(v_a_1142_, 0);
v_snd_1144_ = lean_ctor_get(v_a_1142_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_a_1142_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1146_ = v_a_1142_;
v_isShared_1147_ = v_isSharedCheck_1173_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_snd_1144_);
lean_inc(v_fst_1143_);
lean_dec(v_a_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1173_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_nat_dec_lt(v_snd_1144_, v___x_1140_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1150_; 
if (v_isShared_1147_ == 0)
{
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_fst_1143_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_snd_1144_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v___f_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___y_1157_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___f_1152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_1153_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = lean_array_get_borrowed(v___x_1153_, v_docsWithIntermediateWhitespace_1141_, v_snd_1144_);
v___x_1168_ = lean_nat_add(v_snd_1144_, v___x_1154_);
v___x_1169_ = lean_array_get_size(v_docsWithIntermediateWhitespace_1141_);
v___x_1170_ = lean_nat_dec_lt(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_dec(v___x_1168_);
v___x_1171_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1157_ = v___x_1171_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_array_fget_borrowed(v_docsWithIntermediateWhitespace_1141_, v___x_1168_);
lean_dec(v___x_1168_);
lean_inc(v___x_1172_);
v___y_1157_ = v___x_1172_;
goto v___jp_1156_;
}
v___jp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_inc(v___x_1155_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1155_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___y_1157_);
lean_ctor_set(v___x_1159_, 1, v___f_1152_);
v___x_1160_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1158_, v___x_1159_);
v___x_1161_ = lean_array_push(v_fst_1143_, v___x_1160_);
v___x_1162_ = lean_unsigned_to_nat(2u);
v___x_1163_ = lean_nat_add(v_snd_1144_, v___x_1162_);
lean_dec(v_snd_1144_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v___x_1163_);
lean_ctor_set(v___x_1146_, 0, v___x_1161_);
v___x_1165_ = v___x_1146_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
v_a_1142_ = v___x_1165_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg___boxed(lean_object* v___x_1174_, lean_object* v_docsWithIntermediateWhitespace_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1174_, v_docsWithIntermediateWhitespace_1175_, v_a_1176_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1175_);
lean_dec(v___x_1174_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace(lean_object* v_docsWithIntermediateWhitespace_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1184_ = lean_array_get_size(v_docsWithIntermediateWhitespace_1183_);
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = lean_nat_dec_eq(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_dec_eq(v___x_1184_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_fst_1191_; lean_object* v___x_1192_; 
v___x_1189_ = ((lean_object*)(l_Lean_Fmt_Layouts_retainedWhitespace___closed__1));
v___x_1190_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1184_, v_docsWithIntermediateWhitespace_1183_, v___x_1189_);
v_fst_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_fst_1191_);
lean_dec_ref(v___x_1190_);
v___x_1192_ = l_Lean_Fmt_TaggedDoc_combine(v_fst_1191_);
lean_dec(v_fst_1191_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1194_ = lean_array_get_borrowed(v___x_1193_, v_docsWithIntermediateWhitespace_1183_, v___x_1185_);
lean_inc(v___x_1194_);
return v___x_1194_;
}
}
else
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___boxed(lean_object* v_docsWithIntermediateWhitespace_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Fmt_Layouts_retainedWhitespace(v_docsWithIntermediateWhitespace_1196_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(lean_object* v___x_1198_, lean_object* v_docsWithIntermediateWhitespace_1199_, lean_object* v_inst_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1198_, v_docsWithIntermediateWhitespace_1199_, v_a_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___boxed(lean_object* v___x_1203_, lean_object* v_docsWithIntermediateWhitespace_1204_, lean_object* v_inst_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(v___x_1203_, v_docsWithIntermediateWhitespace_1204_, v_inst_1205_, v_a_1206_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1204_);
lean_dec(v___x_1203_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1___redArg(lean_object* v_v_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1(lean_object* v_00_u03c4_1210_, lean_object* v_v_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(lean_object* v_a_1213_, lean_object* v_x_1214_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 0)
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_box(0);
return v___x_1215_;
}
else
{
lean_object* v_key_1216_; lean_object* v_value_1217_; lean_object* v_tail_1218_; size_t v_ptr_1219_; size_t v_ptr_1220_; uint8_t v___x_1221_; 
v_key_1216_ = lean_ctor_get(v_x_1214_, 0);
v_value_1217_ = lean_ctor_get(v_x_1214_, 1);
v_tail_1218_ = lean_ctor_get(v_x_1214_, 2);
v_ptr_1219_ = lean_ctor_get_usize(v_key_1216_, 1);
v_ptr_1220_ = lean_ctor_get_usize(v_a_1213_, 1);
v___x_1221_ = lean_usize_dec_eq(v_ptr_1219_, v_ptr_1220_);
if (v___x_1221_ == 0)
{
v_x_1214_ = v_tail_1218_;
goto _start;
}
else
{
lean_object* v___x_1223_; 
lean_inc(v_value_1217_);
v___x_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_value_1217_);
return v___x_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg___boxed(lean_object* v_a_1224_, lean_object* v_x_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1224_, v_x_1225_);
lean_dec(v_x_1225_);
lean_dec_ref(v_a_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(lean_object* v_m_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_buckets_1229_; size_t v_ptr_1230_; lean_object* v___x_1231_; uint64_t v___x_1232_; uint64_t v___x_1233_; uint64_t v___x_1234_; uint64_t v_fold_1235_; uint64_t v___x_1236_; uint64_t v___x_1237_; uint64_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_buckets_1229_ = lean_ctor_get(v_m_1227_, 1);
v_ptr_1230_ = lean_ctor_get_usize(v_a_1228_, 1);
v___x_1231_ = lean_array_get_size(v_buckets_1229_);
v___x_1232_ = lean_usize_to_uint64(v_ptr_1230_);
v___x_1233_ = 32ULL;
v___x_1234_ = lean_uint64_shift_right(v___x_1232_, v___x_1233_);
v_fold_1235_ = lean_uint64_xor(v___x_1232_, v___x_1234_);
v___x_1236_ = 16ULL;
v___x_1237_ = lean_uint64_shift_right(v_fold_1235_, v___x_1236_);
v___x_1238_ = lean_uint64_xor(v_fold_1235_, v___x_1237_);
v___x_1239_ = lean_uint64_to_usize(v___x_1238_);
v___x_1240_ = lean_usize_of_nat(v___x_1231_);
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_sub(v___x_1240_, v___x_1241_);
v___x_1243_ = lean_usize_land(v___x_1239_, v___x_1242_);
v___x_1244_ = lean_array_uget_borrowed(v_buckets_1229_, v___x_1243_);
v___x_1245_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1228_, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg___boxed(lean_object* v_m_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1246_, v_a_1247_);
lean_dec_ref(v_a_1247_);
lean_dec_ref(v_m_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(lean_object* v_a_1249_, lean_object* v_b_1250_, lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
lean_dec(v_b_1250_);
lean_dec_ref(v_a_1249_);
return v_x_1251_;
}
else
{
lean_object* v_key_1252_; lean_object* v_value_1253_; lean_object* v_tail_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1268_; 
v_key_1252_ = lean_ctor_get(v_x_1251_, 0);
v_value_1253_ = lean_ctor_get(v_x_1251_, 1);
v_tail_1254_ = lean_ctor_get(v_x_1251_, 2);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_x_1251_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1256_ = v_x_1251_;
v_isShared_1257_ = v_isSharedCheck_1268_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_tail_1254_);
lean_inc(v_value_1253_);
lean_inc(v_key_1252_);
lean_dec(v_x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1268_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
size_t v_ptr_1258_; size_t v_ptr_1259_; uint8_t v___x_1260_; 
v_ptr_1258_ = lean_ctor_get_usize(v_key_1252_, 1);
v_ptr_1259_ = lean_ctor_get_usize(v_a_1249_, 1);
v___x_1260_ = lean_usize_dec_eq(v_ptr_1258_, v_ptr_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1249_, v_b_1250_, v_tail_1254_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 2, v___x_1261_);
v___x_1263_ = v___x_1256_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_key_1252_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_value_1253_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
else
{
lean_object* v___x_1266_; 
lean_dec(v_value_1253_);
lean_dec(v_key_1252_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_b_1250_);
lean_ctor_set(v___x_1256_, 0, v_a_1249_);
v___x_1266_ = v___x_1256_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1249_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_b_1250_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_tail_1254_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 0)
{
return v_x_1269_;
}
else
{
lean_object* v_key_1271_; lean_object* v_value_1272_; lean_object* v_tail_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1297_; 
v_key_1271_ = lean_ctor_get(v_x_1270_, 0);
v_value_1272_ = lean_ctor_get(v_x_1270_, 1);
v_tail_1273_ = lean_ctor_get(v_x_1270_, 2);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_x_1270_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1275_ = v_x_1270_;
v_isShared_1276_ = v_isSharedCheck_1297_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_tail_1273_);
lean_inc(v_value_1272_);
lean_inc(v_key_1271_);
lean_dec(v_x_1270_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1297_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
size_t v_ptr_1277_; lean_object* v___x_1278_; uint64_t v___x_1279_; uint64_t v___x_1280_; uint64_t v___x_1281_; uint64_t v_fold_1282_; uint64_t v___x_1283_; uint64_t v___x_1284_; uint64_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v_ptr_1277_ = lean_ctor_get_usize(v_key_1271_, 1);
v___x_1278_ = lean_array_get_size(v_x_1269_);
v___x_1279_ = lean_usize_to_uint64(v_ptr_1277_);
v___x_1280_ = 32ULL;
v___x_1281_ = lean_uint64_shift_right(v___x_1279_, v___x_1280_);
v_fold_1282_ = lean_uint64_xor(v___x_1279_, v___x_1281_);
v___x_1283_ = 16ULL;
v___x_1284_ = lean_uint64_shift_right(v_fold_1282_, v___x_1283_);
v___x_1285_ = lean_uint64_xor(v_fold_1282_, v___x_1284_);
v___x_1286_ = lean_uint64_to_usize(v___x_1285_);
v___x_1287_ = lean_usize_of_nat(v___x_1278_);
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = lean_usize_sub(v___x_1287_, v___x_1288_);
v___x_1290_ = lean_usize_land(v___x_1286_, v___x_1289_);
v___x_1291_ = lean_array_uget_borrowed(v_x_1269_, v___x_1290_);
lean_inc(v___x_1291_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 2, v___x_1291_);
v___x_1293_ = v___x_1275_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_key_1271_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_value_1272_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_array_uset(v_x_1269_, v___x_1290_, v___x_1293_);
v_x_1269_ = v___x_1294_;
v_x_1270_ = v_tail_1273_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(lean_object* v_i_1298_, lean_object* v_source_1299_, lean_object* v_target_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = lean_array_get_size(v_source_1299_);
v___x_1302_ = lean_nat_dec_lt(v_i_1298_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v_source_1299_);
lean_dec(v_i_1298_);
return v_target_1300_;
}
else
{
lean_object* v_es_1303_; lean_object* v___x_1304_; lean_object* v_source_1305_; lean_object* v_target_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_es_1303_ = lean_array_fget(v_source_1299_, v_i_1298_);
v___x_1304_ = lean_box(0);
v_source_1305_ = lean_array_fset(v_source_1299_, v_i_1298_, v___x_1304_);
v_target_1306_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_target_1300_, v_es_1303_);
v___x_1307_ = lean_unsigned_to_nat(1u);
v___x_1308_ = lean_nat_add(v_i_1298_, v___x_1307_);
lean_dec(v_i_1298_);
v_i_1298_ = v___x_1308_;
v_source_1299_ = v_source_1305_;
v_target_1300_ = v_target_1306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(lean_object* v_data_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_nbuckets_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1311_ = lean_array_get_size(v_data_1310_);
v___x_1312_ = lean_unsigned_to_nat(2u);
v_nbuckets_1313_ = lean_nat_mul(v___x_1311_, v___x_1312_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_mk_array(v_nbuckets_1313_, v___x_1315_);
v___x_1317_ = lean_array_propagate_mark(v_data_1310_, v___x_1316_);
v___x_1318_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v___x_1314_, v_data_1310_, v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(lean_object* v_a_1319_, lean_object* v_x_1320_){
_start:
{
if (lean_obj_tag(v_x_1320_) == 0)
{
uint8_t v___x_1321_; 
v___x_1321_ = 0;
return v___x_1321_;
}
else
{
lean_object* v_key_1322_; lean_object* v_tail_1323_; size_t v_ptr_1324_; size_t v_ptr_1325_; uint8_t v___x_1326_; 
v_key_1322_ = lean_ctor_get(v_x_1320_, 0);
v_tail_1323_ = lean_ctor_get(v_x_1320_, 2);
v_ptr_1324_ = lean_ctor_get_usize(v_key_1322_, 1);
v_ptr_1325_ = lean_ctor_get_usize(v_a_1319_, 1);
v___x_1326_ = lean_usize_dec_eq(v_ptr_1324_, v_ptr_1325_);
if (v___x_1326_ == 0)
{
v_x_1320_ = v_tail_1323_;
goto _start;
}
else
{
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg___boxed(lean_object* v_a_1328_, lean_object* v_x_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1328_, v_x_1329_);
lean_dec(v_x_1329_);
lean_dec_ref(v_a_1328_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(lean_object* v_m_1332_, lean_object* v_a_1333_, lean_object* v_b_1334_){
_start:
{
lean_object* v_size_1335_; lean_object* v_buckets_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1380_; 
v_size_1335_ = lean_ctor_get(v_m_1332_, 0);
v_buckets_1336_ = lean_ctor_get(v_m_1332_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_m_1332_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1338_ = v_m_1332_;
v_isShared_1339_ = v_isSharedCheck_1380_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_buckets_1336_);
lean_inc(v_size_1335_);
lean_dec(v_m_1332_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1380_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
size_t v_ptr_1340_; lean_object* v___x_1341_; uint64_t v___x_1342_; uint64_t v___x_1343_; uint64_t v___x_1344_; uint64_t v_fold_1345_; uint64_t v___x_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; lean_object* v_bkt_1354_; uint8_t v___x_1355_; 
v_ptr_1340_ = lean_ctor_get_usize(v_a_1333_, 1);
v___x_1341_ = lean_array_get_size(v_buckets_1336_);
v___x_1342_ = lean_usize_to_uint64(v_ptr_1340_);
v___x_1343_ = 32ULL;
v___x_1344_ = lean_uint64_shift_right(v___x_1342_, v___x_1343_);
v_fold_1345_ = lean_uint64_xor(v___x_1342_, v___x_1344_);
v___x_1346_ = 16ULL;
v___x_1347_ = lean_uint64_shift_right(v_fold_1345_, v___x_1346_);
v___x_1348_ = lean_uint64_xor(v_fold_1345_, v___x_1347_);
v___x_1349_ = lean_uint64_to_usize(v___x_1348_);
v___x_1350_ = lean_usize_of_nat(v___x_1341_);
v___x_1351_ = ((size_t)1ULL);
v___x_1352_ = lean_usize_sub(v___x_1350_, v___x_1351_);
v___x_1353_ = lean_usize_land(v___x_1349_, v___x_1352_);
v_bkt_1354_ = lean_array_uget_borrowed(v_buckets_1336_, v___x_1353_);
v___x_1355_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1333_, v_bkt_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v_size_x27_1357_; lean_object* v___x_1358_; lean_object* v_buckets_x27_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1356_ = lean_unsigned_to_nat(1u);
v_size_x27_1357_ = lean_nat_add(v_size_1335_, v___x_1356_);
lean_dec(v_size_1335_);
lean_inc(v_bkt_1354_);
v___x_1358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1358_, 0, v_a_1333_);
lean_ctor_set(v___x_1358_, 1, v_b_1334_);
lean_ctor_set(v___x_1358_, 2, v_bkt_1354_);
v_buckets_x27_1359_ = lean_array_uset(v_buckets_1336_, v___x_1353_, v___x_1358_);
v___x_1360_ = lean_unsigned_to_nat(4u);
v___x_1361_ = lean_nat_mul(v_size_x27_1357_, v___x_1360_);
v___x_1362_ = lean_unsigned_to_nat(3u);
v___x_1363_ = lean_nat_div(v___x_1361_, v___x_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_array_get_size(v_buckets_x27_1359_);
v___x_1365_ = lean_nat_dec_le(v___x_1363_, v___x_1364_);
lean_dec(v___x_1363_);
if (v___x_1365_ == 0)
{
lean_object* v_val_1366_; lean_object* v___x_1368_; 
v_val_1366_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_buckets_x27_1359_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v_val_1366_);
lean_ctor_set(v___x_1338_, 0, v_size_x27_1357_);
v___x_1368_ = v___x_1338_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_size_x27_1357_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_val_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
else
{
lean_object* v___x_1371_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v_buckets_x27_1359_);
lean_ctor_set(v___x_1338_, 0, v_size_x27_1357_);
v___x_1371_ = v___x_1338_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_size_x27_1357_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_buckets_x27_1359_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
else
{
lean_object* v___x_1373_; lean_object* v_buckets_x27_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
lean_inc(v_bkt_1354_);
v___x_1373_ = lean_box(0);
v_buckets_x27_1374_ = lean_array_uset(v_buckets_1336_, v___x_1353_, v___x_1373_);
v___x_1375_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1333_, v_b_1334_, v_bkt_1354_);
v___x_1376_ = lean_array_uset(v_buckets_x27_1374_, v___x_1353_, v___x_1375_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v___x_1376_);
v___x_1378_ = v___x_1338_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_size_1335_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___y_1384_; 
switch(lean_obj_tag(v_a_1381_))
{
case 1:
{
lean_dec_ref_known(v_a_1381_, 2);
v___y_1384_ = v_a_1382_;
goto v___jp_1383_;
}
case 2:
{
lean_dec_ref_known(v_a_1381_, 2);
v___y_1384_ = v_a_1382_;
goto v___jp_1383_;
}
case 3:
{
lean_object* v_d_1388_; lean_object* v___x_1389_; 
v_d_1388_ = lean_ctor_get(v_a_1381_, 2);
lean_inc(v_d_1388_);
lean_dec_ref_known(v_a_1381_, 3);
v___x_1389_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1388_, v_a_1382_);
return v___x_1389_;
}
case 4:
{
lean_object* v_d_1390_; lean_object* v___x_1391_; 
v_d_1390_ = lean_ctor_get(v_a_1381_, 1);
lean_inc(v_d_1390_);
lean_dec_ref_known(v_a_1381_, 2);
v___x_1391_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1390_, v_a_1382_);
return v___x_1391_;
}
case 5:
{
lean_object* v_d_1392_; lean_object* v___x_1393_; 
v_d_1392_ = lean_ctor_get(v_a_1381_, 1);
lean_inc(v_d_1392_);
lean_dec_ref_known(v_a_1381_, 2);
v___x_1393_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1392_, v_a_1382_);
return v___x_1393_;
}
case 6:
{
lean_object* v_d_1394_; lean_object* v___x_1395_; 
v_d_1394_ = lean_ctor_get(v_a_1381_, 2);
lean_inc(v_d_1394_);
lean_dec_ref_known(v_a_1381_, 3);
v___x_1395_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1394_, v_a_1382_);
return v___x_1395_;
}
case 7:
{
uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec_ref_known(v_a_1381_, 2);
v___x_1396_ = 1;
v___x_1397_ = lean_box(v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v_a_1382_);
return v___x_1398_;
}
case 8:
{
lean_object* v_d_1399_; lean_object* v___x_1400_; 
v_d_1399_ = lean_ctor_get(v_a_1381_, 1);
lean_inc(v_d_1399_);
lean_dec_ref_known(v_a_1381_, 2);
v___x_1400_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1399_, v_a_1382_);
return v___x_1400_;
}
case 9:
{
lean_object* v_d_1401_; lean_object* v___x_1402_; 
v_d_1401_ = lean_ctor_get(v_a_1381_, 1);
lean_inc(v_d_1401_);
lean_dec_ref_known(v_a_1381_, 2);
v___x_1402_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1401_, v_a_1382_);
return v___x_1402_;
}
case 10:
{
lean_object* v_d_1403_; lean_object* v___x_1404_; 
v_d_1403_ = lean_ctor_get(v_a_1381_, 1);
lean_inc(v_d_1403_);
lean_dec_ref_known(v_a_1381_, 2);
v___x_1404_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1403_, v_a_1382_);
return v___x_1404_;
}
case 11:
{
lean_object* v_d_1405_; lean_object* v___x_1406_; 
v_d_1405_ = lean_ctor_get(v_a_1381_, 1);
lean_inc(v_d_1405_);
lean_dec_ref_known(v_a_1381_, 2);
v___x_1406_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1405_, v_a_1382_);
return v___x_1406_;
}
case 12:
{
lean_object* v_d_1407_; lean_object* v___x_1408_; 
v_d_1407_ = lean_ctor_get(v_a_1381_, 2);
lean_inc(v_d_1407_);
lean_dec_ref_known(v_a_1381_, 3);
v___x_1408_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1407_, v_a_1382_);
return v___x_1408_;
}
case 13:
{
lean_object* v_d_1409_; lean_object* v___x_1410_; 
v_d_1409_ = lean_ctor_get(v_a_1381_, 2);
lean_inc(v_d_1409_);
lean_dec_ref_known(v_a_1381_, 3);
v___x_1410_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1409_, v_a_1382_);
return v___x_1410_;
}
case 14:
{
lean_object* v_a_1411_; lean_object* v_b_1412_; lean_object* v___x_1413_; lean_object* v_fst_1414_; lean_object* v_snd_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_a_1411_ = lean_ctor_get(v_a_1381_, 1);
lean_inc(v_a_1411_);
v_b_1412_ = lean_ctor_get(v_a_1381_, 2);
lean_inc(v_b_1412_);
lean_dec_ref_known(v_a_1381_, 3);
v___x_1413_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_a_1411_, v_a_1382_);
v_fst_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_fst_1414_);
v_snd_1415_ = lean_ctor_get(v___x_1413_, 1);
lean_inc(v_snd_1415_);
lean_dec_ref(v___x_1413_);
v___x_1416_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_b_1412_, v_snd_1415_);
v___x_1417_ = lean_unbox(v_fst_1414_);
if (v___x_1417_ == 0)
{
lean_object* v_snd_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_snd_1418_ = lean_ctor_get(v___x_1416_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1416_, 0);
lean_dec(v_unused_1426_);
v___x_1420_ = v___x_1416_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_snd_1418_);
lean_dec(v___x_1416_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v_fst_1414_);
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_fst_1414_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_snd_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_dec(v_fst_1414_);
return v___x_1416_;
}
}
default: 
{
uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec(v_a_1381_);
v___x_1427_ = 0;
v___x_1428_ = lean_box(v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v_a_1382_);
return v___x_1429_;
}
}
v___jp_1383_:
{
uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = 0;
v___x_1386_ = lean_box(v___x_1385_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v___y_1384_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(lean_object* v_v_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_cacheKey_1432_; lean_object* v___x_1433_; 
lean_inc(v_v_1430_);
v_cacheKey_1432_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1430_);
v___x_1433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_a_1431_, v_cacheKey_1432_);
if (lean_obj_tag(v___x_1433_) == 1)
{
lean_object* v_val_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v_cacheKey_1432_);
lean_dec(v_v_1430_);
v_val_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_val_1434_);
lean_ctor_set(v___x_1435_, 1, v_a_1431_);
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; lean_object* v_fst_1437_; lean_object* v_snd_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v___x_1433_);
v___x_1436_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_v_1430_, v_a_1431_);
v_fst_1437_ = lean_ctor_get(v___x_1436_, 0);
v_snd_1438_ = lean_ctor_get(v___x_1436_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1440_ = v___x_1436_;
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_snd_1438_);
lean_inc(v_fst_1437_);
lean_dec(v___x_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
lean_inc(v_fst_1437_);
v___x_1442_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_snd_1438_, v_cacheKey_1432_, v_fst_1437_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 1, v___x_1442_);
v___x_1444_ = v___x_1440_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_fst_1437_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go(lean_object* v_00_u03c4_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_a_1448_, v_a_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized(lean_object* v_00_u03c4_1451_, lean_object* v_v_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1452_, v_a_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(lean_object* v_00_u03c4_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_m_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1457_, v_a_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___boxed(lean_object* v_00_u03c4_1460_, lean_object* v_00_u03b2_1461_, lean_object* v_m_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(v_00_u03c4_1460_, v_00_u03b2_1461_, v_m_1462_, v_a_1463_);
lean_dec_ref(v_a_1463_);
lean_dec_ref(v_m_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1(lean_object* v_00_u03c4_1465_, lean_object* v_00_u03b2_1466_, lean_object* v_m_1467_, lean_object* v_a_1468_, lean_object* v_b_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_m_1467_, v_a_1468_, v_b_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(lean_object* v_00_u03c4_1471_, lean_object* v_00_u03b2_1472_, lean_object* v_a_1473_, lean_object* v_x_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1473_, v_x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___boxed(lean_object* v_00_u03c4_1476_, lean_object* v_00_u03b2_1477_, lean_object* v_a_1478_, lean_object* v_x_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(v_00_u03c4_1476_, v_00_u03b2_1477_, v_a_1478_, v_x_1479_);
lean_dec(v_x_1479_);
lean_dec_ref(v_a_1478_);
return v_res_1480_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(lean_object* v_00_u03c4_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_a_1483_, lean_object* v_x_1484_){
_start:
{
uint8_t v___x_1485_; 
v___x_1485_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1483_, v_x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___boxed(lean_object* v_00_u03c4_1486_, lean_object* v_00_u03b2_1487_, lean_object* v_a_1488_, lean_object* v_x_1489_){
_start:
{
uint8_t v_res_1490_; lean_object* v_r_1491_; 
v_res_1490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(v_00_u03c4_1486_, v_00_u03b2_1487_, v_a_1488_, v_x_1489_);
lean_dec(v_x_1489_);
lean_dec_ref(v_a_1488_);
v_r_1491_ = lean_box(v_res_1490_);
return v_r_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4(lean_object* v_00_u03c4_1492_, lean_object* v_00_u03b2_1493_, lean_object* v_data_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_data_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5(lean_object* v_00_u03c4_1496_, lean_object* v_00_u03b2_1497_, lean_object* v_a_1498_, lean_object* v_b_1499_, lean_object* v_x_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1498_, v_b_1499_, v_x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5(lean_object* v_00_u03c4_1502_, lean_object* v_00_u03b2_1503_, lean_object* v_i_1504_, lean_object* v_source_1505_, lean_object* v_target_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v_i_1504_, v_source_1505_, v_target_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03c4_1508_, lean_object* v_00_u03b2_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_x_1510_, v_x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_unsigned_to_nat(16u);
v___x_1515_ = lean_mk_array(v___x_1514_, v___x_1513_);
return v___x_1515_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0);
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___x_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(lean_object* v_v_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_fst_1522_; 
v___x_1520_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1);
v___x_1521_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1519_, v___x_1520_);
v_fst_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_fst_1522_);
lean_dec_ref(v___x_1521_);
return v_fst_1522_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(lean_object* v_00_u03c4_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_v_1526_){
_start:
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(v_v_1526_);
v___x_1528_ = lean_unbox(v___x_1527_);
lean_dec(v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___boxed(lean_object* v_00_u03c4_1529_, lean_object* v_inst_1530_, lean_object* v_inst_1531_, lean_object* v_v_1532_){
_start:
{
uint8_t v_res_1533_; lean_object* v_r_1534_; 
v_res_1533_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(v_00_u03c4_1529_, v_inst_1530_, v_inst_1531_, v_v_1532_);
lean_dec_ref(v_inst_1531_);
lean_dec_ref(v_inst_1530_);
v_r_1534_ = lean_box(v_res_1533_);
return v_r_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(uint8_t v_x_1535_){
_start:
{
switch(v_x_1535_)
{
case 0:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
return v___x_1536_;
}
case 1:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_unsigned_to_nat(1u);
return v___x_1537_;
}
default: 
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_unsigned_to_nat(2u);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1539_){
_start:
{
uint8_t v_x_boxed_1540_; lean_object* v_res_1541_; 
v_x_boxed_1540_ = lean_unbox(v_x_1539_);
v_res_1541_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(v_x_boxed_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(lean_object* v_k_1542_){
_start:
{
lean_inc(v_k_1542_);
return v_k_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(v_k_1543_);
lean_dec(v_k_1543_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(lean_object* v_motive_1545_, lean_object* v_ctorIdx_1546_, uint8_t v_t_1547_, lean_object* v_h_1548_, lean_object* v_k_1549_){
_start:
{
lean_inc(v_k_1549_);
return v_k_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1550_, lean_object* v_ctorIdx_1551_, lean_object* v_t_1552_, lean_object* v_h_1553_, lean_object* v_k_1554_){
_start:
{
uint8_t v_t_boxed_1555_; lean_object* v_res_1556_; 
v_t_boxed_1555_ = lean_unbox(v_t_1552_);
v_res_1556_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(v_motive_1550_, v_ctorIdx_1551_, v_t_boxed_1555_, v_h_1553_, v_k_1554_);
lean_dec(v_k_1554_);
lean_dec(v_ctorIdx_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1557_){
_start:
{
lean_inc(v_withoutSpacing_1557_);
return v_withoutSpacing_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1558_);
lean_dec(v_withoutSpacing_1558_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1560_, uint8_t v_t_1561_, lean_object* v_h_1562_, lean_object* v_withoutSpacing_1563_){
_start:
{
lean_inc(v_withoutSpacing_1563_);
return v_withoutSpacing_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1564_, lean_object* v_t_1565_, lean_object* v_h_1566_, lean_object* v_withoutSpacing_1567_){
_start:
{
uint8_t v_t_boxed_1568_; lean_object* v_res_1569_; 
v_t_boxed_1568_ = lean_unbox(v_t_1565_);
v_res_1569_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(v_motive_1564_, v_t_boxed_1568_, v_h_1566_, v_withoutSpacing_1567_);
lean_dec(v_withoutSpacing_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(lean_object* v_withoutSpacingIfAtomic_1570_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1570_);
return v_withoutSpacingIfAtomic_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg___boxed(lean_object* v_withoutSpacingIfAtomic_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(v_withoutSpacingIfAtomic_1571_);
lean_dec(v_withoutSpacingIfAtomic_1571_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(lean_object* v_motive_1573_, uint8_t v_t_1574_, lean_object* v_h_1575_, lean_object* v_withoutSpacingIfAtomic_1576_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1576_);
return v_withoutSpacingIfAtomic_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___boxed(lean_object* v_motive_1577_, lean_object* v_t_1578_, lean_object* v_h_1579_, lean_object* v_withoutSpacingIfAtomic_1580_){
_start:
{
uint8_t v_t_boxed_1581_; lean_object* v_res_1582_; 
v_t_boxed_1581_ = lean_unbox(v_t_1578_);
v_res_1582_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(v_motive_1577_, v_t_boxed_1581_, v_h_1579_, v_withoutSpacingIfAtomic_1580_);
lean_dec(v_withoutSpacingIfAtomic_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1583_){
_start:
{
lean_inc(v_withSpacing_1583_);
return v_withSpacing_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1584_);
lean_dec(v_withSpacing_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(lean_object* v_motive_1586_, uint8_t v_t_1587_, lean_object* v_h_1588_, lean_object* v_withSpacing_1589_){
_start:
{
lean_inc(v_withSpacing_1589_);
return v_withSpacing_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1590_, lean_object* v_t_1591_, lean_object* v_h_1592_, lean_object* v_withSpacing_1593_){
_start:
{
uint8_t v_t_boxed_1594_; lean_object* v_res_1595_; 
v_t_boxed_1594_ = lean_unbox(v_t_1591_);
v_res_1595_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(v_motive_1590_, v_t_boxed_1594_, v_h_1592_, v_withSpacing_1593_);
lean_dec(v_withSpacing_1593_);
return v_res_1595_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_unsigned_to_nat(16u);
v___x_1598_ = lean_mk_array(v___x_1597_, v___x_1596_);
return v___x_1598_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0);
v___x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v___x_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object* v_v_1602_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_fst_1605_; uint8_t v___x_1606_; 
v___x_1603_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1);
v___x_1604_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1602_, v___x_1603_);
v_fst_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_fst_1605_);
lean_dec_ref(v___x_1604_);
v___x_1606_ = lean_unbox(v_fst_1605_);
lean_dec(v_fst_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object* v_v_1607_){
_start:
{
uint8_t v_res_1608_; lean_object* v_r_1609_; 
v_res_1608_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_v_1607_);
v_r_1609_ = lean_box(v_res_1608_);
return v_r_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object* v_prefixOperatorTk_1610_, lean_object* v_operand_1611_, uint8_t v_format_1612_){
_start:
{
lean_object* v___y_1614_; uint8_t v___y_1626_; uint8_t v___x_1633_; uint8_t v___y_1635_; uint8_t v___y_1638_; 
v___x_1633_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_prefixOperatorTk_1610_);
if (v___x_1633_ == 0)
{
if (v_format_1612_ == 0)
{
goto v___jp_1618_;
}
else
{
if (v___x_1633_ == 0)
{
uint8_t v___x_1639_; 
v___x_1639_ = 1;
if (v_format_1612_ == 1)
{
goto v___jp_1640_;
}
else
{
if (v___x_1633_ == 0)
{
v___y_1638_ = v___x_1633_;
goto v___jp_1637_;
}
else
{
goto v___jp_1640_;
}
}
v___jp_1640_:
{
uint8_t v___x_1641_; 
v___x_1641_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_operand_1611_);
if (v___x_1641_ == 0)
{
uint8_t v___x_1642_; 
lean_inc_ref(v_operand_1611_);
v___x_1642_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_operand_1611_);
v___y_1638_ = v___x_1642_;
goto v___jp_1637_;
}
else
{
v___y_1635_ = v___x_1639_;
goto v___jp_1634_;
}
}
}
else
{
goto v___jp_1618_;
}
}
}
else
{
lean_dec_ref(v_prefixOperatorTk_1610_);
return v_operand_1611_;
}
v___jp_1613_:
{
lean_object* v_doc_1615_; uint8_t v___x_1616_; 
v_doc_1615_ = lean_ctor_get(v_operand_1611_, 0);
lean_inc(v_doc_1615_);
lean_dec_ref(v_operand_1611_);
v___x_1616_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1615_);
if (v___x_1616_ == 0)
{
return v___y_1614_;
}
else
{
lean_object* v_doc_1617_; 
v_doc_1617_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___y_1614_);
return v_doc_1617_;
}
}
v___jp_1618_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1619_ = lean_unsigned_to_nat(2u);
v___x_1620_ = lean_mk_empty_array_with_capacity(v___x_1619_);
v___x_1621_ = lean_array_push(v___x_1620_, v_prefixOperatorTk_1610_);
lean_inc_ref(v_operand_1611_);
v___x_1622_ = lean_array_push(v___x_1621_, v_operand_1611_);
v___x_1623_ = l_Lean_Fmt_Layouts_atomic(v___x_1622_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1623_);
v___y_1614_ = v___x_1624_;
goto v___jp_1613_;
}
v___jp_1625_:
{
if (v___y_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1627_ = lean_unsigned_to_nat(2u);
v___x_1628_ = lean_mk_empty_array_with_capacity(v___x_1627_);
v___x_1629_ = lean_array_push(v___x_1628_, v_prefixOperatorTk_1610_);
lean_inc_ref(v_operand_1611_);
v___x_1630_ = lean_array_push(v___x_1629_, v_operand_1611_);
v___x_1631_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1630_);
lean_dec_ref(v___x_1630_);
v___x_1632_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1631_);
v___y_1614_ = v___x_1632_;
goto v___jp_1613_;
}
else
{
goto v___jp_1618_;
}
}
v___jp_1634_:
{
uint8_t v___x_1636_; 
lean_inc_ref(v_operand_1611_);
v___x_1636_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_operand_1611_);
if (v___x_1636_ == 0)
{
v___y_1626_ = v___y_1635_;
goto v___jp_1625_;
}
else
{
v___y_1626_ = v___x_1633_;
goto v___jp_1625_;
}
}
v___jp_1637_:
{
if (v___y_1638_ == 0)
{
v___y_1626_ = v___x_1633_;
goto v___jp_1625_;
}
else
{
v___y_1635_ = v___y_1638_;
goto v___jp_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator___boxed(lean_object* v_prefixOperatorTk_1643_, lean_object* v_operand_1644_, lean_object* v_format_1645_){
_start:
{
uint8_t v_format_boxed_1646_; lean_object* v_res_1647_; 
v_format_boxed_1646_ = lean_unbox(v_format_1645_);
v_res_1647_ = l_Lean_Fmt_Layouts_prefixOperator(v_prefixOperatorTk_1643_, v_operand_1644_, v_format_boxed_1646_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(uint8_t v_x_1648_){
_start:
{
if (v_x_1648_ == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_unsigned_to_nat(0u);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_unsigned_to_nat(1u);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1651_){
_start:
{
uint8_t v_x_boxed_1652_; lean_object* v_res_1653_; 
v_x_boxed_1652_ = lean_unbox(v_x_1651_);
v_res_1653_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(v_x_boxed_1652_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(lean_object* v_k_1654_){
_start:
{
lean_inc(v_k_1654_);
return v_k_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(v_k_1655_);
lean_dec(v_k_1655_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(lean_object* v_motive_1657_, lean_object* v_ctorIdx_1658_, uint8_t v_t_1659_, lean_object* v_h_1660_, lean_object* v_k_1661_){
_start:
{
lean_inc(v_k_1661_);
return v_k_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1662_, lean_object* v_ctorIdx_1663_, lean_object* v_t_1664_, lean_object* v_h_1665_, lean_object* v_k_1666_){
_start:
{
uint8_t v_t_boxed_1667_; lean_object* v_res_1668_; 
v_t_boxed_1667_ = lean_unbox(v_t_1664_);
v_res_1668_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(v_motive_1662_, v_ctorIdx_1663_, v_t_boxed_1667_, v_h_1665_, v_k_1666_);
lean_dec(v_k_1666_);
lean_dec(v_ctorIdx_1663_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1669_){
_start:
{
lean_inc(v_withoutSpacing_1669_);
return v_withoutSpacing_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1670_);
lean_dec(v_withoutSpacing_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1672_, uint8_t v_t_1673_, lean_object* v_h_1674_, lean_object* v_withoutSpacing_1675_){
_start:
{
lean_inc(v_withoutSpacing_1675_);
return v_withoutSpacing_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1676_, lean_object* v_t_1677_, lean_object* v_h_1678_, lean_object* v_withoutSpacing_1679_){
_start:
{
uint8_t v_t_boxed_1680_; lean_object* v_res_1681_; 
v_t_boxed_1680_ = lean_unbox(v_t_1677_);
v_res_1681_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(v_motive_1676_, v_t_boxed_1680_, v_h_1678_, v_withoutSpacing_1679_);
lean_dec(v_withoutSpacing_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1682_){
_start:
{
lean_inc(v_withSpacing_1682_);
return v_withSpacing_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1683_);
lean_dec(v_withSpacing_1683_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(lean_object* v_motive_1685_, uint8_t v_t_1686_, lean_object* v_h_1687_, lean_object* v_withSpacing_1688_){
_start:
{
lean_inc(v_withSpacing_1688_);
return v_withSpacing_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1689_, lean_object* v_t_1690_, lean_object* v_h_1691_, lean_object* v_withSpacing_1692_){
_start:
{
uint8_t v_t_boxed_1693_; lean_object* v_res_1694_; 
v_t_boxed_1693_ = lean_unbox(v_t_1690_);
v_res_1694_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(v_motive_1689_, v_t_boxed_1693_, v_h_1691_, v_withSpacing_1692_);
lean_dec(v_withSpacing_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object* v_operand_1695_, lean_object* v_postfixOperatorTk_1696_, uint8_t v_format_1697_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_postfixOperatorTk_1696_);
if (v___x_1705_ == 0)
{
if (v_format_1697_ == 1)
{
goto v___jp_1698_;
}
else
{
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1706_ = lean_unsigned_to_nat(2u);
v___x_1707_ = lean_mk_empty_array_with_capacity(v___x_1706_);
v___x_1708_ = lean_array_push(v___x_1707_, v_operand_1695_);
v___x_1709_ = lean_array_push(v___x_1708_, v_postfixOperatorTk_1696_);
v___x_1710_ = l_Lean_Fmt_Layouts_atomic(v___x_1709_);
lean_dec_ref(v___x_1709_);
v___x_1711_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1710_);
return v___x_1711_;
}
else
{
goto v___jp_1698_;
}
}
}
else
{
lean_dec_ref(v_postfixOperatorTk_1696_);
return v_operand_1695_;
}
v___jp_1698_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1699_ = lean_unsigned_to_nat(2u);
v___x_1700_ = lean_mk_empty_array_with_capacity(v___x_1699_);
v___x_1701_ = lean_array_push(v___x_1700_, v_operand_1695_);
v___x_1702_ = lean_array_push(v___x_1701_, v_postfixOperatorTk_1696_);
v___x_1703_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1702_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1703_);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator___boxed(lean_object* v_operand_1712_, lean_object* v_postfixOperatorTk_1713_, lean_object* v_format_1714_){
_start:
{
uint8_t v_format_boxed_1715_; lean_object* v_res_1716_; 
v_format_boxed_1715_ = lean_unbox(v_format_1714_);
v_res_1716_ = l_Lean_Fmt_Layouts_postfixOperator(v_operand_1712_, v_postfixOperatorTk_1713_, v_format_boxed_1715_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1717_) == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_unsigned_to_nat(0u);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_unsigned_to_nat(1u);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(v_x_1720_);
lean_dec_ref(v_x_1720_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(lean_object* v_t_1722_, lean_object* v_k_1723_){
_start:
{
if (lean_obj_tag(v_t_1722_) == 0)
{
uint8_t v_hardNestedFirstOperand_1724_; uint8_t v_trailingOperator_1725_; uint8_t v_spacing_1726_; uint8_t v_respectPseudoAlignment_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_hardNestedFirstOperand_1724_ = lean_ctor_get_uint8(v_t_1722_, 0);
v_trailingOperator_1725_ = lean_ctor_get_uint8(v_t_1722_, 1);
v_spacing_1726_ = lean_ctor_get_uint8(v_t_1722_, 2);
v_respectPseudoAlignment_1727_ = lean_ctor_get_uint8(v_t_1722_, 3);
v___x_1728_ = lean_box(v_hardNestedFirstOperand_1724_);
v___x_1729_ = lean_box(v_trailingOperator_1725_);
v___x_1730_ = lean_box(v_spacing_1726_);
v___x_1731_ = lean_box(v_respectPseudoAlignment_1727_);
v___x_1732_ = lean_apply_4(v_k_1723_, v___x_1728_, v___x_1729_, v___x_1730_, v___x_1731_);
return v___x_1732_;
}
else
{
uint8_t v_hardNestedFirstOperand_1733_; uint8_t v_trailingOperator_1734_; uint8_t v_spacing_1735_; uint8_t v_alignedOperators_1736_; uint8_t v_separateFinalOperand_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_hardNestedFirstOperand_1733_ = lean_ctor_get_uint8(v_t_1722_, 0);
v_trailingOperator_1734_ = lean_ctor_get_uint8(v_t_1722_, 1);
v_spacing_1735_ = lean_ctor_get_uint8(v_t_1722_, 2);
v_alignedOperators_1736_ = lean_ctor_get_uint8(v_t_1722_, 3);
v_separateFinalOperand_1737_ = lean_ctor_get_uint8(v_t_1722_, 4);
v___x_1738_ = lean_box(v_hardNestedFirstOperand_1733_);
v___x_1739_ = lean_box(v_trailingOperator_1734_);
v___x_1740_ = lean_box(v_spacing_1735_);
v___x_1741_ = lean_box(v_alignedOperators_1736_);
v___x_1742_ = lean_box(v_separateFinalOperand_1737_);
v___x_1743_ = lean_apply_5(v_k_1723_, v___x_1738_, v___x_1739_, v___x_1740_, v___x_1741_, v___x_1742_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_t_1744_, lean_object* v_k_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1744_, v_k_1745_);
lean_dec_ref(v_t_1744_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(lean_object* v_motive_1747_, lean_object* v_ctorIdx_1748_, lean_object* v_t_1749_, lean_object* v_h_1750_, lean_object* v_k_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1749_, v_k_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1753_, lean_object* v_ctorIdx_1754_, lean_object* v_t_1755_, lean_object* v_h_1756_, lean_object* v_k_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(v_motive_1753_, v_ctorIdx_1754_, v_t_1755_, v_h_1756_, v_k_1757_);
lean_dec_ref(v_t_1755_);
lean_dec(v_ctorIdx_1754_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(lean_object* v_t_1759_, lean_object* v_dense_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1759_, v_dense_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg___boxed(lean_object* v_t_1762_, lean_object* v_dense_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(v_t_1762_, v_dense_1763_);
lean_dec_ref(v_t_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(lean_object* v_motive_1765_, lean_object* v_t_1766_, lean_object* v_h_1767_, lean_object* v_dense_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1766_, v_dense_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___boxed(lean_object* v_motive_1770_, lean_object* v_t_1771_, lean_object* v_h_1772_, lean_object* v_dense_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(v_motive_1770_, v_t_1771_, v_h_1772_, v_dense_1773_);
lean_dec_ref(v_t_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(lean_object* v_t_1775_, lean_object* v_sparse_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1775_, v_sparse_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg___boxed(lean_object* v_t_1778_, lean_object* v_sparse_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(v_t_1778_, v_sparse_1779_);
lean_dec_ref(v_t_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(lean_object* v_motive_1781_, lean_object* v_t_1782_, lean_object* v_h_1783_, lean_object* v_sparse_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1782_, v_sparse_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___boxed(lean_object* v_motive_1786_, lean_object* v_t_1787_, lean_object* v_h_1788_, lean_object* v_sparse_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(v_motive_1786_, v_t_1787_, v_h_1788_, v_sparse_1789_);
lean_dec_ref(v_t_1787_);
return v_res_1790_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(lean_object* v_x_1791_){
_start:
{
uint8_t v_hardNestedFirstOperand_1792_; 
v_hardNestedFirstOperand_1792_ = lean_ctor_get_uint8(v_x_1791_, 0);
return v_hardNestedFirstOperand_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand___boxed(lean_object* v_x_1793_){
_start:
{
uint8_t v_res_1794_; lean_object* v_r_1795_; 
v_res_1794_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(v_x_1793_);
lean_dec_ref(v_x_1793_);
v_r_1795_ = lean_box(v_res_1794_);
return v_r_1795_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(lean_object* v_x_1796_){
_start:
{
uint8_t v_trailingOperator_1797_; 
v_trailingOperator_1797_ = lean_ctor_get_uint8(v_x_1796_, 1);
return v_trailingOperator_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator___boxed(lean_object* v_x_1798_){
_start:
{
uint8_t v_res_1799_; lean_object* v_r_1800_; 
v_res_1799_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(v_x_1798_);
lean_dec_ref(v_x_1798_);
v_r_1800_ = lean_box(v_res_1799_);
return v_r_1800_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(lean_object* v_x_1801_){
_start:
{
uint8_t v_spacing_1802_; 
v_spacing_1802_ = lean_ctor_get_uint8(v_x_1801_, 2);
return v_spacing_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing___boxed(lean_object* v_x_1803_){
_start:
{
uint8_t v_res_1804_; lean_object* v_r_1805_; 
v_res_1804_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(v_x_1803_);
lean_dec_ref(v_x_1803_);
v_r_1805_ = lean_box(v_res_1804_);
return v_r_1805_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(lean_object* v_x_1806_){
_start:
{
if (lean_obj_tag(v_x_1806_) == 0)
{
uint8_t v___x_1807_; 
v___x_1807_ = 0;
return v___x_1807_;
}
else
{
uint8_t v_trailingOperator_1808_; 
v_trailingOperator_1808_ = lean_ctor_get_uint8(v_x_1806_, 1);
if (v_trailingOperator_1808_ == 0)
{
uint8_t v_alignedOperators_1809_; 
v_alignedOperators_1809_ = lean_ctor_get_uint8(v_x_1806_, 3);
return v_alignedOperators_1809_;
}
else
{
uint8_t v___x_1810_; 
v___x_1810_ = 0;
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators___boxed(lean_object* v_x_1811_){
_start:
{
uint8_t v_res_1812_; lean_object* v_r_1813_; 
v_res_1812_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_x_1811_);
lean_dec_ref(v_x_1811_);
v_r_1813_ = lean_box(v_res_1812_);
return v_r_1813_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(lean_object* v_x_1814_){
_start:
{
if (lean_obj_tag(v_x_1814_) == 0)
{
uint8_t v___x_1815_; 
v___x_1815_ = 0;
return v___x_1815_;
}
else
{
uint8_t v_trailingOperator_1816_; 
v_trailingOperator_1816_ = lean_ctor_get_uint8(v_x_1814_, 1);
if (v_trailingOperator_1816_ == 0)
{
uint8_t v_separateFinalOperand_1817_; 
v_separateFinalOperand_1817_ = lean_ctor_get_uint8(v_x_1814_, 4);
return v_separateFinalOperand_1817_;
}
else
{
uint8_t v___x_1818_; 
v___x_1818_ = 0;
return v___x_1818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand___boxed(lean_object* v_x_1819_){
_start:
{
uint8_t v_res_1820_; lean_object* v_r_1821_; 
v_res_1820_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_x_1819_);
lean_dec_ref(v_x_1819_);
v_r_1821_ = lean_box(v_res_1820_);
return v_r_1821_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(lean_object* v_x_1822_){
_start:
{
if (lean_obj_tag(v_x_1822_) == 0)
{
uint8_t v_respectPseudoAlignment_1823_; 
v_respectPseudoAlignment_1823_ = lean_ctor_get_uint8(v_x_1822_, 3);
return v_respectPseudoAlignment_1823_;
}
else
{
uint8_t v___x_1824_; 
v___x_1824_ = 1;
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment___boxed(lean_object* v_x_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(v_x_1825_);
lean_dec_ref(v_x_1825_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_permitDenseLayout(lean_object* v_doc_1828_, uint8_t v_respectPseudoAlignment_1829_){
_start:
{
if (v_respectPseudoAlignment_1829_ == 0)
{
lean_object* v_doc_1830_; uint8_t v___x_1831_; 
v_doc_1830_ = lean_ctor_get(v_doc_1828_, 0);
lean_inc(v_doc_1830_);
lean_dec_ref(v_doc_1828_);
v___x_1831_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1830_);
if (v___x_1831_ == 0)
{
uint8_t v___x_1832_; 
v___x_1832_ = 1;
return v___x_1832_;
}
else
{
return v_respectPseudoAlignment_1829_;
}
}
else
{
uint8_t v___x_1833_; 
lean_inc_ref(v_doc_1828_);
v___x_1833_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_doc_1828_);
if (v___x_1833_ == 0)
{
lean_object* v_doc_1834_; uint8_t v___x_1835_; 
v_doc_1834_ = lean_ctor_get(v_doc_1828_, 0);
lean_inc(v_doc_1834_);
lean_dec_ref(v_doc_1828_);
v___x_1835_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1834_);
if (v___x_1835_ == 0)
{
return v_respectPseudoAlignment_1829_;
}
else
{
return v___x_1833_;
}
}
else
{
uint8_t v___x_1836_; 
lean_dec_ref(v_doc_1828_);
v___x_1836_ = 0;
return v___x_1836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_permitDenseLayout___boxed(lean_object* v_doc_1837_, lean_object* v_respectPseudoAlignment_1838_){
_start:
{
uint8_t v_respectPseudoAlignment_boxed_1839_; uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_respectPseudoAlignment_boxed_1839_ = lean_unbox(v_respectPseudoAlignment_1838_);
v_res_1840_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_doc_1837_, v_respectPseudoAlignment_boxed_1839_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object* v_format_1842_, lean_object* v_docs_1843_){
_start:
{
uint8_t v___y_1845_; uint8_t v_spacing_1848_; 
v_spacing_1848_ = lean_ctor_get_uint8(v_format_1842_, 2);
v___y_1845_ = v_spacing_1848_;
goto v___jp_1844_;
v___jp_1844_:
{
if (v___y_1845_ == 0)
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Fmt_Layouts_atomic(v_docs_1843_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_Fmt_Layouts_spacedAtomic(v_docs_1843_);
return v___x_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object* v_format_1849_, lean_object* v_docs_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1849_, v_docs_1850_);
lean_dec_ref(v_docs_1850_);
lean_dec_ref(v_format_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object* v_msg_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_1854_ = lean_panic_fn_borrowed(v___x_1853_, v_msg_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t v_a_1855_, lean_object* v_as_1856_, size_t v_i_1857_, size_t v_stop_1858_){
_start:
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_usize_dec_eq(v_i_1857_, v_stop_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; uint8_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = lean_array_uget_borrowed(v_as_1856_, v_i_1857_);
v___x_1861_ = lean_unbox(v___x_1860_);
v___x_1862_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_a_1855_, v___x_1861_);
if (v___x_1862_ == 0)
{
size_t v___x_1863_; size_t v___x_1864_; 
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = lean_usize_add(v_i_1857_, v___x_1863_);
v_i_1857_ = v___x_1864_;
goto _start;
}
else
{
return v___x_1862_;
}
}
else
{
uint8_t v___x_1866_; 
v___x_1866_ = 0;
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object* v_a_1867_, lean_object* v_as_1868_, lean_object* v_i_1869_, lean_object* v_stop_1870_){
_start:
{
uint8_t v_a_boxed_1871_; size_t v_i_boxed_1872_; size_t v_stop_boxed_1873_; uint8_t v_res_1874_; lean_object* v_r_1875_; 
v_a_boxed_1871_ = lean_unbox(v_a_1867_);
v_i_boxed_1872_ = lean_unbox_usize(v_i_1869_);
lean_dec(v_i_1869_);
v_stop_boxed_1873_ = lean_unbox_usize(v_stop_1870_);
lean_dec(v_stop_1870_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_boxed_1871_, v_as_1868_, v_i_boxed_1872_, v_stop_boxed_1873_);
lean_dec_ref(v_as_1868_);
v_r_1875_ = lean_box(v_res_1874_);
return v_r_1875_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object* v_as_1876_, uint8_t v_a_1877_){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = lean_array_get_size(v_as_1876_);
v___x_1880_ = lean_nat_dec_lt(v___x_1878_, v___x_1879_);
if (v___x_1880_ == 0)
{
return v___x_1880_;
}
else
{
if (v___x_1880_ == 0)
{
return v___x_1880_;
}
else
{
size_t v___x_1881_; size_t v___x_1882_; uint8_t v___x_1883_; 
v___x_1881_ = ((size_t)0ULL);
v___x_1882_ = lean_usize_of_nat(v___x_1879_);
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_1877_, v_as_1876_, v___x_1881_, v___x_1882_);
return v___x_1883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object* v_as_1884_, lean_object* v_a_1885_){
_start:
{
uint8_t v_a_boxed_1886_; uint8_t v_res_1887_; lean_object* v_r_1888_; 
v_a_boxed_1886_ = lean_unbox(v_a_1885_);
v_res_1887_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_as_1884_, v_a_boxed_1886_);
lean_dec_ref(v_as_1884_);
v_r_1888_ = lean_box(v_res_1887_);
return v_r_1888_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1892_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2));
v___x_1893_ = lean_unsigned_to_nat(14u);
v___x_1894_ = lean_unsigned_to_nat(22u);
v___x_1895_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1));
v___x_1896_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_1897_ = l_mkPanicMessageWithDecl(v___x_1896_, v___x_1895_, v___x_1894_, v___x_1893_, v___x_1892_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(lean_object* v_format_1898_, lean_object* v_doc_1899_, lean_object* v_lastOperand_1900_, uint8_t v_isTailless_1901_, lean_object* v_combinedChain_1902_, lean_object* v_eligibleKinds_1903_){
_start:
{
lean_object* v___x_1904_; uint8_t v___y_1906_; lean_object* v___y_1907_; uint8_t v___y_1928_; uint8_t v_trailingOperator_1941_; 
v___x_1904_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_1941_ = lean_ctor_get_uint8(v_format_1898_, 1);
v___y_1928_ = v_trailingOperator_1941_;
goto v___jp_1927_;
v___jp_1905_:
{
lean_object* v_stickyVariant_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_stickyVariant_1908_ = lean_ctor_get(v___y_1907_, 0);
v___x_1909_ = lean_array_get_size(v_combinedChain_1902_);
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = lean_nat_sub(v___x_1909_, v___x_1910_);
lean_inc_ref(v_stickyVariant_1908_);
v___x_1912_ = lean_array_set(v_combinedChain_1902_, v___x_1911_, v_stickyVariant_1908_);
lean_dec(v___x_1911_);
lean_inc_ref(v___x_1912_);
v___x_1913_ = lean_array_pop(v___x_1912_);
v___x_1914_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1898_, v___x_1913_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1914_);
v___x_1916_ = lean_array_get_size(v___x_1912_);
v___x_1917_ = lean_nat_sub(v___x_1916_, v___x_1910_);
v___x_1918_ = lean_array_get(v___x_1904_, v___x_1912_, v___x_1917_);
lean_dec(v___x_1917_);
lean_dec_ref(v___x_1912_);
v___x_1919_ = lean_unsigned_to_nat(2u);
v___x_1920_ = lean_mk_empty_array_with_capacity(v___x_1919_);
v___x_1921_ = lean_array_push(v___x_1920_, v___x_1915_);
v___x_1922_ = lean_array_push(v___x_1921_, v___x_1918_);
v___x_1923_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1898_, v___x_1922_);
lean_dec_ref(v___x_1922_);
v___x_1924_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_1907_, v___y_1906_);
lean_dec_ref(v___y_1907_);
v___x_1925_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1899_, v___x_1923_, v___x_1924_);
lean_dec(v___x_1924_);
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
v___jp_1927_:
{
if (v___y_1928_ == 0)
{
lean_object* v___x_1929_; 
lean_dec_ref(v_combinedChain_1902_);
lean_dec_ref(v_lastOperand_1900_);
lean_dec_ref(v_doc_1899_);
v___x_1929_ = lean_box(0);
return v___x_1929_;
}
else
{
if (v_isTailless_1901_ == 0)
{
lean_object* v___x_1930_; 
lean_inc_ref(v_lastOperand_1900_);
v___x_1930_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v_lastOperand_1900_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref(v_combinedChain_1902_);
lean_dec_ref(v_lastOperand_1900_);
lean_dec_ref(v_doc_1899_);
v___x_1931_ = lean_box(0);
return v___x_1931_;
}
else
{
lean_object* v_val_1932_; uint8_t v___x_1933_; uint8_t v___x_1934_; 
v_val_1932_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_val_1932_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1933_ = lean_unbox(v_val_1932_);
lean_dec(v_val_1932_);
v___x_1934_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_1903_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec_ref(v_combinedChain_1902_);
lean_dec_ref(v_lastOperand_1900_);
lean_dec_ref(v_doc_1899_);
v___x_1935_ = lean_box(0);
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_lastOperand_1900_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_1938_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_1937_);
v___y_1906_ = v___x_1934_;
v___y_1907_ = v___x_1938_;
goto v___jp_1905_;
}
else
{
lean_object* v_val_1939_; 
v_val_1939_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_val_1939_);
lean_dec_ref_known(v___x_1936_, 1);
v___y_1906_ = v___x_1934_;
v___y_1907_ = v_val_1939_;
goto v___jp_1905_;
}
}
}
}
else
{
lean_object* v___x_1940_; 
lean_dec_ref(v_combinedChain_1902_);
lean_dec_ref(v_lastOperand_1900_);
lean_dec_ref(v_doc_1899_);
v___x_1940_ = lean_box(0);
return v___x_1940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___boxed(lean_object* v_format_1942_, lean_object* v_doc_1943_, lean_object* v_lastOperand_1944_, lean_object* v_isTailless_1945_, lean_object* v_combinedChain_1946_, lean_object* v_eligibleKinds_1947_){
_start:
{
uint8_t v_isTailless_boxed_1948_; lean_object* v_res_1949_; 
v_isTailless_boxed_1948_ = lean_unbox(v_isTailless_1945_);
v_res_1949_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_1942_, v_doc_1943_, v_lastOperand_1944_, v_isTailless_boxed_1948_, v_combinedChain_1946_, v_eligibleKinds_1947_);
lean_dec_ref(v_eligibleKinds_1947_);
lean_dec_ref(v_format_1942_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(lean_object* v_format_1950_, lean_object* v_doc_1951_, lean_object* v_lastOperand_1952_, uint8_t v_isTailless_1953_, lean_object* v_combinedChain_1954_){
_start:
{
if (lean_obj_tag(v_format_1950_) == 0)
{
if (v_isTailless_1953_ == 0)
{
uint8_t v_trailingOperator_1955_; lean_object* v___x_1956_; 
v_trailingOperator_1955_ = lean_ctor_get_uint8(v_format_1950_, 1);
v___x_1956_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (v_trailingOperator_1955_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1975_ = lean_array_get_size(v_combinedChain_1954_);
v___x_1976_ = lean_unsigned_to_nat(2u);
v___x_1977_ = lean_nat_dec_eq(v___x_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref(v_combinedChain_1954_);
lean_dec_ref(v_lastOperand_1952_);
lean_dec_ref(v_doc_1951_);
v___x_1978_ = lean_box(0);
return v___x_1978_;
}
else
{
goto v___jp_1957_;
}
}
else
{
goto v___jp_1957_;
}
v___jp_1957_:
{
uint8_t v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(v_format_1950_);
v___x_1959_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_lastOperand_1952_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v_combinedChain_1954_);
lean_dec_ref(v_doc_1951_);
v___x_1960_ = lean_box(0);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_inc_ref(v_combinedChain_1954_);
v___x_1961_ = lean_array_pop(v_combinedChain_1954_);
v___x_1962_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1950_, v___x_1961_);
lean_dec_ref(v___x_1961_);
v___x_1963_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1962_);
v___x_1964_ = lean_array_get_size(v_combinedChain_1954_);
v___x_1965_ = lean_unsigned_to_nat(1u);
v___x_1966_ = lean_nat_sub(v___x_1964_, v___x_1965_);
v___x_1967_ = lean_array_get(v___x_1956_, v_combinedChain_1954_, v___x_1966_);
lean_dec(v___x_1966_);
lean_dec_ref(v_combinedChain_1954_);
v___x_1968_ = lean_unsigned_to_nat(2u);
v___x_1969_ = lean_mk_empty_array_with_capacity(v___x_1968_);
v___x_1970_ = lean_array_push(v___x_1969_, v___x_1963_);
v___x_1971_ = lean_array_push(v___x_1970_, v___x_1967_);
v___x_1972_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1950_, v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = l_Lean_Fmt_TaggedDoc_fallbackOnHeight(v_doc_1951_, v___x_1972_);
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
}
}
else
{
lean_object* v___x_1979_; 
lean_dec_ref(v_combinedChain_1954_);
lean_dec_ref(v_lastOperand_1952_);
lean_dec_ref(v_doc_1951_);
v___x_1979_ = lean_box(0);
return v___x_1979_;
}
}
else
{
lean_object* v___x_1980_; 
lean_dec_ref(v_combinedChain_1954_);
lean_dec_ref(v_lastOperand_1952_);
lean_dec_ref(v_doc_1951_);
v___x_1980_ = lean_box(0);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f___boxed(lean_object* v_format_1981_, lean_object* v_doc_1982_, lean_object* v_lastOperand_1983_, lean_object* v_isTailless_1984_, lean_object* v_combinedChain_1985_){
_start:
{
uint8_t v_isTailless_boxed_1986_; lean_object* v_res_1987_; 
v_isTailless_boxed_1986_ = lean_unbox(v_isTailless_1984_);
v_res_1987_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_1981_, v_doc_1982_, v_lastOperand_1983_, v_isTailless_boxed_1986_, v_combinedChain_1985_);
lean_dec_ref(v_format_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(lean_object* v_snd_1988_, lean_object* v___x_1989_, lean_object* v_____r_1990_, lean_object* v_normalized_1991_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_nat_add(v_snd_1988_, v___x_1989_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v_normalized_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0___boxed(lean_object* v_snd_1995_, lean_object* v___x_1996_, lean_object* v_____r_1997_, lean_object* v_normalized_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1995_, v___x_1996_, v_____r_1997_, v_normalized_1998_);
lean_dec(v___x_1996_);
lean_dec(v_snd_1995_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object* v___x_2000_, lean_object* v_chain_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___y_2004_; lean_object* v_fst_2008_; lean_object* v_snd_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2036_; 
v_fst_2008_ = lean_ctor_get(v_a_2002_, 0);
v_snd_2009_ = lean_ctor_get(v_a_2002_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_2002_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2011_ = v_a_2002_;
v_isShared_2012_ = v_isSharedCheck_2036_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snd_2009_);
lean_inc(v_fst_2008_);
lean_dec(v_a_2002_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2036_;
goto v_resetjp_2010_;
}
v___jp_2003_:
{
if (lean_obj_tag(v___y_2004_) == 0)
{
lean_object* v_a_2005_; 
v_a_2005_ = lean_ctor_get(v___y_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___y_2004_, 1);
return v_a_2005_;
}
else
{
lean_object* v_a_2006_; 
v_a_2006_ = lean_ctor_get(v___y_2004_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___y_2004_, 1);
v_a_2002_ = v_a_2006_;
goto _start;
}
}
v_resetjp_2010_:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_nat_dec_lt(v_snd_2009_, v___x_2000_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2015_; 
if (v_isShared_2012_ == 0)
{
v___x_2015_ = v___x_2011_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_fst_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_snd_2009_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2017_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2018_ = lean_array_get_borrowed(v___x_2017_, v_chain_2001_, v_snd_2009_);
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_nat_add(v_snd_2009_, v___x_2019_);
v___x_2021_ = lean_array_get_size(v_chain_2001_);
v___x_2022_ = lean_nat_dec_lt(v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
lean_dec(v___x_2020_);
lean_inc(v___x_2018_);
v___x_2023_ = lean_array_push(v_fst_2008_, v___x_2018_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2023_);
v___x_2025_ = v___x_2011_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_snd_2009_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
lean_del_object(v___x_2011_);
v___x_2027_ = lean_unsigned_to_nat(2u);
v___x_2028_ = lean_array_fget_borrowed(v_chain_2001_, v___x_2020_);
lean_dec(v___x_2020_);
v___x_2029_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_inc(v___x_2018_);
v___x_2030_ = lean_array_push(v_fst_2008_, v___x_2018_);
lean_inc(v___x_2028_);
v___x_2031_ = lean_array_push(v___x_2030_, v___x_2028_);
v___x_2032_ = lean_box(0);
v___x_2033_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2009_, v___x_2027_, v___x_2032_, v___x_2031_);
lean_dec(v_snd_2009_);
v___y_2004_ = v___x_2033_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_box(0);
v___x_2035_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2009_, v___x_2027_, v___x_2034_, v_fst_2008_);
lean_dec(v_snd_2009_);
v___y_2004_ = v___x_2035_;
goto v___jp_2003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object* v___x_2037_, lean_object* v_chain_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2037_, v_chain_2038_, v_a_2039_);
lean_dec_ref(v_chain_2038_);
lean_dec(v___x_2037_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(lean_object* v___x_2041_, lean_object* v_chain_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v___y_2045_; lean_object* v_fst_2049_; lean_object* v_snd_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2077_; 
v_fst_2049_ = lean_ctor_get(v_a_2043_, 0);
v_snd_2050_ = lean_ctor_get(v_a_2043_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_a_2043_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2052_ = v_a_2043_;
v_isShared_2053_ = v_isSharedCheck_2077_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_snd_2050_);
lean_inc(v_fst_2049_);
lean_dec(v_a_2043_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2077_;
goto v_resetjp_2051_;
}
v___jp_2044_:
{
if (lean_obj_tag(v___y_2045_) == 0)
{
lean_object* v_a_2046_; 
v_a_2046_ = lean_ctor_get(v___y_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___y_2045_, 1);
return v_a_2046_;
}
else
{
lean_object* v_a_2047_; 
v_a_2047_ = lean_ctor_get(v___y_2045_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___y_2045_, 1);
v_a_2043_ = v_a_2047_;
goto _start;
}
}
v_resetjp_2051_:
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_nat_dec_lt(v_snd_2050_, v___x_2041_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2056_; 
if (v_isShared_2053_ == 0)
{
v___x_2056_ = v___x_2052_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_fst_2049_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2050_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2058_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2059_ = lean_array_get_borrowed(v___x_2058_, v_chain_2042_, v_snd_2050_);
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = lean_nat_add(v_snd_2050_, v___x_2060_);
v___x_2062_ = lean_array_get_size(v_chain_2042_);
v___x_2063_ = lean_nat_dec_lt(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_dec(v___x_2061_);
lean_inc(v___x_2059_);
v___x_2064_ = lean_array_push(v_fst_2049_, v___x_2059_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2064_);
v___x_2066_ = v___x_2052_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_snd_2050_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
else
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
lean_del_object(v___x_2052_);
v___x_2068_ = lean_unsigned_to_nat(2u);
v___x_2069_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2059_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2070_ = lean_array_fget_borrowed(v_chain_2042_, v___x_2061_);
lean_dec(v___x_2061_);
lean_inc(v___x_2059_);
v___x_2071_ = lean_array_push(v_fst_2049_, v___x_2059_);
lean_inc(v___x_2070_);
v___x_2072_ = lean_array_push(v___x_2071_, v___x_2070_);
v___x_2073_ = lean_box(0);
v___x_2074_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2050_, v___x_2068_, v___x_2073_, v___x_2072_);
lean_dec(v_snd_2050_);
v___y_2045_ = v___x_2074_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v___x_2061_);
v___x_2075_ = lean_box(0);
v___x_2076_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2050_, v___x_2068_, v___x_2075_, v_fst_2049_);
lean_dec(v_snd_2050_);
v___y_2045_ = v___x_2076_;
goto v___jp_2044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___boxed(lean_object* v___x_2078_, lean_object* v_chain_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2078_, v_chain_2079_, v_a_2080_);
lean_dec_ref(v_chain_2079_);
lean_dec(v___x_2078_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(lean_object* v_format_2090_, lean_object* v_chain_2091_){
_start:
{
lean_object* v___y_2093_; lean_object* v___y_2094_; uint8_t v___y_2095_; lean_object* v___y_2096_; uint8_t v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2114_; uint8_t v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; uint8_t v___y_2118_; lean_object* v___y_2119_; lean_object* v___f_2134_; lean_object* v___x_2135_; lean_object* v_chainSizeBeforeSuffixTrim_2136_; lean_object* v_chain_2137_; lean_object* v_chainSizeBeforePrefixTrim_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___y_2144_; uint8_t v___y_2145_; lean_object* v___y_2146_; uint8_t v___y_2147_; uint8_t v___y_2148_; lean_object* v___y_2160_; uint8_t v___y_2161_; lean_object* v___y_2162_; uint8_t v___y_2163_; uint8_t v___y_2168_; uint8_t v___x_2178_; 
v___f_2134_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0));
v___x_2135_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_chainSizeBeforeSuffixTrim_2136_ = lean_array_get_size(v_chain_2091_);
v_chain_2137_ = l_Array_popWhile___redArg(v___f_2134_, v_chain_2091_);
v_chainSizeBeforePrefixTrim_2138_ = lean_array_get_size(v_chain_2137_);
v___x_2139_ = lean_nat_sub(v_chainSizeBeforeSuffixTrim_2136_, v_chainSizeBeforePrefixTrim_2138_);
v___x_2140_ = lean_unsigned_to_nat(2u);
v___x_2141_ = lean_nat_mod(v___x_2139_, v___x_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2178_ = lean_nat_dec_eq(v___x_2141_, v___x_2142_);
lean_dec(v___x_2141_);
if (v___x_2178_ == 0)
{
uint8_t v___x_2179_; 
v___x_2179_ = 1;
v___y_2168_ = v___x_2179_;
goto v___jp_2167_;
}
else
{
uint8_t v___x_2180_; 
v___x_2180_ = 0;
v___y_2168_ = v___x_2180_;
goto v___jp_2167_;
}
v___jp_2092_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v_fst_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2111_; 
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___y_2093_);
lean_ctor_set(v___x_2099_, 1, v___y_2098_);
v___x_2100_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___y_2096_, v___y_2094_, v___x_2099_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2096_);
v_fst_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v___x_2100_, 1);
lean_dec(v_unused_2112_);
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_fst_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2105_ = lean_box(v___y_2097_);
v___x_2106_ = lean_box(v___y_2095_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 1, v___x_2106_);
lean_ctor_set(v___x_2103_, 0, v___x_2105_);
v___x_2108_ = v___x_2103_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v_fst_2101_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
return v___x_2109_;
}
}
}
v___jp_2113_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v_fst_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2132_; 
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___y_2117_);
lean_ctor_set(v___x_2120_, 1, v___y_2119_);
v___x_2121_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___y_2116_, v___y_2114_, v___x_2120_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2116_);
v_fst_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v___x_2121_, 1);
lean_dec(v_unused_2133_);
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2132_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_fst_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2132_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2126_ = lean_box(v___y_2118_);
v___x_2127_ = lean_box(v___y_2115_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v___x_2127_);
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2129_ = v___x_2124_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_fst_2122_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
return v___x_2130_;
}
}
}
v___jp_2143_:
{
if (v___y_2148_ == 0)
{
if (v___y_2147_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2149_ = lean_array_get_borrowed(v___x_2135_, v___y_2144_, v___x_2142_);
v___x_2150_ = lean_unsigned_to_nat(1u);
v___x_2151_ = lean_mk_empty_array_with_capacity(v___x_2150_);
lean_inc(v___x_2149_);
v___x_2152_ = lean_array_push(v___x_2151_, v___x_2149_);
v___y_2114_ = v___y_2144_;
v___y_2115_ = v___y_2145_;
v___y_2116_ = v___y_2146_;
v___y_2117_ = v___x_2152_;
v___y_2118_ = v___y_2147_;
v___y_2119_ = v___x_2150_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2153_; 
v___x_2153_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2114_ = v___y_2144_;
v___y_2115_ = v___y_2145_;
v___y_2116_ = v___y_2146_;
v___y_2117_ = v___x_2153_;
v___y_2118_ = v___y_2147_;
v___y_2119_ = v___x_2142_;
goto v___jp_2113_;
}
}
else
{
if (v___y_2147_ == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2093_ = v___x_2154_;
v___y_2094_ = v___y_2144_;
v___y_2095_ = v___y_2145_;
v___y_2096_ = v___y_2146_;
v___y_2097_ = v___y_2147_;
v___y_2098_ = v___x_2142_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2155_ = lean_array_get_borrowed(v___x_2135_, v___y_2144_, v___x_2142_);
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = lean_mk_empty_array_with_capacity(v___x_2156_);
lean_inc(v___x_2155_);
v___x_2158_ = lean_array_push(v___x_2157_, v___x_2155_);
v___y_2093_ = v___x_2158_;
v___y_2094_ = v___y_2144_;
v___y_2095_ = v___y_2145_;
v___y_2096_ = v___y_2146_;
v___y_2097_ = v___y_2147_;
v___y_2098_ = v___x_2156_;
goto v___jp_2092_;
}
}
}
v___jp_2159_:
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_nat_dec_eq(v___y_2162_, v___x_2142_);
if (v___x_2164_ == 0)
{
uint8_t v_trailingOperator_2165_; 
v_trailingOperator_2165_ = lean_ctor_get_uint8(v_format_2090_, 1);
v___y_2144_ = v___y_2160_;
v___y_2145_ = v___y_2161_;
v___y_2146_ = v___y_2162_;
v___y_2147_ = v___y_2163_;
v___y_2148_ = v_trailingOperator_2165_;
goto v___jp_2143_;
}
else
{
lean_object* v___x_2166_; 
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2160_);
v___x_2166_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2));
return v___x_2166_;
}
}
v___jp_2167_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v_chain_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2169_ = l_Array_reverse___redArg(v_chain_2137_);
v___x_2170_ = l_Array_popWhile___redArg(v___f_2134_, v___x_2169_);
v_chain_2171_ = l_Array_reverse___redArg(v___x_2170_);
v___x_2172_ = lean_array_get_size(v_chain_2171_);
v___x_2173_ = lean_nat_sub(v_chainSizeBeforePrefixTrim_2138_, v___x_2172_);
v___x_2174_ = lean_nat_mod(v___x_2173_, v___x_2140_);
lean_dec(v___x_2173_);
v___x_2175_ = lean_nat_dec_eq(v___x_2174_, v___x_2142_);
lean_dec(v___x_2174_);
if (v___x_2175_ == 0)
{
uint8_t v___x_2176_; 
v___x_2176_ = 1;
v___y_2160_ = v_chain_2171_;
v___y_2161_ = v___y_2168_;
v___y_2162_ = v___x_2172_;
v___y_2163_ = v___x_2176_;
goto v___jp_2159_;
}
else
{
uint8_t v___x_2177_; 
v___x_2177_ = 0;
v___y_2160_ = v_chain_2171_;
v___y_2161_ = v___y_2168_;
v___y_2162_ = v___x_2172_;
v___y_2163_ = v___x_2177_;
goto v___jp_2159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___boxed(lean_object* v_format_2181_, lean_object* v_chain_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2181_, v_chain_2182_);
lean_dec_ref(v_format_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(lean_object* v___x_2184_, lean_object* v_chain_2185_, lean_object* v_inst_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2184_, v_chain_2185_, v_a_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___boxed(lean_object* v___x_2189_, lean_object* v_chain_2190_, lean_object* v_inst_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(v___x_2189_, v_chain_2190_, v_inst_2191_, v_a_2192_);
lean_dec_ref(v_chain_2190_);
lean_dec(v___x_2189_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object* v___x_2194_, lean_object* v_chain_2195_, lean_object* v_inst_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2194_, v_chain_2195_, v_a_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object* v___x_2199_, lean_object* v_chain_2200_, lean_object* v_inst_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(v___x_2199_, v_chain_2200_, v_inst_2201_, v_a_2202_);
lean_dec_ref(v_chain_2200_);
lean_dec(v___x_2199_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(lean_object* v_chain_2204_, lean_object* v_format_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_fst_2207_; lean_object* v_snd_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2238_; 
v_fst_2207_ = lean_ctor_get(v_a_2206_, 0);
v_snd_2208_ = lean_ctor_get(v_a_2206_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_a_2206_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2210_ = v_a_2206_;
v_isShared_2211_ = v_isSharedCheck_2238_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_snd_2208_);
lean_inc(v_fst_2207_);
lean_dec(v_a_2206_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2238_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = lean_array_get_size(v_chain_2204_);
v___x_2213_ = lean_nat_dec_lt(v_snd_2208_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2215_; 
if (v_isShared_2211_ == 0)
{
v___x_2215_ = v___x_2210_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_fst_2207_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_snd_2208_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___y_2220_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2217_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2218_ = lean_array_get_borrowed(v___x_2217_, v_chain_2204_, v_snd_2208_);
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = lean_nat_add(v_snd_2208_, v___x_2233_);
v___x_2235_ = lean_nat_dec_lt(v___x_2234_, v___x_2212_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; 
lean_dec(v___x_2234_);
v___x_2236_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2220_ = v___x_2236_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_array_fget_borrowed(v_chain_2204_, v___x_2234_);
lean_dec(v___x_2234_);
lean_inc(v___x_2237_);
v___y_2220_ = v___x_2237_;
goto v___jp_2219_;
}
v___jp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2221_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2220_);
v___x_2222_ = lean_unsigned_to_nat(2u);
v___x_2223_ = lean_mk_empty_array_with_capacity(v___x_2222_);
lean_inc(v___x_2218_);
v___x_2224_ = lean_array_push(v___x_2223_, v___x_2218_);
v___x_2225_ = lean_array_push(v___x_2224_, v___x_2221_);
v___x_2226_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2205_, v___x_2225_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = lean_array_push(v_fst_2207_, v___x_2226_);
v___x_2228_ = lean_nat_add(v_snd_2208_, v___x_2222_);
lean_dec(v_snd_2208_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 1, v___x_2228_);
lean_ctor_set(v___x_2210_, 0, v___x_2227_);
v___x_2230_ = v___x_2210_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
v_a_2206_ = v___x_2230_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg___boxed(lean_object* v_chain_2239_, lean_object* v_format_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2239_, v_format_2240_, v_a_2241_);
lean_dec_ref(v_format_2240_);
lean_dec_ref(v_chain_2239_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(lean_object* v_chain_2243_, lean_object* v_format_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_fst_2246_; lean_object* v_snd_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2277_; 
v_fst_2246_ = lean_ctor_get(v_a_2245_, 0);
v_snd_2247_ = lean_ctor_get(v_a_2245_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_a_2245_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2249_ = v_a_2245_;
v_isShared_2250_ = v_isSharedCheck_2277_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_snd_2247_);
lean_inc(v_fst_2246_);
lean_dec(v_a_2245_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2277_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_array_get_size(v_chain_2243_);
v___x_2252_ = lean_nat_dec_lt(v_snd_2247_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2254_; 
if (v_isShared_2250_ == 0)
{
v___x_2254_ = v___x_2249_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_fst_2246_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_snd_2247_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___y_2259_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2256_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2257_ = lean_array_get_borrowed(v___x_2256_, v_chain_2243_, v_snd_2247_);
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_add(v_snd_2247_, v___x_2272_);
v___x_2274_ = lean_nat_dec_lt(v___x_2273_, v___x_2251_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; 
lean_dec(v___x_2273_);
v___x_2275_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2259_ = v___x_2275_;
goto v___jp_2258_;
}
else
{
lean_object* v___x_2276_; 
v___x_2276_ = lean_array_fget_borrowed(v_chain_2243_, v___x_2273_);
lean_dec(v___x_2273_);
lean_inc(v___x_2276_);
v___y_2259_ = v___x_2276_;
goto v___jp_2258_;
}
v___jp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
lean_inc(v___x_2257_);
v___x_2260_ = l_Lean_Fmt_TaggedDoc_nested(v___x_2257_);
v___x_2261_ = lean_unsigned_to_nat(2u);
v___x_2262_ = lean_mk_empty_array_with_capacity(v___x_2261_);
v___x_2263_ = lean_array_push(v___x_2262_, v___x_2260_);
v___x_2264_ = lean_array_push(v___x_2263_, v___y_2259_);
v___x_2265_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2244_, v___x_2264_);
lean_dec_ref(v___x_2264_);
v___x_2266_ = lean_array_push(v_fst_2246_, v___x_2265_);
v___x_2267_ = lean_nat_add(v_snd_2247_, v___x_2261_);
lean_dec(v_snd_2247_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v___x_2267_);
lean_ctor_set(v___x_2249_, 0, v___x_2266_);
v___x_2269_ = v___x_2249_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
v_a_2245_ = v___x_2269_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg___boxed(lean_object* v_chain_2278_, lean_object* v_format_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2278_, v_format_2279_, v_a_2280_);
lean_dec_ref(v_format_2279_);
lean_dec_ref(v_chain_2278_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(lean_object* v_format_2282_, lean_object* v_chain_2283_, uint8_t v_isHeadless_2284_){
_start:
{
lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2292_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2302_; lean_object* v___x_2305_; uint8_t v___y_2307_; uint8_t v_trailingOperator_2320_; 
v___x_2305_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_2320_ = lean_ctor_get_uint8(v_format_2282_, 1);
v___y_2307_ = v_trailingOperator_2320_;
goto v___jp_2306_;
v___jp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v_fst_2290_; 
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___y_2286_);
lean_ctor_set(v___x_2288_, 1, v___y_2287_);
v___x_2289_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2283_, v_format_2282_, v___x_2288_);
v_fst_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_fst_2290_);
lean_dec_ref(v___x_2289_);
return v_fst_2290_;
}
v___jp_2291_:
{
if (v_isHeadless_2284_ == 0)
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_unsigned_to_nat(0u);
v___y_2286_ = v___y_2292_;
v___y_2287_ = v___x_2293_;
goto v___jp_2285_;
}
else
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_unsigned_to_nat(1u);
v___y_2286_ = v___y_2292_;
v___y_2287_ = v___x_2294_;
goto v___jp_2285_;
}
}
v___jp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_fst_2300_; 
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___y_2296_);
lean_ctor_set(v___x_2298_, 1, v___y_2297_);
v___x_2299_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2283_, v_format_2282_, v___x_2298_);
v_fst_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_fst_2300_);
lean_dec_ref(v___x_2299_);
return v_fst_2300_;
}
v___jp_2301_:
{
if (v_isHeadless_2284_ == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_unsigned_to_nat(1u);
v___y_2296_ = v___y_2302_;
v___y_2297_ = v___x_2303_;
goto v___jp_2295_;
}
else
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_unsigned_to_nat(0u);
v___y_2296_ = v___y_2302_;
v___y_2297_ = v___x_2304_;
goto v___jp_2295_;
}
}
v___jp_2306_:
{
if (v___y_2307_ == 0)
{
if (v_isHeadless_2284_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = lean_array_get_borrowed(v___x_2305_, v_chain_2283_, v___x_2308_);
v___x_2310_ = lean_unsigned_to_nat(1u);
v___x_2311_ = lean_mk_empty_array_with_capacity(v___x_2310_);
lean_inc(v___x_2309_);
v___x_2312_ = lean_array_push(v___x_2311_, v___x_2309_);
v___y_2302_ = v___x_2312_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2302_ = v___x_2313_;
goto v___jp_2301_;
}
}
else
{
if (v_isHeadless_2284_ == 0)
{
lean_object* v___x_2314_; 
v___x_2314_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2292_ = v___x_2314_;
goto v___jp_2291_;
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_array_get_borrowed(v___x_2305_, v_chain_2283_, v___x_2315_);
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___x_2317_);
lean_inc(v___x_2316_);
v___x_2319_ = lean_array_push(v___x_2318_, v___x_2316_);
v___y_2292_ = v___x_2319_;
goto v___jp_2291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain___boxed(lean_object* v_format_2321_, lean_object* v_chain_2322_, lean_object* v_isHeadless_2323_){
_start:
{
uint8_t v_isHeadless_boxed_2324_; lean_object* v_res_2325_; 
v_isHeadless_boxed_2324_ = lean_unbox(v_isHeadless_2323_);
v_res_2325_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2321_, v_chain_2322_, v_isHeadless_boxed_2324_);
lean_dec_ref(v_chain_2322_);
lean_dec_ref(v_format_2321_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(lean_object* v_chain_2326_, lean_object* v_format_2327_, lean_object* v_inst_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2326_, v_format_2327_, v_a_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___boxed(lean_object* v_chain_2331_, lean_object* v_format_2332_, lean_object* v_inst_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(v_chain_2331_, v_format_2332_, v_inst_2333_, v_a_2334_);
lean_dec_ref(v_format_2332_);
lean_dec_ref(v_chain_2331_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(lean_object* v_chain_2336_, lean_object* v_format_2337_, lean_object* v_inst_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2336_, v_format_2337_, v_a_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___boxed(lean_object* v_chain_2341_, lean_object* v_format_2342_, lean_object* v_inst_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(v_chain_2341_, v_format_2342_, v_inst_2343_, v_a_2344_);
lean_dec_ref(v_format_2342_);
lean_dec_ref(v_chain_2341_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(lean_object* v_format_2346_, lean_object* v_docs_2347_){
_start:
{
uint8_t v___y_2349_; uint8_t v___x_2352_; 
v___x_2352_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_format_2346_);
if (v___x_2352_ == 0)
{
uint8_t v___x_2353_; 
v___x_2353_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_format_2346_);
if (v___x_2353_ == 0)
{
uint8_t v_spacing_2354_; 
v_spacing_2354_ = lean_ctor_get_uint8(v_format_2346_, 2);
v___y_2349_ = v_spacing_2354_;
goto v___jp_2348_;
}
else
{
lean_object* v___x_2355_; uint8_t v___y_2357_; uint8_t v_spacing_2384_; 
v___x_2355_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_spacing_2384_ = lean_ctor_get_uint8(v_format_2346_, 2);
v___y_2357_ = v_spacing_2384_;
goto v___jp_2356_;
v___jp_2356_:
{
if (v___y_2357_ == 0)
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2358_ = lean_unsigned_to_nat(0u);
v___x_2359_ = lean_array_get_size(v_docs_2347_);
v___x_2360_ = lean_unsigned_to_nat(1u);
v___x_2361_ = lean_nat_sub(v___x_2359_, v___x_2360_);
lean_inc(v___x_2361_);
lean_inc_ref(v_docs_2347_);
v___x_2362_ = l_Array_toSubarray___redArg(v_docs_2347_, v___x_2358_, v___x_2361_);
v___x_2363_ = l_Subarray_copy___redArg(v___x_2362_);
v___x_2364_ = l_Lean_Fmt_TaggedDoc_fill(v___x_2363_);
v___x_2365_ = lean_array_get(v___x_2355_, v_docs_2347_, v___x_2361_);
lean_dec(v___x_2361_);
lean_dec_ref(v_docs_2347_);
v___x_2366_ = lean_unsigned_to_nat(2u);
v___x_2367_ = lean_mk_empty_array_with_capacity(v___x_2366_);
v___x_2368_ = lean_array_push(v___x_2367_, v___x_2364_);
v___x_2369_ = lean_array_push(v___x_2368_, v___x_2365_);
v___x_2370_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2369_, v___y_2357_);
lean_dec_ref(v___x_2369_);
return v___x_2370_;
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = lean_array_get_size(v_docs_2347_);
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_sub(v___x_2372_, v___x_2373_);
lean_inc(v___x_2374_);
lean_inc_ref(v_docs_2347_);
v___x_2375_ = l_Array_toSubarray___redArg(v_docs_2347_, v___x_2371_, v___x_2374_);
v___x_2376_ = l_Subarray_copy___redArg(v___x_2375_);
v___x_2377_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_2376_);
v___x_2378_ = lean_array_get(v___x_2355_, v_docs_2347_, v___x_2374_);
lean_dec(v___x_2374_);
lean_dec_ref(v_docs_2347_);
v___x_2379_ = lean_unsigned_to_nat(2u);
v___x_2380_ = lean_mk_empty_array_with_capacity(v___x_2379_);
v___x_2381_ = lean_array_push(v___x_2380_, v___x_2377_);
v___x_2382_ = lean_array_push(v___x_2381_, v___x_2378_);
v___x_2383_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2382_, v___x_2353_);
lean_dec_ref(v___x_2382_);
return v___x_2383_;
}
}
}
}
else
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Fmt_Layouts_lines(v_docs_2347_);
lean_dec_ref(v_docs_2347_);
return v___x_2385_;
}
v___jp_2348_:
{
if (v___y_2349_ == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Fmt_TaggedDoc_fill(v_docs_2347_);
return v___x_2350_;
}
else
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v_docs_2347_);
return v___x_2351_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill___boxed(lean_object* v_format_2386_, lean_object* v_docs_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2386_, v_docs_2387_);
lean_dec_ref(v_format_2386_);
return v_res_2388_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(lean_object* v_columnPos_2389_, lean_object* v_indentation_2390_, lean_object* v_nonCumulativeIndentation_2391_){
_start:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = lean_nat_add(v_indentation_2390_, v_nonCumulativeIndentation_2391_);
v___x_2393_ = lean_nat_dec_le(v_columnPos_2389_, v___x_2392_);
lean_dec(v___x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed(lean_object* v_columnPos_2394_, lean_object* v_indentation_2395_, lean_object* v_nonCumulativeIndentation_2396_){
_start:
{
uint8_t v_res_2397_; lean_object* v_r_2398_; 
v_res_2397_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(v_columnPos_2394_, v_indentation_2395_, v_nonCumulativeIndentation_2396_);
lean_dec(v_nonCumulativeIndentation_2396_);
lean_dec(v_indentation_2395_);
lean_dec(v_columnPos_2394_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(lean_object* v_format_2415_, lean_object* v_combinedChain_2416_){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v_firstOperand_2419_; lean_object* v___y_2421_; uint8_t v___y_2441_; uint8_t v_hardNestedFirstOperand_2448_; 
v___x_2417_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2418_ = lean_unsigned_to_nat(0u);
v_firstOperand_2419_ = lean_array_get_borrowed(v___x_2417_, v_combinedChain_2416_, v___x_2418_);
v_hardNestedFirstOperand_2448_ = lean_ctor_get_uint8(v_format_2415_, 0);
v___y_2441_ = v_hardNestedFirstOperand_2448_;
goto v___jp_2440_;
v___jp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v_compactFirstOperation_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_compactedChain_2435_; lean_object* v___x_2436_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion));
v___x_2423_ = l_Lean_Fmt_TaggedDoc_guarded(v___x_2422_, v___y_2421_);
v___x_2424_ = lean_unsigned_to_nat(2u);
v___x_2425_ = lean_mk_empty_array_with_capacity(v___x_2424_);
lean_inc(v_firstOperand_2419_);
v___x_2426_ = lean_array_push(v___x_2425_, v_firstOperand_2419_);
v___x_2427_ = lean_array_push(v___x_2426_, v___x_2423_);
v_compactFirstOperation_2428_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2415_, v___x_2427_);
lean_dec_ref(v___x_2427_);
v___x_2429_ = lean_unsigned_to_nat(1u);
v___x_2430_ = lean_mk_empty_array_with_capacity(v___x_2429_);
v___x_2431_ = lean_array_push(v___x_2430_, v_compactFirstOperation_2428_);
v___x_2432_ = lean_array_get_size(v_combinedChain_2416_);
v___x_2433_ = l_Array_toSubarray___redArg(v_combinedChain_2416_, v___x_2424_, v___x_2432_);
v___x_2434_ = l_Subarray_copy___redArg(v___x_2433_);
v_compactedChain_2435_ = l_Array_append___redArg(v___x_2431_, v___x_2434_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2415_, v_compactedChain_2435_);
return v___x_2436_;
}
v___jp_2437_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = lean_unsigned_to_nat(1u);
v___x_2439_ = lean_array_get_borrowed(v___x_2417_, v_combinedChain_2416_, v___x_2438_);
lean_inc(v___x_2439_);
v___y_2421_ = v___x_2439_;
goto v___jp_2420_;
}
v___jp_2440_:
{
if (v___y_2441_ == 0)
{
goto v___jp_2437_;
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2442_ = lean_unsigned_to_nat(2u);
v___x_2443_ = lean_array_get_size(v_combinedChain_2416_);
v___x_2444_ = lean_nat_dec_lt(v___x_2442_, v___x_2443_);
if (v___x_2444_ == 0)
{
goto v___jp_2437_;
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = lean_unsigned_to_nat(1u);
v___x_2446_ = lean_array_get_borrowed(v___x_2417_, v_combinedChain_2416_, v___x_2445_);
lean_inc(v___x_2446_);
v___x_2447_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_2446_);
v___y_2421_ = v___x_2447_;
goto v___jp_2420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation___boxed(lean_object* v_format_2449_, lean_object* v_combinedChain_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2449_, v_combinedChain_2450_);
lean_dec_ref(v_format_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(lean_object* v_format_2452_, lean_object* v_docs_2453_, lean_object* v_wrap_2454_){
_start:
{
uint8_t v___y_2456_; uint8_t v_spacing_2459_; 
v_spacing_2459_ = lean_ctor_get_uint8(v_format_2452_, 2);
v___y_2456_ = v_spacing_2459_;
goto v___jp_2455_;
v___jp_2455_:
{
if (v___y_2456_ == 0)
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_Fmt_TaggedDoc_fillWrapping(v_docs_2453_, v_wrap_2454_);
return v___x_2457_;
}
else
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(v_docs_2453_, v_wrap_2454_);
return v___x_2458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping___boxed(lean_object* v_format_2460_, lean_object* v_docs_2461_, lean_object* v_wrap_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2460_, v_docs_2461_, v_wrap_2462_);
lean_dec_ref(v_format_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(lean_object* v___x_2464_, size_t v_sz_2465_, size_t v_i_2466_, lean_object* v_bs_2467_){
_start:
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_usize_dec_lt(v_i_2466_, v_sz_2465_);
if (v___x_2468_ == 0)
{
return v_bs_2467_;
}
else
{
lean_object* v___x_2469_; lean_object* v_v_2470_; lean_object* v___x_2471_; lean_object* v_bs_x27_2472_; lean_object* v___y_2474_; lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2469_ = lean_unsigned_to_nat(1u);
v_v_2470_ = lean_array_uget(v_bs_2467_, v_i_2466_);
v___x_2471_ = lean_unsigned_to_nat(0u);
v_bs_x27_2472_ = lean_array_uset(v_bs_2467_, v_i_2466_, v___x_2471_);
v___x_2479_ = lean_usize_to_nat(v_i_2466_);
v___x_2480_ = lean_nat_sub(v___x_2464_, v___x_2469_);
v___x_2481_ = lean_nat_dec_lt(v___x_2479_, v___x_2480_);
lean_dec(v___x_2480_);
lean_dec(v___x_2479_);
if (v___x_2481_ == 0)
{
v___y_2474_ = v_v_2470_;
goto v___jp_2473_;
}
else
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2470_);
v___y_2474_ = v___x_2482_;
goto v___jp_2473_;
}
v___jp_2473_:
{
size_t v___x_2475_; size_t v___x_2476_; lean_object* v___x_2477_; 
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2466_, v___x_2475_);
v___x_2477_ = lean_array_uset(v_bs_x27_2472_, v_i_2466_, v___y_2474_);
v_i_2466_ = v___x_2476_;
v_bs_2467_ = v___x_2477_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg___boxed(lean_object* v___x_2483_, lean_object* v_sz_2484_, lean_object* v_i_2485_, lean_object* v_bs_2486_){
_start:
{
size_t v_sz_boxed_2487_; size_t v_i_boxed_2488_; lean_object* v_res_2489_; 
v_sz_boxed_2487_ = lean_unbox_usize(v_sz_2484_);
lean_dec(v_sz_2484_);
v_i_boxed_2488_ = lean_unbox_usize(v_i_2485_);
lean_dec(v_i_2485_);
v_res_2489_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2483_, v_sz_boxed_2487_, v_i_boxed_2488_, v_bs_2486_);
lean_dec(v___x_2483_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object* v_chain_2504_, lean_object* v_format_2505_){
_start:
{
uint8_t v___y_2507_; lean_object* v_doc_2508_; lean_object* v___x_2512_; lean_object* v_snd_2513_; lean_object* v_fst_2514_; lean_object* v_fst_2515_; lean_object* v_snd_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2512_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2505_, v_chain_2504_);
v_snd_2513_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_snd_2513_);
v_fst_2514_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_fst_2514_);
lean_dec_ref(v___x_2512_);
v_fst_2515_ = lean_ctor_get(v_snd_2513_, 0);
lean_inc(v_fst_2515_);
v_snd_2516_ = lean_ctor_get(v_snd_2513_, 1);
lean_inc(v_snd_2516_);
lean_dec(v_snd_2513_);
v___x_2517_ = lean_array_get_size(v_fst_2514_);
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = lean_nat_dec_eq(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; uint8_t v___x_2521_; lean_object* v_combinedChain_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___y_2526_; uint8_t v___y_2527_; lean_object* v_doc_2528_; lean_object* v___y_2543_; lean_object* v___y_2544_; uint8_t v___y_2545_; uint8_t v___x_2552_; lean_object* v___y_2554_; uint8_t v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2559_; uint8_t v___y_2560_; lean_object* v___y_2563_; uint8_t v___y_2564_; lean_object* v_combinedChain_2569_; uint8_t v___y_2572_; uint8_t v___y_2579_; uint8_t v___y_2580_; uint8_t v___y_2588_; uint8_t v___y_2591_; 
v___x_2520_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2521_ = lean_unbox(v_fst_2515_);
v_combinedChain_2522_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2505_, v_fst_2514_, v___x_2521_);
v___x_2523_ = lean_array_get_size(v_combinedChain_2522_);
v___x_2524_ = lean_unsigned_to_nat(1u);
v___x_2552_ = lean_nat_dec_eq(v___x_2523_, v___x_2524_);
if (v___x_2552_ == 0)
{
uint8_t v_trailingOperator_2592_; 
v_trailingOperator_2592_ = lean_ctor_get_uint8(v_format_2505_, 1);
v___y_2591_ = v_trailingOperator_2592_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2593_; 
lean_dec(v_snd_2516_);
lean_dec(v_fst_2515_);
lean_dec(v_fst_2514_);
v___x_2593_ = lean_array_get(v___x_2520_, v_combinedChain_2522_, v___x_2518_);
lean_dec_ref(v_combinedChain_2522_);
return v___x_2593_;
}
v___jp_2525_:
{
lean_object* v___x_2529_; lean_object* v_lastOperand_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2529_ = lean_nat_sub(v___x_2517_, v___x_2524_);
v_lastOperand_2530_ = lean_array_get(v___x_2520_, v_fst_2514_, v___x_2529_);
lean_dec(v___x_2529_);
lean_dec(v_fst_2514_);
v___x_2531_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
v___x_2532_ = lean_unbox(v_snd_2516_);
lean_inc_ref(v___y_2526_);
lean_inc(v_lastOperand_2530_);
lean_inc_ref(v_doc_2528_);
v___x_2533_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2505_, v_doc_2528_, v_lastOperand_2530_, v___x_2532_, v___y_2526_, v___x_2531_);
if (lean_obj_tag(v___x_2533_) == 1)
{
lean_object* v_val_2534_; 
lean_dec(v_lastOperand_2530_);
lean_dec_ref(v_doc_2528_);
lean_dec_ref(v___y_2526_);
lean_dec(v_snd_2516_);
v_val_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_val_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___y_2507_ = v___y_2527_;
v_doc_2508_ = v_val_2534_;
goto v___jp_2506_;
}
else
{
uint8_t v___x_2535_; lean_object* v___x_2536_; 
lean_dec(v___x_2533_);
v___x_2535_ = lean_unbox(v_snd_2516_);
lean_inc_ref(v___y_2526_);
lean_inc(v_lastOperand_2530_);
lean_inc_ref(v_doc_2528_);
v___x_2536_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2505_, v_doc_2528_, v_lastOperand_2530_, v___x_2535_, v___y_2526_);
if (lean_obj_tag(v___x_2536_) == 1)
{
lean_object* v_val_2537_; 
lean_dec(v_lastOperand_2530_);
lean_dec_ref(v_doc_2528_);
lean_dec_ref(v___y_2526_);
lean_dec(v_snd_2516_);
v_val_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_val_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v___y_2507_ = v___y_2527_;
v_doc_2508_ = v_val_2537_;
goto v___jp_2506_;
}
else
{
lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; 
lean_dec(v___x_2536_);
v___x_2538_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
v___x_2539_ = lean_unbox(v_snd_2516_);
lean_dec(v_snd_2516_);
lean_inc_ref(v_doc_2528_);
v___x_2540_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2505_, v_doc_2528_, v_lastOperand_2530_, v___x_2539_, v___y_2526_, v___x_2538_);
if (lean_obj_tag(v___x_2540_) == 1)
{
lean_object* v_val_2541_; 
lean_dec_ref(v_doc_2528_);
v_val_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_val_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v___y_2507_ = v___y_2527_;
v_doc_2508_ = v_val_2541_;
goto v___jp_2506_;
}
else
{
lean_dec(v___x_2540_);
v___y_2507_ = v___y_2527_;
v_doc_2508_ = v_doc_2528_;
goto v___jp_2506_;
}
}
}
}
v___jp_2542_:
{
if (v___y_2545_ == 0)
{
v___y_2526_ = v___y_2543_;
v___y_2527_ = v___y_2545_;
v_doc_2528_ = v___y_2544_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v_doc_2551_; 
lean_inc_ref(v___y_2543_);
v___x_2546_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2505_, v___y_2543_);
v___x_2547_ = lean_unsigned_to_nat(2u);
v___x_2548_ = lean_mk_empty_array_with_capacity(v___x_2547_);
v___x_2549_ = lean_array_push(v___x_2548_, v___x_2546_);
v___x_2550_ = lean_array_push(v___x_2549_, v___y_2544_);
v_doc_2551_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2550_);
v___y_2526_ = v___y_2543_;
v___y_2527_ = v___y_2545_;
v_doc_2528_ = v_doc_2551_;
goto v___jp_2525_;
}
}
v___jp_2553_:
{
uint8_t v___x_2557_; 
v___x_2557_ = lean_unbox(v_fst_2515_);
lean_dec(v_fst_2515_);
if (v___x_2557_ == 0)
{
v___y_2543_ = v___y_2554_;
v___y_2544_ = v___y_2556_;
v___y_2545_ = v___y_2555_;
goto v___jp_2542_;
}
else
{
if (v___x_2552_ == 0)
{
v___y_2526_ = v___y_2554_;
v___y_2527_ = v___y_2555_;
v_doc_2528_ = v___y_2556_;
goto v___jp_2525_;
}
else
{
v___y_2543_ = v___y_2554_;
v___y_2544_ = v___y_2556_;
v___y_2545_ = v___y_2555_;
goto v___jp_2542_;
}
}
}
v___jp_2558_:
{
lean_object* v___x_2561_; 
lean_inc_ref(v___y_2559_);
v___x_2561_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2505_, v___y_2559_);
v___y_2554_ = v___y_2559_;
v___y_2555_ = v___y_2560_;
v___y_2556_ = v___x_2561_;
goto v___jp_2553_;
}
v___jp_2562_:
{
if (v___y_2564_ == 0)
{
uint8_t v___x_2565_; 
v___x_2565_ = 1;
v___y_2559_ = v___y_2563_;
v___y_2560_ = v___x_2565_;
goto v___jp_2558_;
}
else
{
if (v___x_2552_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
lean_inc_ref(v___y_2563_);
v___x_2567_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2505_, v___y_2563_, v___x_2566_);
v___y_2554_ = v___y_2563_;
v___y_2555_ = v___x_2552_;
v___y_2556_ = v___x_2567_;
goto v___jp_2553_;
}
else
{
v___y_2559_ = v___y_2563_;
v___y_2560_ = v___x_2552_;
goto v___jp_2558_;
}
}
}
v___jp_2568_:
{
uint8_t v_trailingOperator_2570_; 
v_trailingOperator_2570_ = lean_ctor_get_uint8(v_format_2505_, 1);
v___y_2563_ = v_combinedChain_2569_;
v___y_2564_ = v_trailingOperator_2570_;
goto v___jp_2562_;
}
v___jp_2571_:
{
if (v___y_2572_ == 0)
{
v_combinedChain_2569_ = v_combinedChain_2522_;
goto v___jp_2568_;
}
else
{
size_t v_sz_2573_; size_t v___x_2574_; lean_object* v_combinedChain_2575_; 
v_sz_2573_ = lean_array_size(v_combinedChain_2522_);
v___x_2574_ = ((size_t)0ULL);
v_combinedChain_2575_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2523_, v_sz_2573_, v___x_2574_, v_combinedChain_2522_);
v_combinedChain_2569_ = v_combinedChain_2575_;
goto v___jp_2568_;
}
}
v___jp_2576_:
{
uint8_t v_hardNestedFirstOperand_2577_; 
v_hardNestedFirstOperand_2577_ = lean_ctor_get_uint8(v_format_2505_, 0);
v___y_2572_ = v_hardNestedFirstOperand_2577_;
goto v___jp_2571_;
}
v___jp_2578_:
{
if (v___y_2580_ == 0)
{
if (v___y_2579_ == 0)
{
v_combinedChain_2569_ = v_combinedChain_2522_;
goto v___jp_2568_;
}
else
{
goto v___jp_2576_;
}
}
else
{
uint8_t v___x_2581_; 
v___x_2581_ = lean_nat_dec_lt(v___x_2518_, v___x_2523_);
if (v___x_2581_ == 0)
{
v_combinedChain_2569_ = v_combinedChain_2522_;
goto v___jp_2568_;
}
else
{
lean_object* v_v_2582_; lean_object* v___x_2583_; lean_object* v_xs_x27_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_v_2582_ = lean_array_fget(v_combinedChain_2522_, v___x_2518_);
v___x_2583_ = lean_box(0);
v_xs_x27_2584_ = lean_array_fset(v_combinedChain_2522_, v___x_2518_, v___x_2583_);
v___x_2585_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2582_);
v___x_2586_ = lean_array_fset(v_xs_x27_2584_, v___x_2518_, v___x_2585_);
v_combinedChain_2569_ = v___x_2586_;
goto v___jp_2568_;
}
}
}
v___jp_2587_:
{
uint8_t v_hardNestedFirstOperand_2589_; 
v_hardNestedFirstOperand_2589_ = lean_ctor_get_uint8(v_format_2505_, 0);
v___y_2579_ = v___y_2588_;
v___y_2580_ = v_hardNestedFirstOperand_2589_;
goto v___jp_2578_;
}
v___jp_2590_:
{
if (v___y_2591_ == 0)
{
v___y_2588_ = v___y_2591_;
goto v___jp_2587_;
}
else
{
if (v___x_2552_ == 0)
{
goto v___jp_2576_;
}
else
{
v___y_2588_ = v___y_2591_;
goto v___jp_2587_;
}
}
}
}
else
{
lean_object* v___x_2594_; 
lean_dec(v_snd_2516_);
lean_dec(v_fst_2515_);
lean_dec(v_fst_2514_);
v___x_2594_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_2594_;
}
v___jp_2506_:
{
if (v___y_2507_ == 0)
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2508_);
return v___x_2509_;
}
else
{
lean_object* v_doc_2510_; lean_object* v___x_2511_; 
v_doc_2510_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2508_);
v___x_2511_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2510_);
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator___boxed(lean_object* v_chain_2595_, lean_object* v_format_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_2595_, v_format_2596_);
lean_dec_ref(v_format_2596_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(lean_object* v___x_2598_, lean_object* v_as_2599_, size_t v_sz_2600_, size_t v_i_2601_, lean_object* v_bs_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2598_, v_sz_2600_, v_i_2601_, v_bs_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___boxed(lean_object* v___x_2604_, lean_object* v_as_2605_, lean_object* v_sz_2606_, lean_object* v_i_2607_, lean_object* v_bs_2608_){
_start:
{
size_t v_sz_boxed_2609_; size_t v_i_boxed_2610_; lean_object* v_res_2611_; 
v_sz_boxed_2609_ = lean_unbox_usize(v_sz_2606_);
lean_dec(v_sz_2606_);
v_i_boxed_2610_ = lean_unbox_usize(v_i_2607_);
lean_dec(v_i_2607_);
v_res_2611_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(v___x_2604_, v_as_2605_, v_sz_boxed_2609_, v_i_boxed_2610_, v_bs_2608_);
lean_dec_ref(v_as_2605_);
lean_dec(v___x_2604_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object* v_lhs_2612_, lean_object* v_typeAscriptionTk_2613_, lean_object* v_rhs_2614_, lean_object* v_format_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2616_ = lean_unsigned_to_nat(3u);
v___x_2617_ = lean_mk_empty_array_with_capacity(v___x_2616_);
v___x_2618_ = lean_array_push(v___x_2617_, v_lhs_2612_);
v___x_2619_ = lean_array_push(v___x_2618_, v_typeAscriptionTk_2613_);
v___x_2620_ = lean_array_push(v___x_2619_, v_rhs_2614_);
v___x_2621_ = l_Lean_Fmt_Layouts_infixOperator(v___x_2620_, v_format_2615_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription___boxed(lean_object* v_lhs_2622_, lean_object* v_typeAscriptionTk_2623_, lean_object* v_rhs_2624_, lean_object* v_format_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Fmt_Layouts_typeAscription(v_lhs_2622_, v_typeAscriptionTk_2623_, v_rhs_2624_, v_format_2625_);
lean_dec_ref(v_format_2625_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(lean_object* v_x_2627_){
_start:
{
if (lean_obj_tag(v_x_2627_) == 0)
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_unsigned_to_nat(0u);
return v___x_2628_;
}
else
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_unsigned_to_nat(1u);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___boxed(lean_object* v_x_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(v_x_2630_);
lean_dec_ref(v_x_2630_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(lean_object* v_t_2632_, lean_object* v_k_2633_){
_start:
{
if (lean_obj_tag(v_t_2632_) == 0)
{
uint8_t v_spacing_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_spacing_2634_ = lean_ctor_get_uint8(v_t_2632_, 0);
lean_dec_ref_known(v_t_2632_, 0);
v___x_2635_ = lean_box(v_spacing_2634_);
v___x_2636_ = lean_apply_1(v_k_2633_, v___x_2635_);
return v___x_2636_;
}
else
{
lean_object* v_sep_2637_; uint8_t v_unindentedRb_2638_; uint8_t v_stickynessKind_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_sep_2637_ = lean_ctor_get(v_t_2632_, 0);
lean_inc_ref(v_sep_2637_);
v_unindentedRb_2638_ = lean_ctor_get_uint8(v_t_2632_, sizeof(void*)*1);
v_stickynessKind_2639_ = lean_ctor_get_uint8(v_t_2632_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_2632_, 1);
v___x_2640_ = lean_box(v_unindentedRb_2638_);
v___x_2641_ = lean_box(v_stickynessKind_2639_);
v___x_2642_ = lean_apply_3(v_k_2633_, v_sep_2637_, v___x_2640_, v___x_2641_);
return v___x_2642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(lean_object* v_motive_2643_, lean_object* v_ctorIdx_2644_, lean_object* v_t_2645_, lean_object* v_h_2646_, lean_object* v_k_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2645_, v_k_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___boxed(lean_object* v_motive_2649_, lean_object* v_ctorIdx_2650_, lean_object* v_t_2651_, lean_object* v_h_2652_, lean_object* v_k_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(v_motive_2649_, v_ctorIdx_2650_, v_t_2651_, v_h_2652_, v_k_2653_);
lean_dec(v_ctorIdx_2650_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim___redArg(lean_object* v_t_2655_, lean_object* v_dense_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2655_, v_dense_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim(lean_object* v_motive_2658_, lean_object* v_t_2659_, lean_object* v_h_2660_, lean_object* v_dense_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2659_, v_dense_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim___redArg(lean_object* v_t_2663_, lean_object* v_sparse_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2663_, v_sparse_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim(lean_object* v_motive_2666_, lean_object* v_t_2667_, lean_object* v_h_2668_, lean_object* v_sparse_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2667_, v_sparse_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object* v_lb_2671_, lean_object* v_rb_2672_, uint8_t v_isBodyAligned_2673_, uint8_t v_isBodyPseudoAligned_2674_, uint8_t v___x_2675_, lean_object* v_body_2676_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v_doc_2683_; 
v___x_2677_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2676_);
v___x_2678_ = lean_unsigned_to_nat(3u);
v___x_2679_ = lean_mk_empty_array_with_capacity(v___x_2678_);
v___x_2680_ = lean_array_push(v___x_2679_, v_lb_2671_);
v___x_2681_ = lean_array_push(v___x_2680_, v___x_2677_);
v___x_2682_ = lean_array_push(v___x_2681_, v_rb_2672_);
v_doc_2683_ = l_Lean_Fmt_Layouts_atomic(v___x_2682_);
lean_dec_ref(v___x_2682_);
if (v_isBodyAligned_2673_ == 0)
{
if (v_isBodyPseudoAligned_2674_ == 0)
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2683_, v___x_2675_);
return v___x_2684_;
}
else
{
lean_object* v_doc_2685_; lean_object* v___x_2686_; 
v_doc_2685_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2683_);
v___x_2686_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2685_, v___x_2675_);
return v___x_2686_;
}
}
else
{
lean_object* v_doc_2687_; lean_object* v___x_2688_; 
v_doc_2687_ = l_Lean_Fmt_TaggedDoc_aligned(v_doc_2683_);
v___x_2688_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2687_, v___x_2675_);
return v___x_2688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0___boxed(lean_object* v_lb_2689_, lean_object* v_rb_2690_, lean_object* v_isBodyAligned_2691_, lean_object* v_isBodyPseudoAligned_2692_, lean_object* v___x_2693_, lean_object* v_body_2694_){
_start:
{
uint8_t v_isBodyAligned_boxed_2695_; uint8_t v_isBodyPseudoAligned_boxed_2696_; uint8_t v___x_590__boxed_2697_; lean_object* v_res_2698_; 
v_isBodyAligned_boxed_2695_ = lean_unbox(v_isBodyAligned_2691_);
v_isBodyPseudoAligned_boxed_2696_ = lean_unbox(v_isBodyPseudoAligned_2692_);
v___x_590__boxed_2697_ = lean_unbox(v___x_2693_);
v_res_2698_ = l_Lean_Fmt_Layouts_bracketed___lam__0(v_lb_2689_, v_rb_2690_, v_isBodyAligned_boxed_2695_, v_isBodyPseudoAligned_boxed_2696_, v___x_590__boxed_2697_, v_body_2694_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object* v_lb_2702_, lean_object* v_body_2703_, lean_object* v_rb_2704_, lean_object* v_format_2705_){
_start:
{
uint8_t v___x_2706_; 
v___x_2706_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2703_);
if (v___x_2706_ == 0)
{
lean_object* v_doc_2707_; uint8_t v___x_2708_; 
v_doc_2707_ = lean_ctor_get(v_body_2703_, 0);
v___x_2708_ = 1;
if (lean_obj_tag(v_format_2705_) == 0)
{
uint8_t v_spacing_2709_; 
v_spacing_2709_ = lean_ctor_get_uint8(v_format_2705_, 0);
lean_dec_ref_known(v_format_2705_, 0);
if (v_spacing_2709_ == 0)
{
uint8_t v_isBodyAligned_2710_; uint8_t v_isBodyPseudoAligned_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v_f_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_inc(v_doc_2707_);
v_isBodyAligned_2710_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2707_);
lean_inc_ref(v_body_2703_);
v_isBodyPseudoAligned_2711_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_body_2703_);
v___x_2712_ = lean_box(v_isBodyAligned_2710_);
v___x_2713_ = lean_box(v_isBodyPseudoAligned_2711_);
v___x_2714_ = lean_box(v___x_2708_);
v_f_2715_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_bracketed___lam__0___boxed), 6, 5);
lean_closure_set(v_f_2715_, 0, v_lb_2702_);
lean_closure_set(v_f_2715_, 1, v_rb_2704_);
lean_closure_set(v_f_2715_, 2, v___x_2712_);
lean_closure_set(v_f_2715_, 3, v___x_2713_);
lean_closure_set(v_f_2715_, 4, v___x_2714_);
v___x_2716_ = ((lean_object*)(l_Lean_Fmt_Layouts_bracketed___closed__0));
v___x_2717_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_body_2703_, v_f_2715_, v___x_2716_);
return v___x_2717_;
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2718_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2703_);
v___x_2719_ = lean_unsigned_to_nat(3u);
v___x_2720_ = lean_mk_empty_array_with_capacity(v___x_2719_);
v___x_2721_ = lean_array_push(v___x_2720_, v_lb_2702_);
v___x_2722_ = lean_array_push(v___x_2721_, v___x_2718_);
v___x_2723_ = lean_array_push(v___x_2722_, v_rb_2704_);
v___x_2724_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2723_);
lean_dec_ref(v___x_2723_);
return v___x_2724_;
}
}
else
{
lean_object* v_sep_2725_; uint8_t v_unindentedRb_2726_; uint8_t v_stickynessKind_2727_; lean_object* v_sparse_2729_; lean_object* v___y_2740_; lean_object* v___y_2743_; lean_object* v___y_2755_; lean_object* v___y_2767_; lean_object* v_body_2779_; uint8_t v___x_2780_; 
v_sep_2725_ = lean_ctor_get(v_format_2705_, 0);
lean_inc_ref(v_sep_2725_);
v_unindentedRb_2726_ = lean_ctor_get_uint8(v_format_2705_, sizeof(void*)*1);
v_stickynessKind_2727_ = lean_ctor_get_uint8(v_format_2705_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_format_2705_, 1);
v_body_2779_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_2703_);
v___x_2780_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2725_);
if (v___x_2780_ == 0)
{
uint8_t v___x_2781_; 
v___x_2781_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2779_);
if (v___x_2781_ == 0)
{
lean_object* v_doc_2782_; lean_object* v_doc_2783_; uint8_t v___x_2784_; 
v_doc_2782_ = lean_ctor_get(v_sep_2725_, 0);
v_doc_2783_ = lean_ctor_get(v_body_2779_, 0);
lean_inc(v_doc_2783_);
lean_dec_ref(v_body_2779_);
v___x_2784_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2782_);
if (v___x_2784_ == 0)
{
uint8_t v___x_2785_; 
v___x_2785_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2783_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_inc(v_doc_2782_);
v___x_2786_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2782_, v_doc_2783_);
v___x_2787_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2786_);
v___y_2767_ = v___x_2787_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2788_; 
lean_dec(v_doc_2783_);
lean_inc(v_doc_2782_);
v___x_2788_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2782_);
v___y_2767_ = v___x_2788_;
goto v___jp_2766_;
}
}
else
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2783_);
v___y_2767_ = v___x_2789_;
goto v___jp_2766_;
}
}
else
{
lean_dec_ref(v_body_2779_);
lean_inc_ref(v_sep_2725_);
v___y_2767_ = v_sep_2725_;
goto v___jp_2766_;
}
}
else
{
v___y_2767_ = v_body_2779_;
goto v___jp_2766_;
}
v___jp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v_stickyVariant_2736_; lean_object* v_nonStickyVariant_2737_; lean_object* v___x_2738_; 
lean_inc_ref(v_sparse_2729_);
v___x_2730_ = l_Lean_Fmt_TaggedDoc_aligned(v_sparse_2729_);
v___x_2731_ = lean_unsigned_to_nat(2u);
v___x_2732_ = lean_mk_empty_array_with_capacity(v___x_2731_);
v___x_2733_ = lean_array_push(v___x_2732_, v_sparse_2729_);
v___x_2734_ = lean_array_push(v___x_2733_, v___x_2730_);
v___x_2735_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2734_);
v_stickyVariant_2736_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_2735_, v___x_2708_);
lean_inc_ref(v_stickyVariant_2736_);
v_nonStickyVariant_2737_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_stickyVariant_2736_);
v___x_2738_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_2737_, v_stickyVariant_2736_, v_stickynessKind_2727_);
return v___x_2738_;
}
v___jp_2739_:
{
if (v_unindentedRb_2726_ == 0)
{
v_sparse_2729_ = v___y_2740_;
goto v___jp_2728_;
}
else
{
lean_object* v_sparse_2741_; 
v_sparse_2741_ = l_Lean_Fmt_TaggedDoc_unindented(v___y_2740_, v___x_2708_);
v_sparse_2729_ = v_sparse_2741_;
goto v___jp_2728_;
}
}
v___jp_2742_:
{
uint8_t v___x_2744_; 
v___x_2744_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_2743_);
if (v___x_2744_ == 0)
{
uint8_t v___x_2745_; 
v___x_2745_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rb_2704_);
if (v___x_2745_ == 0)
{
lean_object* v_doc_2746_; lean_object* v_doc_2747_; uint8_t v___x_2748_; 
v_doc_2746_ = lean_ctor_get(v___y_2743_, 0);
lean_inc(v_doc_2746_);
lean_dec_ref(v___y_2743_);
v_doc_2747_ = lean_ctor_get(v_rb_2704_, 0);
lean_inc(v_doc_2747_);
lean_dec_ref(v_rb_2704_);
v___x_2748_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2746_);
if (v___x_2748_ == 0)
{
uint8_t v___x_2749_; 
v___x_2749_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2747_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2746_, v_doc_2747_);
v___x_2751_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2750_);
v___y_2740_ = v___x_2751_;
goto v___jp_2739_;
}
else
{
lean_object* v___x_2752_; 
lean_dec(v_doc_2747_);
v___x_2752_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2746_);
v___y_2740_ = v___x_2752_;
goto v___jp_2739_;
}
}
else
{
lean_object* v___x_2753_; 
lean_dec(v_doc_2746_);
v___x_2753_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2747_);
v___y_2740_ = v___x_2753_;
goto v___jp_2739_;
}
}
else
{
lean_dec_ref(v_rb_2704_);
v___y_2740_ = v___y_2743_;
goto v___jp_2739_;
}
}
else
{
lean_dec_ref(v___y_2743_);
v___y_2740_ = v_rb_2704_;
goto v___jp_2739_;
}
}
v___jp_2754_:
{
uint8_t v___x_2756_; 
v___x_2756_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_2755_);
if (v___x_2756_ == 0)
{
uint8_t v___x_2757_; 
v___x_2757_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2725_);
if (v___x_2757_ == 0)
{
lean_object* v_doc_2758_; lean_object* v_doc_2759_; uint8_t v___x_2760_; 
v_doc_2758_ = lean_ctor_get(v___y_2755_, 0);
lean_inc(v_doc_2758_);
lean_dec_ref(v___y_2755_);
v_doc_2759_ = lean_ctor_get(v_sep_2725_, 0);
lean_inc(v_doc_2759_);
lean_dec_ref(v_sep_2725_);
v___x_2760_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2758_);
if (v___x_2760_ == 0)
{
uint8_t v___x_2761_; 
v___x_2761_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2759_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2758_, v_doc_2759_);
v___x_2763_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2762_);
v___y_2743_ = v___x_2763_;
goto v___jp_2742_;
}
else
{
lean_object* v___x_2764_; 
lean_dec(v_doc_2759_);
v___x_2764_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2758_);
v___y_2743_ = v___x_2764_;
goto v___jp_2742_;
}
}
else
{
lean_object* v___x_2765_; 
lean_dec(v_doc_2758_);
v___x_2765_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2759_);
v___y_2743_ = v___x_2765_;
goto v___jp_2742_;
}
}
else
{
lean_dec_ref(v_sep_2725_);
v___y_2743_ = v___y_2755_;
goto v___jp_2742_;
}
}
else
{
lean_dec_ref(v___y_2755_);
v___y_2743_ = v_sep_2725_;
goto v___jp_2742_;
}
}
v___jp_2766_:
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = l_Lean_Fmt_TaggedDoc_hardNested(v___y_2767_);
v___x_2769_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_lb_2702_);
if (v___x_2769_ == 0)
{
uint8_t v___x_2770_; 
v___x_2770_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2768_);
if (v___x_2770_ == 0)
{
lean_object* v_doc_2771_; lean_object* v_doc_2772_; uint8_t v___x_2773_; 
v_doc_2771_ = lean_ctor_get(v_lb_2702_, 0);
lean_inc(v_doc_2771_);
lean_dec_ref(v_lb_2702_);
v_doc_2772_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_doc_2772_);
lean_dec_ref(v___x_2768_);
v___x_2773_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2771_);
if (v___x_2773_ == 0)
{
uint8_t v___x_2774_; 
v___x_2774_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2772_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2771_, v_doc_2772_);
v___x_2776_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2775_);
v___y_2755_ = v___x_2776_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2777_; 
lean_dec(v_doc_2772_);
v___x_2777_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2771_);
v___y_2755_ = v___x_2777_;
goto v___jp_2754_;
}
}
else
{
lean_object* v___x_2778_; 
lean_dec(v_doc_2771_);
v___x_2778_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2772_);
v___y_2755_ = v___x_2778_;
goto v___jp_2754_;
}
}
else
{
lean_dec_ref(v___x_2768_);
v___y_2755_ = v_lb_2702_;
goto v___jp_2754_;
}
}
else
{
lean_dec_ref(v_lb_2702_);
v___y_2755_ = v___x_2768_;
goto v___jp_2754_;
}
}
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec_ref(v_format_2705_);
lean_dec_ref(v_body_2703_);
v___x_2790_ = lean_unsigned_to_nat(2u);
v___x_2791_ = lean_mk_empty_array_with_capacity(v___x_2790_);
v___x_2792_ = lean_array_push(v___x_2791_, v_lb_2702_);
v___x_2793_ = lean_array_push(v___x_2792_, v_rb_2704_);
v___x_2794_ = l_Lean_Fmt_Layouts_atomic(v___x_2793_);
lean_dec_ref(v___x_2793_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object* v_lbTk_2797_, lean_object* v_body_2798_, lean_object* v_rbTk_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_2801_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2797_, v_body_2798_, v_rbTk_2799_, v___x_2800_);
return v___x_2801_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0(void){
_start:
{
uint8_t v___x_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2802_ = 1;
v___x_2803_ = 1;
v___x_2804_ = l_Lean_Fmt_TaggedDoc_break;
v___x_2805_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1, v___x_2803_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1 + 1, v___x_2802_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object* v_lbTk_2806_, lean_object* v_seq_2807_, lean_object* v_rbTk_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_obj_once(&l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0, &l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0);
v___x_2810_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2806_, v_seq_2807_, v_rbTk_2808_, v___x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(uint8_t v_isComplex_2811_, lean_object* v_subAlts_2812_){
_start:
{
if (v_isComplex_2811_ == 0)
{
uint8_t v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = 1;
v___x_2814_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_subAlts_2812_, v___x_2813_);
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_Fmt_Layouts_lines(v_subAlts_2812_);
return v___x_2815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts___boxed(lean_object* v_isComplex_2816_, lean_object* v_subAlts_2817_){
_start:
{
uint8_t v_isComplex_boxed_2818_; lean_object* v_res_2819_; 
v_isComplex_boxed_2818_ = lean_unbox(v_isComplex_2816_);
v_res_2819_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_boxed_2818_, v_subAlts_2817_);
lean_dec_ref(v_subAlts_2817_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t v_sz_2820_, size_t v_i_2821_, lean_object* v_bs_2822_){
_start:
{
uint8_t v___x_2823_; 
v___x_2823_ = lean_usize_dec_lt(v_i_2821_, v_sz_2820_);
if (v___x_2823_ == 0)
{
return v_bs_2822_;
}
else
{
lean_object* v_v_2824_; lean_object* v___x_2825_; lean_object* v_bs_x27_2826_; lean_object* v___x_2827_; size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; 
v_v_2824_ = lean_array_uget(v_bs_2822_, v_i_2821_);
v___x_2825_ = lean_unsigned_to_nat(0u);
v_bs_x27_2826_ = lean_array_uset(v_bs_2822_, v_i_2821_, v___x_2825_);
v___x_2827_ = l_Lean_Fmt_TaggedDoc_nested(v_v_2824_);
v___x_2828_ = ((size_t)1ULL);
v___x_2829_ = lean_usize_add(v_i_2821_, v___x_2828_);
v___x_2830_ = lean_array_uset(v_bs_x27_2826_, v_i_2821_, v___x_2827_);
v_i_2821_ = v___x_2829_;
v_bs_2822_ = v___x_2830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object* v_sz_2832_, lean_object* v_i_2833_, lean_object* v_bs_2834_){
_start:
{
size_t v_sz_boxed_2835_; size_t v_i_boxed_2836_; lean_object* v_res_2837_; 
v_sz_boxed_2835_ = lean_unbox_usize(v_sz_2832_);
lean_dec(v_sz_2832_);
v_i_boxed_2836_ = lean_unbox_usize(v_i_2833_);
lean_dec(v_i_2833_);
v_res_2837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_boxed_2835_, v_i_boxed_2836_, v_bs_2834_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object* v_subAlts_2838_, lean_object* v_arrowTk_2839_, lean_object* v_rhs_2840_, uint8_t v_isComplex_2841_){
_start:
{
uint8_t v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; uint8_t v___y_2885_; uint8_t v___x_2902_; 
v___x_2902_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_arrowTk_2839_);
if (v___x_2902_ == 0)
{
v___y_2885_ = v___x_2902_;
goto v___jp_2884_;
}
else
{
uint8_t v___x_2903_; 
v___x_2903_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_2840_);
v___y_2885_ = v___x_2903_;
goto v___jp_2884_;
}
v___jp_2842_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v_lhs_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v_nonStickyDoc_2861_; lean_object* v_flat_2862_; lean_object* v___x_2863_; 
v___x_2846_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_2841_, v___y_2845_);
lean_dec_ref(v___y_2845_);
v___x_2847_ = lean_unsigned_to_nat(2u);
v___x_2848_ = lean_mk_empty_array_with_capacity(v___x_2847_);
lean_inc_ref_n(v___x_2848_, 2);
v___x_2849_ = lean_array_push(v___x_2848_, v___x_2846_);
v___x_2850_ = lean_array_push(v___x_2849_, v_arrowTk_2839_);
v_lhs_2851_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2850_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_lhs_2851_);
v___x_2853_ = l_Lean_Fmt_TaggedDoc_nl;
lean_inc_ref(v___y_2844_);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___y_2844_);
lean_inc_ref(v___x_2852_);
v___x_2855_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2852_, v___x_2854_);
v___x_2856_ = lean_box(0);
lean_inc_ref(v_rhs_2840_);
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_rhs_2840_);
v___x_2858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
lean_ctor_set(v___x_2858_, 2, v___x_2856_);
v___x_2859_ = lean_array_push(v___x_2848_, v___x_2855_);
v___x_2860_ = lean_array_push(v___x_2859_, v___x_2858_);
v_nonStickyDoc_2861_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2860_);
lean_dec_ref(v___x_2860_);
lean_inc_ref(v_nonStickyDoc_2861_);
v_flat_2862_ = l_Lean_Fmt_TaggedDoc_flattened(v_nonStickyDoc_2861_);
v___x_2863_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_2840_);
if (lean_obj_tag(v___x_2863_) == 1)
{
lean_object* v_val_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2882_; 
v_val_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2882_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_val_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2882_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v_stickyVariant_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v_stickyVariant_2868_ = lean_ctor_get(v_val_2864_, 0);
v___x_2869_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v___y_2844_);
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set(v___x_2870_, 1, v___y_2844_);
v___x_2871_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2852_, v___x_2870_);
lean_inc_ref(v_stickyVariant_2868_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v_stickyVariant_2868_);
v___x_2873_ = v___x_2866_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_stickyVariant_2868_);
v___x_2873_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v_stickyDoc_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2856_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
lean_ctor_set(v___x_2874_, 2, v___x_2856_);
v___x_2875_ = lean_array_push(v___x_2848_, v___x_2871_);
v___x_2876_ = lean_array_push(v___x_2875_, v___x_2874_);
v_stickyDoc_2877_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2876_);
lean_dec_ref(v___x_2876_);
v___x_2878_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_2864_, v___y_2843_);
lean_dec(v_val_2864_);
v___x_2879_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_2861_, v_stickyDoc_2877_, v___x_2878_);
lean_dec(v___x_2878_);
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v_flat_2862_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
return v___x_2880_;
}
}
}
else
{
lean_object* v___x_2883_; 
lean_dec(v___x_2863_);
lean_dec_ref_known(v___x_2852_, 1);
lean_dec_ref(v___x_2848_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_flat_2862_);
lean_ctor_set(v___x_2883_, 1, v_nonStickyDoc_2861_);
return v___x_2883_;
}
}
v___jp_2884_:
{
if (v___y_2885_ == 0)
{
lean_object* v___x_2886_; size_t v_sz_2887_; size_t v___x_2888_; lean_object* v_subAlts_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v___x_2886_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_sz_2887_ = lean_array_size(v_subAlts_2838_);
v___x_2888_ = ((size_t)0ULL);
v_subAlts_2889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_2887_, v___x_2888_, v_subAlts_2838_);
v___x_2890_ = lean_array_get_size(v_subAlts_2889_);
v___x_2891_ = lean_unsigned_to_nat(1u);
v___x_2892_ = lean_nat_sub(v___x_2890_, v___x_2891_);
v___x_2893_ = lean_nat_dec_lt(v___x_2892_, v___x_2890_);
if (v___x_2893_ == 0)
{
lean_dec(v___x_2892_);
v___y_2843_ = v___y_2885_;
v___y_2844_ = v___x_2886_;
v___y_2845_ = v_subAlts_2889_;
goto v___jp_2842_;
}
else
{
lean_object* v_v_2894_; lean_object* v___x_2895_; lean_object* v_xs_x27_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_v_2894_ = lean_array_fget(v_subAlts_2889_, v___x_2892_);
v___x_2895_ = lean_box(0);
v_xs_x27_2896_ = lean_array_fset(v_subAlts_2889_, v___x_2892_, v___x_2895_);
v___x_2897_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2894_);
v___x_2898_ = lean_array_fset(v_xs_x27_2896_, v___x_2892_, v___x_2897_);
lean_dec(v___x_2892_);
v___y_2843_ = v___y_2885_;
v___y_2844_ = v___x_2886_;
v___y_2845_ = v___x_2898_;
goto v___jp_2842_;
}
}
else
{
lean_object* v_subAlts_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_dec_ref(v_rhs_2840_);
lean_dec_ref(v_arrowTk_2839_);
v_subAlts_2899_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_2841_, v_subAlts_2838_);
lean_dec_ref(v_subAlts_2838_);
lean_inc_ref(v_subAlts_2899_);
v___x_2900_ = l_Lean_Fmt_TaggedDoc_flattened(v_subAlts_2899_);
v___x_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
lean_ctor_set(v___x_2901_, 1, v_subAlts_2899_);
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt___boxed(lean_object* v_subAlts_2904_, lean_object* v_arrowTk_2905_, lean_object* v_rhs_2906_, lean_object* v_isComplex_2907_){
_start:
{
uint8_t v_isComplex_boxed_2908_; lean_object* v_res_2909_; 
v_isComplex_boxed_2908_ = lean_unbox(v_isComplex_2907_);
v_res_2909_ = l_Lean_Fmt_Layouts_alt(v_subAlts_2904_, v_arrowTk_2905_, v_rhs_2906_, v_isComplex_boxed_2908_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(size_t v_sz_2910_, size_t v_i_2911_, lean_object* v_bs_2912_){
_start:
{
uint8_t v___x_2913_; 
v___x_2913_ = lean_usize_dec_lt(v_i_2911_, v_sz_2910_);
if (v___x_2913_ == 0)
{
return v_bs_2912_;
}
else
{
lean_object* v_v_2914_; lean_object* v_flat_2915_; lean_object* v___x_2916_; lean_object* v_bs_x27_2917_; size_t v___x_2918_; size_t v___x_2919_; lean_object* v___x_2920_; 
v_v_2914_ = lean_array_uget_borrowed(v_bs_2912_, v_i_2911_);
v_flat_2915_ = lean_ctor_get(v_v_2914_, 0);
lean_inc_ref(v_flat_2915_);
v___x_2916_ = lean_unsigned_to_nat(0u);
v_bs_x27_2917_ = lean_array_uset(v_bs_2912_, v_i_2911_, v___x_2916_);
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = lean_usize_add(v_i_2911_, v___x_2918_);
v___x_2920_ = lean_array_uset(v_bs_x27_2917_, v_i_2911_, v_flat_2915_);
v_i_2911_ = v___x_2919_;
v_bs_2912_ = v___x_2920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object* v_sz_2922_, lean_object* v_i_2923_, lean_object* v_bs_2924_){
_start:
{
size_t v_sz_boxed_2925_; size_t v_i_boxed_2926_; lean_object* v_res_2927_; 
v_sz_boxed_2925_ = lean_unbox_usize(v_sz_2922_);
lean_dec(v_sz_2922_);
v_i_boxed_2926_ = lean_unbox_usize(v_i_2923_);
lean_dec(v_i_2923_);
v_res_2927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_boxed_2925_, v_i_boxed_2926_, v_bs_2924_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t v_sz_2928_, size_t v_i_2929_, lean_object* v_bs_2930_){
_start:
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_usize_dec_lt(v_i_2929_, v_sz_2928_);
if (v___x_2931_ == 0)
{
return v_bs_2930_;
}
else
{
lean_object* v_v_2932_; lean_object* v_nonFlat_2933_; lean_object* v___x_2934_; lean_object* v_bs_x27_2935_; size_t v___x_2936_; size_t v___x_2937_; lean_object* v___x_2938_; 
v_v_2932_ = lean_array_uget_borrowed(v_bs_2930_, v_i_2929_);
v_nonFlat_2933_ = lean_ctor_get(v_v_2932_, 1);
lean_inc_ref(v_nonFlat_2933_);
v___x_2934_ = lean_unsigned_to_nat(0u);
v_bs_x27_2935_ = lean_array_uset(v_bs_2930_, v_i_2929_, v___x_2934_);
v___x_2936_ = ((size_t)1ULL);
v___x_2937_ = lean_usize_add(v_i_2929_, v___x_2936_);
v___x_2938_ = lean_array_uset(v_bs_x27_2935_, v_i_2929_, v_nonFlat_2933_);
v_i_2929_ = v___x_2937_;
v_bs_2930_ = v___x_2938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object* v_sz_2940_, lean_object* v_i_2941_, lean_object* v_bs_2942_){
_start:
{
size_t v_sz_boxed_2943_; size_t v_i_boxed_2944_; lean_object* v_res_2945_; 
v_sz_boxed_2943_ = lean_unbox_usize(v_sz_2940_);
lean_dec(v_sz_2940_);
v_i_boxed_2944_ = lean_unbox_usize(v_i_2941_);
lean_dec(v_i_2941_);
v_res_2945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_boxed_2943_, v_i_boxed_2944_, v_bs_2942_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts(lean_object* v_alts_2946_, uint8_t v_allowFlattenedAlts_2947_){
_start:
{
size_t v_sz_2948_; size_t v___x_2949_; lean_object* v___x_2950_; lean_object* v_unflattened_2951_; 
v_sz_2948_ = lean_array_size(v_alts_2946_);
v___x_2949_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2946_);
v___x_2950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_2948_, v___x_2949_, v_alts_2946_);
v_unflattened_2951_ = l_Lean_Fmt_Layouts_lines(v___x_2950_);
lean_dec_ref(v___x_2950_);
if (v_allowFlattenedAlts_2947_ == 0)
{
lean_object* v___x_2952_; 
lean_dec_ref(v_alts_2946_);
v___x_2952_ = l_Lean_Fmt_TaggedDoc_withPosition(v_unflattened_2951_);
return v___x_2952_;
}
else
{
lean_object* v___x_2953_; lean_object* v_flattened_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_2948_, v___x_2949_, v_alts_2946_);
v_flattened_2954_ = l_Lean_Fmt_Layouts_lines(v___x_2953_);
lean_dec_ref(v___x_2953_);
v___x_2955_ = lean_unsigned_to_nat(2u);
v___x_2956_ = lean_mk_empty_array_with_capacity(v___x_2955_);
v___x_2957_ = lean_array_push(v___x_2956_, v_flattened_2954_);
v___x_2958_ = lean_array_push(v___x_2957_, v_unflattened_2951_);
v___x_2959_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2958_);
v___x_2960_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_2959_);
return v___x_2960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts___boxed(lean_object* v_alts_2961_, lean_object* v_allowFlattenedAlts_2962_){
_start:
{
uint8_t v_allowFlattenedAlts_boxed_2963_; lean_object* v_res_2964_; 
v_allowFlattenedAlts_boxed_2963_ = lean_unbox(v_allowFlattenedAlts_2962_);
v_res_2964_ = l_Lean_Fmt_Layouts_alts(v_alts_2961_, v_allowFlattenedAlts_boxed_2963_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(uint8_t v_x_2965_){
_start:
{
if (v_x_2965_ == 0)
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_unsigned_to_nat(0u);
return v___x_2966_;
}
else
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_unsigned_to_nat(1u);
return v___x_2967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___boxed(lean_object* v_x_2968_){
_start:
{
uint8_t v_x_boxed_2969_; lean_object* v_res_2970_; 
v_x_boxed_2969_ = lean_unbox(v_x_2968_);
v_res_2970_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(v_x_boxed_2969_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(lean_object* v_k_2971_){
_start:
{
lean_inc(v_k_2971_);
return v_k_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg___boxed(lean_object* v_k_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(v_k_2972_);
lean_dec(v_k_2972_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(lean_object* v_motive_2974_, lean_object* v_ctorIdx_2975_, uint8_t v_t_2976_, lean_object* v_h_2977_, lean_object* v_k_2978_){
_start:
{
lean_inc(v_k_2978_);
return v_k_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___boxed(lean_object* v_motive_2979_, lean_object* v_ctorIdx_2980_, lean_object* v_t_2981_, lean_object* v_h_2982_, lean_object* v_k_2983_){
_start:
{
uint8_t v_t_boxed_2984_; lean_object* v_res_2985_; 
v_t_boxed_2984_ = lean_unbox(v_t_2981_);
v_res_2985_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(v_motive_2979_, v_ctorIdx_2980_, v_t_boxed_2984_, v_h_2982_, v_k_2983_);
lean_dec(v_k_2983_);
lean_dec(v_ctorIdx_2980_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(lean_object* v_sticky_2986_){
_start:
{
lean_inc(v_sticky_2986_);
return v_sticky_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(v_sticky_2987_);
lean_dec(v_sticky_2987_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(lean_object* v_motive_2989_, uint8_t v_t_2990_, lean_object* v_h_2991_, lean_object* v_sticky_2992_){
_start:
{
lean_inc(v_sticky_2992_);
return v_sticky_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___boxed(lean_object* v_motive_2993_, lean_object* v_t_2994_, lean_object* v_h_2995_, lean_object* v_sticky_2996_){
_start:
{
uint8_t v_t_boxed_2997_; lean_object* v_res_2998_; 
v_t_boxed_2997_ = lean_unbox(v_t_2994_);
v_res_2998_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(v_motive_2993_, v_t_boxed_2997_, v_h_2995_, v_sticky_2996_);
lean_dec(v_sticky_2996_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_2999_){
_start:
{
lean_inc(v_nonSticky_2999_);
return v_nonSticky_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(v_nonSticky_3000_);
lean_dec(v_nonSticky_3000_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(lean_object* v_motive_3002_, uint8_t v_t_3003_, lean_object* v_h_3004_, lean_object* v_nonSticky_3005_){
_start:
{
lean_inc(v_nonSticky_3005_);
return v_nonSticky_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___boxed(lean_object* v_motive_3006_, lean_object* v_t_3007_, lean_object* v_h_3008_, lean_object* v_nonSticky_3009_){
_start:
{
uint8_t v_t_boxed_3010_; lean_object* v_res_3011_; 
v_t_boxed_3010_ = lean_unbox(v_t_3007_);
v_res_3011_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(v_motive_3006_, v_t_boxed_3010_, v_h_3008_, v_nonSticky_3009_);
lean_dec(v_nonSticky_3009_);
return v_res_3011_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3013_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
lean_ctor_set(v___x_3014_, 1, v___x_3012_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object* v_keywordTk_3015_, lean_object* v_seq_3016_, uint8_t v_format_3017_){
_start:
{
lean_object* v___x_3018_; uint8_t v___x_3019_; lean_object* v_doc_3020_; 
v___x_3018_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3019_ = 1;
v_doc_3020_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_keywordTk_3015_, v___x_3018_, v_seq_3016_, v___x_3019_);
if (v_format_3017_ == 0)
{
lean_object* v___x_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; 
lean_inc_ref(v_doc_3020_);
v___x_3021_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3020_);
v___x_3022_ = 1;
v___x_3023_ = l_Lean_Fmt_TaggedDoc_sticky(v___x_3021_, v_doc_3020_, v___x_3022_);
return v___x_3023_;
}
else
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3020_);
return v___x_3024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___boxed(lean_object* v_keywordTk_3025_, lean_object* v_seq_3026_, lean_object* v_format_3027_){
_start:
{
uint8_t v_format_boxed_3028_; lean_object* v_res_3029_; 
v_format_boxed_3028_ = lean_unbox(v_format_3027_);
v_res_3029_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_keywordTk_3025_, v_seq_3026_, v_format_boxed_3028_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(uint8_t v_x_3030_){
_start:
{
if (v_x_3030_ == 0)
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_unsigned_to_nat(0u);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_unsigned_to_nat(1u);
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___boxed(lean_object* v_x_3033_){
_start:
{
uint8_t v_x_boxed_3034_; lean_object* v_res_3035_; 
v_x_boxed_3034_ = lean_unbox(v_x_3033_);
v_res_3035_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(v_x_boxed_3034_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(lean_object* v_k_3036_){
_start:
{
lean_inc(v_k_3036_);
return v_k_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg___boxed(lean_object* v_k_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(v_k_3037_);
lean_dec(v_k_3037_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(lean_object* v_motive_3039_, lean_object* v_ctorIdx_3040_, uint8_t v_t_3041_, lean_object* v_h_3042_, lean_object* v_k_3043_){
_start:
{
lean_inc(v_k_3043_);
return v_k_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___boxed(lean_object* v_motive_3044_, lean_object* v_ctorIdx_3045_, lean_object* v_t_3046_, lean_object* v_h_3047_, lean_object* v_k_3048_){
_start:
{
uint8_t v_t_boxed_3049_; lean_object* v_res_3050_; 
v_t_boxed_3049_ = lean_unbox(v_t_3046_);
v_res_3050_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(v_motive_3044_, v_ctorIdx_3045_, v_t_boxed_3049_, v_h_3047_, v_k_3048_);
lean_dec(v_k_3048_);
lean_dec(v_ctorIdx_3045_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(lean_object* v_sticky_3051_){
_start:
{
lean_inc(v_sticky_3051_);
return v_sticky_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(v_sticky_3052_);
lean_dec(v_sticky_3052_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(lean_object* v_motive_3054_, uint8_t v_t_3055_, lean_object* v_h_3056_, lean_object* v_sticky_3057_){
_start:
{
lean_inc(v_sticky_3057_);
return v_sticky_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___boxed(lean_object* v_motive_3058_, lean_object* v_t_3059_, lean_object* v_h_3060_, lean_object* v_sticky_3061_){
_start:
{
uint8_t v_t_boxed_3062_; lean_object* v_res_3063_; 
v_t_boxed_3062_ = lean_unbox(v_t_3059_);
v_res_3063_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(v_motive_3058_, v_t_boxed_3062_, v_h_3060_, v_sticky_3061_);
lean_dec(v_sticky_3061_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3064_){
_start:
{
lean_inc(v_nonSticky_3064_);
return v_nonSticky_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(v_nonSticky_3065_);
lean_dec(v_nonSticky_3065_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(lean_object* v_motive_3067_, uint8_t v_t_3068_, lean_object* v_h_3069_, lean_object* v_nonSticky_3070_){
_start:
{
lean_inc(v_nonSticky_3070_);
return v_nonSticky_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___boxed(lean_object* v_motive_3071_, lean_object* v_t_3072_, lean_object* v_h_3073_, lean_object* v_nonSticky_3074_){
_start:
{
uint8_t v_t_boxed_3075_; lean_object* v_res_3076_; 
v_t_boxed_3075_ = lean_unbox(v_t_3072_);
v_res_3076_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(v_motive_3071_, v_t_boxed_3075_, v_h_3073_, v_nonSticky_3074_);
lean_dec(v_nonSticky_3074_);
return v_res_3076_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3078_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set(v___x_3079_, 1, v___x_3077_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object* v_keyword_3080_, lean_object* v_term_3081_, uint8_t v_format_3082_){
_start:
{
lean_object* v___y_3084_; uint8_t v___x_3099_; 
v___x_3099_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_term_3081_);
if (v___x_3099_ == 0)
{
uint8_t v___x_3100_; lean_object* v___y_3102_; uint8_t v___x_3115_; 
v___x_3100_ = 1;
lean_inc_ref(v_term_3081_);
v___x_3115_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_term_3081_, v___x_3099_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_inc_ref(v_keyword_3080_);
v___x_3116_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3080_);
v___x_3117_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_term_3081_);
v___x_3118_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3116_, v___x_3117_, v_term_3081_, v___x_3100_);
v___x_3119_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3118_);
v___y_3102_ = v___x_3119_;
goto v___jp_3101_;
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_inc_ref(v_keyword_3080_);
v___x_3120_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3080_);
v___x_3121_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v_term_3081_);
v___x_3122_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3120_, v___x_3121_, v_term_3081_, v___x_3100_);
v___y_3102_ = v___x_3122_;
goto v___jp_3101_;
}
v___jp_3101_:
{
if (v_format_3082_ == 0)
{
lean_object* v___x_3103_; 
lean_inc_ref(v_term_3081_);
v___x_3103_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_term_3081_);
if (lean_obj_tag(v___x_3103_) == 1)
{
lean_object* v_val_3104_; uint8_t v_kind_3105_; 
v_val_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_val_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v_kind_3105_ = lean_ctor_get_uint8(v_val_3104_, sizeof(void*)*1);
lean_dec(v_val_3104_);
if (v_kind_3105_ == 1)
{
v___y_3084_ = v___y_3102_;
goto v___jp_3083_;
}
else
{
if (v___x_3099_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3106_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3080_);
v___x_3107_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3108_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3106_, v___x_3107_, v_term_3081_, v___x_3100_);
v___x_3109_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3102_, v___x_3108_, v_kind_3105_);
return v___x_3109_;
}
else
{
v___y_3084_ = v___y_3102_;
goto v___jp_3083_;
}
}
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v___x_3103_);
v___x_3110_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3080_);
v___x_3111_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3112_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3110_, v___x_3111_, v_term_3081_, v___x_3100_);
v___x_3113_ = 0;
v___x_3114_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3102_, v___x_3112_, v___x_3113_);
return v___x_3114_;
}
}
else
{
lean_dec_ref(v_term_3081_);
lean_dec_ref(v_keyword_3080_);
return v___y_3102_;
}
}
}
else
{
uint8_t v___x_3123_; 
lean_dec_ref(v_term_3081_);
v___x_3123_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keyword_3080_);
if (v___x_3123_ == 0)
{
if (v_format_3082_ == 0)
{
lean_object* v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; 
lean_inc_ref(v_keyword_3080_);
v___x_3124_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3080_);
v___x_3125_ = 0;
v___x_3126_ = l_Lean_Fmt_TaggedDoc_sticky(v_keyword_3080_, v___x_3124_, v___x_3125_);
return v___x_3126_;
}
else
{
return v_keyword_3080_;
}
}
else
{
lean_object* v___x_3127_; 
lean_dec_ref(v_keyword_3080_);
v___x_3127_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3127_;
}
}
v___jp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; 
v___x_3085_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3080_);
v___x_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
v___x_3087_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3088_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3086_, v___x_3087_);
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3090_, 0, v_term_3081_);
v___x_3091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
lean_ctor_set(v___x_3091_, 2, v___x_3089_);
v___x_3092_ = lean_unsigned_to_nat(2u);
v___x_3093_ = lean_mk_empty_array_with_capacity(v___x_3092_);
v___x_3094_ = lean_array_push(v___x_3093_, v___x_3088_);
v___x_3095_ = lean_array_push(v___x_3094_, v___x_3091_);
v___x_3096_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3095_);
lean_dec_ref(v___x_3095_);
v___x_3097_ = 1;
v___x_3098_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3084_, v___x_3096_, v___x_3097_);
return v___x_3098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___boxed(lean_object* v_keyword_3128_, lean_object* v_term_3129_, lean_object* v_format_3130_){
_start:
{
uint8_t v_format_boxed_3131_; lean_object* v_res_3132_; 
v_format_boxed_3131_ = lean_unbox(v_format_3130_);
v_res_3132_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3128_, v_term_3129_, v_format_boxed_3131_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(uint8_t v_x_3133_){
_start:
{
if (v_x_3133_ == 0)
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_unsigned_to_nat(0u);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_unsigned_to_nat(1u);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___boxed(lean_object* v_x_3136_){
_start:
{
uint8_t v_x_boxed_3137_; lean_object* v_res_3138_; 
v_x_boxed_3137_ = lean_unbox(v_x_3136_);
v_res_3138_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(v_x_boxed_3137_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(lean_object* v_k_3139_){
_start:
{
lean_inc(v_k_3139_);
return v_k_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg___boxed(lean_object* v_k_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(v_k_3140_);
lean_dec(v_k_3140_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(lean_object* v_motive_3142_, lean_object* v_ctorIdx_3143_, uint8_t v_t_3144_, lean_object* v_h_3145_, lean_object* v_k_3146_){
_start:
{
lean_inc(v_k_3146_);
return v_k_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___boxed(lean_object* v_motive_3147_, lean_object* v_ctorIdx_3148_, lean_object* v_t_3149_, lean_object* v_h_3150_, lean_object* v_k_3151_){
_start:
{
uint8_t v_t_boxed_3152_; lean_object* v_res_3153_; 
v_t_boxed_3152_ = lean_unbox(v_t_3149_);
v_res_3153_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(v_motive_3147_, v_ctorIdx_3148_, v_t_boxed_3152_, v_h_3150_, v_k_3151_);
lean_dec(v_k_3151_);
lean_dec(v_ctorIdx_3148_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(lean_object* v_sticky_3154_){
_start:
{
lean_inc(v_sticky_3154_);
return v_sticky_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(v_sticky_3155_);
lean_dec(v_sticky_3155_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(lean_object* v_motive_3157_, uint8_t v_t_3158_, lean_object* v_h_3159_, lean_object* v_sticky_3160_){
_start:
{
lean_inc(v_sticky_3160_);
return v_sticky_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___boxed(lean_object* v_motive_3161_, lean_object* v_t_3162_, lean_object* v_h_3163_, lean_object* v_sticky_3164_){
_start:
{
uint8_t v_t_boxed_3165_; lean_object* v_res_3166_; 
v_t_boxed_3165_ = lean_unbox(v_t_3162_);
v_res_3166_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(v_motive_3161_, v_t_boxed_3165_, v_h_3163_, v_sticky_3164_);
lean_dec(v_sticky_3164_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3167_){
_start:
{
lean_inc(v_nonSticky_3167_);
return v_nonSticky_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(v_nonSticky_3168_);
lean_dec(v_nonSticky_3168_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(lean_object* v_motive_3170_, uint8_t v_t_3171_, lean_object* v_h_3172_, lean_object* v_nonSticky_3173_){
_start:
{
lean_inc(v_nonSticky_3173_);
return v_nonSticky_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___boxed(lean_object* v_motive_3174_, lean_object* v_t_3175_, lean_object* v_h_3176_, lean_object* v_nonSticky_3177_){
_start:
{
uint8_t v_t_boxed_3178_; lean_object* v_res_3179_; 
v_t_boxed_3178_ = lean_unbox(v_t_3175_);
v_res_3179_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(v_motive_3174_, v_t_boxed_3178_, v_h_3176_, v_nonSticky_3177_);
lean_dec(v_nonSticky_3177_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object* v_keyword_3180_, lean_object* v_alts_3181_, uint8_t v_format_3182_){
_start:
{
uint8_t v___x_3183_; lean_object* v_alts_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v_nonStickyDoc_3189_; 
v___x_3183_ = 1;
v_alts_3184_ = l_Lean_Fmt_Layouts_alts(v_alts_3181_, v___x_3183_);
v___x_3185_ = lean_unsigned_to_nat(2u);
v___x_3186_ = lean_mk_empty_array_with_capacity(v___x_3185_);
lean_inc_ref(v_keyword_3180_);
lean_inc_ref(v___x_3186_);
v___x_3187_ = lean_array_push(v___x_3186_, v_keyword_3180_);
lean_inc_ref(v_alts_3184_);
v___x_3188_ = lean_array_push(v___x_3187_, v_alts_3184_);
v_nonStickyDoc_3189_ = l_Lean_Fmt_Layouts_lines(v___x_3188_);
lean_dec_ref(v___x_3188_);
if (v_format_3182_ == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v_stickyDoc_3193_; uint8_t v___x_3194_; lean_object* v___x_3195_; 
v___x_3190_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3180_);
v___x_3191_ = lean_array_push(v___x_3186_, v___x_3190_);
v___x_3192_ = lean_array_push(v___x_3191_, v_alts_3184_);
v_stickyDoc_3193_ = l_Lean_Fmt_Layouts_lines(v___x_3192_);
lean_dec_ref(v___x_3192_);
v___x_3194_ = 0;
v___x_3195_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3189_, v_stickyDoc_3193_, v___x_3194_);
return v___x_3195_;
}
else
{
lean_dec_ref(v___x_3186_);
lean_dec_ref(v_alts_3184_);
lean_dec_ref(v_keyword_3180_);
return v_nonStickyDoc_3189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts___boxed(lean_object* v_keyword_3196_, lean_object* v_alts_3197_, lean_object* v_format_3198_){
_start:
{
uint8_t v_format_boxed_3199_; lean_object* v_res_3200_; 
v_format_boxed_3199_ = lean_unbox(v_format_3198_);
v_res_3200_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v_keyword_3196_, v_alts_3197_, v_format_boxed_3199_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(lean_object* v_x_3201_){
_start:
{
if (lean_obj_tag(v_x_3201_) == 0)
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_unsigned_to_nat(0u);
return v___x_3202_;
}
else
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_unsigned_to_nat(1u);
return v___x_3203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___boxed(lean_object* v_x_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(v_x_3204_);
lean_dec_ref(v_x_3204_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(lean_object* v_t_3206_, lean_object* v_k_3207_){
_start:
{
lean_object* v_sepArrayFormat_3208_; lean_object* v___x_3209_; 
v_sepArrayFormat_3208_ = lean_ctor_get(v_t_3206_, 0);
lean_inc_ref(v_sepArrayFormat_3208_);
lean_dec_ref(v_t_3206_);
v___x_3209_ = lean_apply_1(v_k_3207_, v_sepArrayFormat_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(lean_object* v_motive_3210_, lean_object* v_ctorIdx_3211_, lean_object* v_t_3212_, lean_object* v_h_3213_, lean_object* v_k_3214_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3212_, v_k_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___boxed(lean_object* v_motive_3216_, lean_object* v_ctorIdx_3217_, lean_object* v_t_3218_, lean_object* v_h_3219_, lean_object* v_k_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(v_motive_3216_, v_ctorIdx_3217_, v_t_3218_, v_h_3219_, v_k_3220_);
lean_dec(v_ctorIdx_3217_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim___redArg(lean_object* v_t_3222_, lean_object* v_sticky_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3222_, v_sticky_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim(lean_object* v_motive_3225_, lean_object* v_t_3226_, lean_object* v_h_3227_, lean_object* v_sticky_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3226_, v_sticky_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim___redArg(lean_object* v_t_3230_, lean_object* v_nonSticky_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3230_, v_nonSticky_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim(lean_object* v_motive_3233_, lean_object* v_t_3234_, lean_object* v_h_3235_, lean_object* v_nonSticky_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3234_, v_nonSticky_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(lean_object* v_x_3238_){
_start:
{
if (lean_obj_tag(v_x_3238_) == 0)
{
uint8_t v___x_3239_; 
v___x_3239_ = 1;
return v___x_3239_;
}
else
{
uint8_t v___x_3240_; 
v___x_3240_ = 0;
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky___boxed(lean_object* v_x_3241_){
_start:
{
uint8_t v_res_3242_; lean_object* v_r_3243_; 
v_res_3242_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_x_3241_);
lean_dec_ref(v_x_3241_);
v_r_3243_ = lean_box(v_res_3242_);
return v_r_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(lean_object* v_x_3244_){
_start:
{
lean_object* v_sepArrayFormat_3245_; 
v_sepArrayFormat_3245_ = lean_ctor_get(v_x_3244_, 0);
lean_inc_ref(v_sepArrayFormat_3245_);
return v_sepArrayFormat_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat___boxed(lean_object* v_x_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(v_x_3246_);
lean_dec_ref(v_x_3246_);
return v_res_3247_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3249_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
lean_ctor_set(v___x_3250_, 1, v___x_3248_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray(lean_object* v_sep_3251_, lean_object* v_keyword_3252_, lean_object* v_sepArray_3253_, lean_object* v_format_3254_){
_start:
{
lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___x_3293_; lean_object* v___y_3295_; uint8_t v___y_3296_; lean_object* v___y_3301_; uint8_t v___y_3302_; lean_object* v___y_3318_; lean_object* v_sepArrayFormat_3322_; 
v___x_3293_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_sepArrayFormat_3322_ = lean_ctor_get(v_format_3254_, 0);
lean_inc_ref(v_sepArrayFormat_3322_);
v___y_3318_ = v_sepArrayFormat_3322_;
goto v___jp_3317_;
v___jp_3255_:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v_nonStickyDoc_3282_; uint8_t v___x_3283_; 
lean_inc_ref(v_keyword_3252_);
v___x_3259_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3252_);
v___x_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
v___x_3261_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v___x_3260_);
v___x_3262_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3260_, v___x_3261_);
v___x_3263_ = lean_box(0);
lean_inc_ref(v___y_3256_);
lean_inc_ref(v_sep_3251_);
v___x_3264_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3251_, v___y_3258_, v___y_3256_);
lean_dec_ref(v___y_3258_);
v___x_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3263_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
lean_ctor_set(v___x_3266_, 2, v___x_3263_);
v___x_3267_ = lean_unsigned_to_nat(2u);
v___x_3268_ = lean_mk_empty_array_with_capacity(v___x_3267_);
lean_inc_ref_n(v___x_3268_, 3);
v___x_3269_ = lean_array_push(v___x_3268_, v___x_3262_);
v___x_3270_ = lean_array_push(v___x_3269_, v___x_3266_);
v___x_3271_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3270_);
lean_dec_ref(v___x_3270_);
v___x_3272_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_3273_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3260_, v___x_3272_);
v___x_3274_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3251_, v___y_3257_, v___y_3256_);
lean_dec_ref(v___y_3257_);
v___x_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
v___x_3276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3263_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
lean_ctor_set(v___x_3276_, 2, v___x_3263_);
v___x_3277_ = lean_array_push(v___x_3268_, v___x_3273_);
lean_inc_ref(v___x_3276_);
v___x_3278_ = lean_array_push(v___x_3277_, v___x_3276_);
v___x_3279_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3278_);
lean_dec_ref(v___x_3278_);
v___x_3280_ = lean_array_push(v___x_3268_, v___x_3271_);
v___x_3281_ = lean_array_push(v___x_3280_, v___x_3279_);
v_nonStickyDoc_3282_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3281_);
v___x_3283_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3254_);
lean_dec_ref(v_format_3254_);
if (v___x_3283_ == 0)
{
lean_dec_ref_known(v___x_3276_, 3);
lean_dec_ref(v___x_3268_);
lean_dec_ref(v_keyword_3252_);
return v_nonStickyDoc_3282_;
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v_stickyDoc_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; 
v___x_3284_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3252_);
v___x_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
v___x_3286_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3287_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3285_, v___x_3286_);
v___x_3288_ = lean_array_push(v___x_3268_, v___x_3287_);
v___x_3289_ = lean_array_push(v___x_3288_, v___x_3276_);
v_stickyDoc_3290_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3289_);
lean_dec_ref(v___x_3289_);
v___x_3291_ = 0;
v___x_3292_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3282_, v_stickyDoc_3290_, v___x_3291_);
return v___x_3292_;
}
}
v___jp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = lean_unsigned_to_nat(0u);
v___x_3298_ = lean_array_get(v___x_3293_, v___y_3295_, v___x_3297_);
lean_dec_ref(v___y_3295_);
v___x_3299_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3252_, v___x_3298_, v___y_3296_);
return v___x_3299_;
}
v___jp_3300_:
{
lean_object* v_sepArray_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; 
lean_inc_ref(v_sep_3251_);
v_sepArray_3303_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_3251_, v_sepArray_3253_, v___y_3302_);
v___x_3304_ = lean_array_get_size(v_sepArray_3303_);
v___x_3305_ = lean_unsigned_to_nat(1u);
v___x_3306_ = lean_nat_dec_eq(v___x_3304_, v___x_3305_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = lean_nat_dec_lt(v___x_3307_, v___x_3304_);
if (v___x_3308_ == 0)
{
lean_inc_ref(v_sepArray_3303_);
v___y_3256_ = v___y_3301_;
v___y_3257_ = v_sepArray_3303_;
v___y_3258_ = v_sepArray_3303_;
goto v___jp_3255_;
}
else
{
lean_object* v_v_3309_; lean_object* v___x_3310_; lean_object* v_xs_x27_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_v_3309_ = lean_array_fget(v_sepArray_3303_, v___x_3307_);
v___x_3310_ = lean_box(0);
lean_inc_ref(v_sepArray_3303_);
v_xs_x27_3311_ = lean_array_fset(v_sepArray_3303_, v___x_3307_, v___x_3310_);
v___x_3312_ = l_Lean_Fmt_TaggedDoc_flattened(v_v_3309_);
v___x_3313_ = lean_array_fset(v_xs_x27_3311_, v___x_3307_, v___x_3312_);
v___y_3256_ = v___y_3301_;
v___y_3257_ = v_sepArray_3303_;
v___y_3258_ = v___x_3313_;
goto v___jp_3255_;
}
}
else
{
uint8_t v___x_3314_; 
lean_dec_ref(v___y_3301_);
lean_dec_ref(v_sep_3251_);
v___x_3314_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3254_);
lean_dec_ref(v_format_3254_);
if (v___x_3314_ == 0)
{
uint8_t v___x_3315_; 
v___x_3315_ = 1;
v___y_3295_ = v_sepArray_3303_;
v___y_3296_ = v___x_3315_;
goto v___jp_3294_;
}
else
{
uint8_t v___x_3316_; 
v___x_3316_ = 0;
v___y_3295_ = v_sepArray_3303_;
v___y_3296_ = v___x_3316_;
goto v___jp_3294_;
}
}
}
v___jp_3317_:
{
switch(lean_obj_tag(v___y_3318_))
{
case 1:
{
uint8_t v_trailingSep_3319_; 
v_trailingSep_3319_ = lean_ctor_get_uint8(v___y_3318_, sizeof(void*)*1 + 1);
v___y_3301_ = v___y_3318_;
v___y_3302_ = v_trailingSep_3319_;
goto v___jp_3300_;
}
case 3:
{
uint8_t v_trailingSep_3320_; 
v_trailingSep_3320_ = lean_ctor_get_uint8(v___y_3318_, sizeof(void*)*1);
v___y_3301_ = v___y_3318_;
v___y_3302_ = v_trailingSep_3320_;
goto v___jp_3300_;
}
default: 
{
uint8_t v_trailingSep_3321_; 
v_trailingSep_3321_ = lean_ctor_get_uint8(v___y_3318_, sizeof(void*)*2);
v___y_3301_ = v___y_3318_;
v___y_3302_ = v_trailingSep_3321_;
goto v___jp_3300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___boxed(lean_object* v_sep_3323_, lean_object* v_keyword_3324_, lean_object* v_sepArray_3325_, lean_object* v_format_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3323_, v_keyword_3324_, v_sepArray_3325_, v_format_3326_);
lean_dec_ref(v_sepArray_3325_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(uint8_t v_x_3328_){
_start:
{
if (v_x_3328_ == 0)
{
lean_object* v___x_3329_; 
v___x_3329_ = lean_unsigned_to_nat(0u);
return v___x_3329_;
}
else
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_unsigned_to_nat(1u);
return v___x_3330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___boxed(lean_object* v_x_3331_){
_start:
{
uint8_t v_x_boxed_3332_; lean_object* v_res_3333_; 
v_x_boxed_3332_ = lean_unbox(v_x_3331_);
v_res_3333_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(v_x_boxed_3332_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(lean_object* v_k_3334_){
_start:
{
lean_inc(v_k_3334_);
return v_k_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg___boxed(lean_object* v_k_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(v_k_3335_);
lean_dec(v_k_3335_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(lean_object* v_motive_3337_, lean_object* v_ctorIdx_3338_, uint8_t v_t_3339_, lean_object* v_h_3340_, lean_object* v_k_3341_){
_start:
{
lean_inc(v_k_3341_);
return v_k_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___boxed(lean_object* v_motive_3342_, lean_object* v_ctorIdx_3343_, lean_object* v_t_3344_, lean_object* v_h_3345_, lean_object* v_k_3346_){
_start:
{
uint8_t v_t_boxed_3347_; lean_object* v_res_3348_; 
v_t_boxed_3347_ = lean_unbox(v_t_3344_);
v_res_3348_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(v_motive_3342_, v_ctorIdx_3343_, v_t_boxed_3347_, v_h_3345_, v_k_3346_);
lean_dec(v_k_3346_);
lean_dec(v_ctorIdx_3343_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(lean_object* v_sticky_3349_){
_start:
{
lean_inc(v_sticky_3349_);
return v_sticky_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(v_sticky_3350_);
lean_dec(v_sticky_3350_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(lean_object* v_motive_3352_, uint8_t v_t_3353_, lean_object* v_h_3354_, lean_object* v_sticky_3355_){
_start:
{
lean_inc(v_sticky_3355_);
return v_sticky_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___boxed(lean_object* v_motive_3356_, lean_object* v_t_3357_, lean_object* v_h_3358_, lean_object* v_sticky_3359_){
_start:
{
uint8_t v_t_boxed_3360_; lean_object* v_res_3361_; 
v_t_boxed_3360_ = lean_unbox(v_t_3357_);
v_res_3361_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(v_motive_3356_, v_t_boxed_3360_, v_h_3358_, v_sticky_3359_);
lean_dec(v_sticky_3359_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3362_){
_start:
{
lean_inc(v_nonSticky_3362_);
return v_nonSticky_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(v_nonSticky_3363_);
lean_dec(v_nonSticky_3363_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(lean_object* v_motive_3365_, uint8_t v_t_3366_, lean_object* v_h_3367_, lean_object* v_nonSticky_3368_){
_start:
{
lean_inc(v_nonSticky_3368_);
return v_nonSticky_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___boxed(lean_object* v_motive_3369_, lean_object* v_t_3370_, lean_object* v_h_3371_, lean_object* v_nonSticky_3372_){
_start:
{
uint8_t v_t_boxed_3373_; lean_object* v_res_3374_; 
v_t_boxed_3373_ = lean_unbox(v_t_3370_);
v_res_3374_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(v_motive_3369_, v_t_boxed_3373_, v_h_3371_, v_nonSticky_3372_);
lean_dec(v_nonSticky_3372_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object* v_sep_3379_, lean_object* v_keyword_3380_, lean_object* v_sepArray_3381_, uint8_t v_format_3382_){
_start:
{
if (v_format_3382_ == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0));
v___x_3384_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3379_, v_keyword_3380_, v_sepArray_3381_, v___x_3383_);
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1));
v___x_3386_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3379_, v_keyword_3380_, v_sepArray_3381_, v___x_3385_);
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___boxed(lean_object* v_sep_3387_, lean_object* v_keyword_3388_, lean_object* v_sepArray_3389_, lean_object* v_format_3390_){
_start:
{
uint8_t v_format_boxed_3391_; lean_object* v_res_3392_; 
v_format_boxed_3391_ = lean_unbox(v_format_3390_);
v_res_3392_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v_sep_3387_, v_keyword_3388_, v_sepArray_3389_, v_format_boxed_3391_);
lean_dec_ref(v_sepArray_3389_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(lean_object* v_format_3393_, lean_object* v_a_3394_){
_start:
{
uint8_t v_nestedRhs_3395_; 
v_nestedRhs_3395_ = lean_ctor_get_uint8(v_format_3393_, 1);
if (v_nestedRhs_3395_ == 0)
{
return v_a_3394_;
}
else
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_Fmt_TaggedDoc_nested(v_a_3394_);
return v___x_3396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed(lean_object* v_format_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(v_format_3397_, v_a_3398_);
lean_dec_ref(v_format_3397_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(lean_object* v_format_3400_){
_start:
{
uint8_t v_allowFlattening_3401_; 
v_allowFlattening_3401_ = lean_ctor_get_uint8(v_format_3400_, 0);
if (v_allowFlattening_3401_ == 0)
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Fmt_TaggedDoc_hardNl;
return v___x_3402_;
}
else
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_Fmt_TaggedDoc_nl;
return v___x_3403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep___boxed(lean_object* v_format_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3404_);
lean_dec_ref(v_format_3404_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(lean_object* v_rhs_3406_, lean_object* v_format_3407_, lean_object* v_lhs_3408_){
_start:
{
uint8_t v_allowFlattening_3409_; 
v_allowFlattening_3409_ = lean_ctor_get_uint8(v_format_3407_, 0);
if (v_allowFlattening_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3410_, 0, v_lhs_3408_);
v___x_3411_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3407_);
v___x_3412_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3412_, 0, v_format_3407_);
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___x_3414_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3410_, v___x_3413_);
v___x_3415_ = lean_box(0);
v___x_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3416_, 0, v_rhs_3406_);
v___x_3417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
lean_ctor_set(v___x_3417_, 2, v___x_3415_);
v___x_3418_ = lean_unsigned_to_nat(2u);
v___x_3419_ = lean_mk_empty_array_with_capacity(v___x_3418_);
v___x_3420_ = lean_array_push(v___x_3419_, v___x_3414_);
v___x_3421_ = lean_array_push(v___x_3420_, v___x_3417_);
v___x_3422_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3421_);
lean_dec_ref(v___x_3421_);
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3423_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3407_);
v___x_3424_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3424_, 0, v_format_3407_);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_3408_, v___x_3425_, v_rhs_3406_, v_allowFlattening_3409_);
return v___x_3426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0(lean_object* v___y_3427_){
_start:
{
lean_inc_ref(v___y_3427_);
return v___y_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0___boxed(lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_Fmt_Layouts_keywordSeparated___lam__0(v___y_3428_);
lean_dec_ref(v___y_3428_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object* v_lhs_3431_, lean_object* v_keywordTk_3432_, lean_object* v_rhs_3433_, lean_object* v_format_3434_){
_start:
{
uint8_t v___x_3435_; 
v___x_3435_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keywordTk_3432_);
if (v___x_3435_ == 0)
{
lean_object* v___f_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v_trailingKeywordLhs_3442_; lean_object* v___x_3443_; lean_object* v_leadingKeywordRhs_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___f_3436_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_3437_ = lean_unsigned_to_nat(2u);
v___x_3438_ = lean_mk_empty_array_with_capacity(v___x_3437_);
lean_inc_ref(v_lhs_3431_);
lean_inc_ref_n(v___x_3438_, 2);
v___x_3439_ = lean_array_push(v___x_3438_, v_lhs_3431_);
lean_inc_ref(v_keywordTk_3432_);
v___x_3440_ = lean_array_push(v___x_3439_, v_keywordTk_3432_);
v___x_3441_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3440_);
lean_dec_ref(v___x_3440_);
v_trailingKeywordLhs_3442_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3441_);
lean_inc_ref_n(v_format_3434_, 2);
lean_inc_ref(v_rhs_3433_);
v___x_3443_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3433_, v_format_3434_, v_keywordTk_3432_);
v_leadingKeywordRhs_3444_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3443_);
v___x_3445_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3433_, v_format_3434_, v_trailingKeywordLhs_3442_);
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_lhs_3431_);
v___x_3447_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3434_);
lean_dec_ref(v_format_3434_);
v___x_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
lean_ctor_set(v___x_3448_, 1, v___f_3436_);
v___x_3449_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3446_, v___x_3448_);
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_leadingKeywordRhs_3444_);
v___x_3452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
lean_ctor_set(v___x_3452_, 2, v___x_3450_);
v___x_3453_ = lean_array_push(v___x_3438_, v___x_3449_);
v___x_3454_ = lean_array_push(v___x_3453_, v___x_3452_);
v___x_3455_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3454_);
lean_dec_ref(v___x_3454_);
v___x_3456_ = lean_array_push(v___x_3438_, v___x_3445_);
v___x_3457_ = lean_array_push(v___x_3456_, v___x_3455_);
v___x_3458_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3457_);
v___x_3459_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3458_);
return v___x_3459_;
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec_ref(v_keywordTk_3432_);
v___x_3460_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3433_, v_format_3434_, v_lhs_3431_);
v___x_3461_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3460_);
return v___x_3461_;
}
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0(void){
_start:
{
lean_object* v___f_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___f_3462_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_3463_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v___f_3462_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(lean_object* v_terms_3465_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3466_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3467_ = lean_box(0);
v___x_3468_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v_terms_3465_);
v___x_3469_ = lean_array_pop(v_terms_3465_);
v___x_3470_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_3468_, v___x_3469_);
v___x_3471_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3470_);
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
v___x_3473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3467_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
lean_ctor_set(v___x_3473_, 2, v___x_3467_);
v___x_3474_ = lean_array_get_size(v_terms_3465_);
v___x_3475_ = lean_unsigned_to_nat(1u);
v___x_3476_ = lean_nat_sub(v___x_3474_, v___x_3475_);
v___x_3477_ = lean_array_get(v___x_3466_, v_terms_3465_, v___x_3476_);
lean_dec(v___x_3476_);
lean_dec_ref(v_terms_3465_);
v___x_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
v___x_3479_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_3480_ = l_Lean_Fmt_TaggedDoc_Component_withSepBefore(v___x_3478_, v___x_3479_);
v___x_3481_ = lean_unsigned_to_nat(2u);
v___x_3482_ = lean_mk_empty_array_with_capacity(v___x_3481_);
v___x_3483_ = lean_array_push(v___x_3482_, v___x_3473_);
v___x_3484_ = lean_array_push(v___x_3483_, v___x_3480_);
v___x_3485_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3484_);
lean_dec_ref(v___x_3484_);
return v___x_3485_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3487_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(lean_object* v_app_3488_, lean_object* v_fillableTerms_3489_, lean_object* v_terms_3490_, lean_object* v_eligibleKinds_3491_){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v_allowFill_3498_; 
v___x_3492_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3493_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3494_ = lean_array_get_size(v_fillableTerms_3489_);
v___x_3495_ = lean_unsigned_to_nat(1u);
v___x_3496_ = lean_nat_sub(v___x_3494_, v___x_3495_);
v___x_3497_ = lean_array_get_borrowed(v___x_3493_, v_fillableTerms_3489_, v___x_3496_);
lean_dec(v___x_3496_);
v_allowFill_3498_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*1);
if (v_allowFill_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_dec_ref(v_terms_3490_);
lean_dec_ref(v_app_3488_);
v___x_3499_ = lean_box(0);
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3500_ = lean_array_get_size(v_terms_3490_);
v___x_3501_ = lean_nat_sub(v___x_3500_, v___x_3495_);
v___x_3502_ = lean_array_get_borrowed(v___x_3492_, v_terms_3490_, v___x_3501_);
lean_inc(v___x_3502_);
v___x_3503_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v___x_3502_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v___x_3504_; 
lean_dec(v___x_3501_);
lean_dec_ref(v_terms_3490_);
lean_dec_ref(v_app_3488_);
v___x_3504_ = lean_box(0);
return v___x_3504_;
}
else
{
lean_object* v_val_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3526_; 
v_val_3505_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3507_ = v___x_3503_;
v_isShared_3508_ = v_isSharedCheck_3526_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_val_3505_);
lean_dec(v___x_3503_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3526_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
uint8_t v___x_3509_; uint8_t v___x_3510_; lean_object* v___y_3512_; 
v___x_3509_ = lean_unbox(v_val_3505_);
lean_dec(v_val_3505_);
v___x_3510_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_3491_, v___x_3509_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3521_; 
lean_del_object(v___x_3507_);
lean_dec(v___x_3501_);
lean_dec_ref(v_terms_3490_);
lean_dec_ref(v_app_3488_);
v___x_3521_ = lean_box(0);
return v___x_3521_;
}
else
{
lean_object* v___x_3522_; 
lean_inc(v___x_3502_);
v___x_3522_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v___x_3502_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_3524_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_3523_);
v___y_3512_ = v___x_3524_;
goto v___jp_3511_;
}
else
{
lean_object* v_val_3525_; 
v_val_3525_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_val_3525_);
lean_dec_ref_known(v___x_3522_, 1);
v___y_3512_ = v_val_3525_;
goto v___jp_3511_;
}
}
v___jp_3511_:
{
lean_object* v_stickyVariant_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
v_stickyVariant_3513_ = lean_ctor_get(v___y_3512_, 0);
lean_inc_ref(v_stickyVariant_3513_);
v___x_3514_ = lean_array_set(v_terms_3490_, v___x_3501_, v_stickyVariant_3513_);
lean_dec(v___x_3501_);
v___x_3515_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v___x_3514_);
v___x_3516_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_3512_, v___x_3510_);
lean_dec_ref(v___y_3512_);
v___x_3517_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_app_3488_, v___x_3515_, v___x_3516_);
lean_dec(v___x_3516_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3517_);
v___x_3519_ = v___x_3507_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___boxed(lean_object* v_app_3527_, lean_object* v_fillableTerms_3528_, lean_object* v_terms_3529_, lean_object* v_eligibleKinds_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3527_, v_fillableTerms_3528_, v_terms_3529_, v_eligibleKinds_3530_);
lean_dec_ref(v_eligibleKinds_3530_);
lean_dec_ref(v_fillableTerms_3528_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(lean_object* v_format_3532_, lean_object* v_app_3533_, lean_object* v_terms_3534_){
_start:
{
uint8_t v_sparse_3535_; 
v_sparse_3535_ = lean_ctor_get_uint8(v_format_3532_, 1);
if (v_sparse_3535_ == 0)
{
uint8_t v_respectPseudoAlignment_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v_respectPseudoAlignment_3536_ = lean_ctor_get_uint8(v_format_3532_, 3);
v___x_3537_ = lean_array_get_size(v_terms_3534_);
v___x_3538_ = lean_unsigned_to_nat(2u);
v___x_3539_ = lean_nat_dec_eq(v___x_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; 
lean_dec_ref(v_terms_3534_);
lean_dec_ref(v_app_3533_);
v___x_3540_ = lean_box(0);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3541_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3542_ = lean_unsigned_to_nat(1u);
v___x_3543_ = lean_nat_sub(v___x_3537_, v___x_3542_);
v___x_3544_ = lean_array_get_borrowed(v___x_3541_, v_terms_3534_, v___x_3543_);
lean_dec(v___x_3543_);
lean_inc(v___x_3544_);
v___x_3545_ = l_Lean_Fmt_Layouts_permitDenseLayout(v___x_3544_, v_respectPseudoAlignment_3536_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; 
lean_dec_ref(v_terms_3534_);
lean_dec_ref(v_app_3533_);
v___x_3546_ = lean_box(0);
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3547_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v_terms_3534_);
v___x_3548_ = lean_mk_empty_array_with_capacity(v___x_3538_);
v___x_3549_ = lean_array_push(v___x_3548_, v___x_3547_);
v___x_3550_ = lean_array_push(v___x_3549_, v_app_3533_);
v___x_3551_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3550_);
v___x_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
}
}
else
{
lean_object* v___x_3553_; 
lean_dec_ref(v_terms_3534_);
lean_dec_ref(v_app_3533_);
v___x_3553_ = lean_box(0);
return v___x_3553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f___boxed(lean_object* v_format_3554_, lean_object* v_app_3555_, lean_object* v_terms_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3554_, v_app_3555_, v_terms_3556_);
lean_dec_ref(v_format_3554_);
return v_res_3557_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0));
v___x_3560_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3559_);
return v___x_3560_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3561_; lean_object* v_lbTk_3562_; 
v___x_3561_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1);
v_lbTk_3562_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3561_);
return v_lbTk_3562_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3));
v___x_3565_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_3566_; lean_object* v_rbTk_3567_; 
v___x_3566_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4);
v_rbTk_3567_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3566_);
return v_rbTk_3567_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(lean_object* v_upperBound_3568_, lean_object* v_a_3569_, lean_object* v_b_3570_){
_start:
{
lean_object* v_a_3572_; uint8_t v___x_3576_; 
v___x_3576_ = lean_nat_dec_lt(v_a_3569_, v_upperBound_3568_);
if (v___x_3576_ == 0)
{
lean_dec(v_a_3569_);
return v_b_3570_;
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v_v_3579_; uint8_t v_allowFill_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3592_; 
v___x_3577_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3578_ = lean_array_get(v___x_3577_, v_b_3570_, v_a_3569_);
v_v_3579_ = lean_ctor_get(v___x_3578_, 0);
v_allowFill_3580_ = lean_ctor_get_uint8(v___x_3578_, sizeof(void*)*1);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3582_ = v___x_3578_;
v_isShared_3583_ = v_isSharedCheck_3592_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_v_3579_);
lean_dec(v___x_3578_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3592_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
uint8_t v___x_3584_; 
lean_inc(v_v_3579_);
v___x_3584_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_v_3579_);
if (v___x_3584_ == 0)
{
lean_del_object(v___x_3582_);
lean_dec(v_v_3579_);
v_a_3572_ = v_b_3570_;
goto v___jp_3571_;
}
else
{
lean_object* v_lbTk_3585_; lean_object* v_rbTk_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v_lbTk_3585_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2);
v_rbTk_3586_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5);
v___x_3587_ = l_Lean_Fmt_Layouts_parens(v_lbTk_3585_, v_v_3579_, v_rbTk_3586_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v___x_3587_);
v___x_3589_ = v___x_3582_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3587_);
lean_ctor_set_uint8(v_reuseFailAlloc_3591_, sizeof(void*)*1, v_allowFill_3580_);
v___x_3589_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_array_set(v_b_3570_, v_a_3569_, v___x_3589_);
v_a_3572_ = v___x_3590_;
goto v___jp_3571_;
}
}
}
}
v___jp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = lean_unsigned_to_nat(1u);
v___x_3574_ = lean_nat_add(v_a_3569_, v___x_3573_);
lean_dec(v_a_3569_);
v_a_3569_ = v___x_3574_;
v_b_3570_ = v_a_3572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___boxed(lean_object* v_upperBound_3593_, lean_object* v_a_3594_, lean_object* v_b_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3593_, v_a_3594_, v_b_3595_);
lean_dec(v_upperBound_3593_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(lean_object* v_as_3597_, size_t v_i_3598_, size_t v_stop_3599_, lean_object* v_b_3600_){
_start:
{
lean_object* v___y_3602_; uint8_t v___x_3606_; 
v___x_3606_ = lean_usize_dec_eq(v_i_3598_, v_stop_3599_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v_v_3608_; uint8_t v___x_3609_; 
v___x_3607_ = lean_array_uget_borrowed(v_as_3597_, v_i_3598_);
v_v_3608_ = lean_ctor_get(v___x_3607_, 0);
v___x_3609_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_inc(v___x_3607_);
v___x_3610_ = lean_array_push(v_b_3600_, v___x_3607_);
v___y_3602_ = v___x_3610_;
goto v___jp_3601_;
}
else
{
v___y_3602_ = v_b_3600_;
goto v___jp_3601_;
}
}
else
{
return v_b_3600_;
}
v___jp_3601_:
{
size_t v___x_3603_; size_t v___x_3604_; 
v___x_3603_ = ((size_t)1ULL);
v___x_3604_ = lean_usize_add(v_i_3598_, v___x_3603_);
v_i_3598_ = v___x_3604_;
v_b_3600_ = v___y_3602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2___boxed(lean_object* v_as_3611_, lean_object* v_i_3612_, lean_object* v_stop_3613_, lean_object* v_b_3614_){
_start:
{
size_t v_i_boxed_3615_; size_t v_stop_boxed_3616_; lean_object* v_res_3617_; 
v_i_boxed_3615_ = lean_unbox_usize(v_i_3612_);
lean_dec(v_i_3612_);
v_stop_boxed_3616_ = lean_unbox_usize(v_stop_3613_);
lean_dec(v_stop_3613_);
v_res_3617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_as_3611_, v_i_boxed_3615_, v_stop_boxed_3616_, v_b_3614_);
lean_dec_ref(v_as_3611_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(size_t v_sz_3618_, size_t v_i_3619_, lean_object* v_bs_3620_){
_start:
{
uint8_t v___x_3621_; 
v___x_3621_ = lean_usize_dec_lt(v_i_3619_, v_sz_3618_);
if (v___x_3621_ == 0)
{
return v_bs_3620_;
}
else
{
lean_object* v_v_3622_; lean_object* v_v_3623_; lean_object* v___x_3624_; lean_object* v_bs_x27_3625_; size_t v___x_3626_; size_t v___x_3627_; lean_object* v___x_3628_; 
v_v_3622_ = lean_array_uget_borrowed(v_bs_3620_, v_i_3619_);
v_v_3623_ = lean_ctor_get(v_v_3622_, 0);
lean_inc(v_v_3623_);
v___x_3624_ = lean_unsigned_to_nat(0u);
v_bs_x27_3625_ = lean_array_uset(v_bs_3620_, v_i_3619_, v___x_3624_);
v___x_3626_ = ((size_t)1ULL);
v___x_3627_ = lean_usize_add(v_i_3619_, v___x_3626_);
v___x_3628_ = lean_array_uset(v_bs_x27_3625_, v_i_3619_, v_v_3623_);
v_i_3619_ = v___x_3627_;
v_bs_3620_ = v___x_3628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0___boxed(lean_object* v_sz_3630_, lean_object* v_i_3631_, lean_object* v_bs_3632_){
_start:
{
size_t v_sz_boxed_3633_; size_t v_i_boxed_3634_; lean_object* v_res_3635_; 
v_sz_boxed_3633_ = lean_unbox_usize(v_sz_3630_);
lean_dec(v_sz_3630_);
v_i_boxed_3634_ = lean_unbox_usize(v_i_3631_);
lean_dec(v_i_3631_);
v_res_3635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_boxed_3633_, v_i_boxed_3634_, v_bs_3632_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object* v_terms_3638_, lean_object* v_format_3639_){
_start:
{
lean_object* v_app_3641_; lean_object* v_fillableTerms_3645_; lean_object* v___y_3659_; lean_object* v_fillableTerms_3660_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___y_3668_; lean_object* v___x_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v___x_3665_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3666_ = lean_unsigned_to_nat(0u);
v___x_3693_ = lean_array_get_size(v_terms_3638_);
v___x_3694_ = ((lean_object*)(l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0));
v___x_3695_ = lean_nat_dec_lt(v___x_3666_, v___x_3693_);
if (v___x_3695_ == 0)
{
v___y_3668_ = v___x_3694_;
goto v___jp_3667_;
}
else
{
uint8_t v___x_3696_; 
v___x_3696_ = lean_nat_dec_le(v___x_3693_, v___x_3693_);
if (v___x_3696_ == 0)
{
if (v___x_3695_ == 0)
{
v___y_3668_ = v___x_3694_;
goto v___jp_3667_;
}
else
{
size_t v___x_3697_; size_t v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = ((size_t)0ULL);
v___x_3698_ = lean_usize_of_nat(v___x_3693_);
v___x_3699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3638_, v___x_3697_, v___x_3698_, v___x_3694_);
v___y_3668_ = v___x_3699_;
goto v___jp_3667_;
}
}
else
{
size_t v___x_3700_; size_t v___x_3701_; lean_object* v___x_3702_; 
v___x_3700_ = ((size_t)0ULL);
v___x_3701_ = lean_usize_of_nat(v___x_3693_);
v___x_3702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3638_, v___x_3700_, v___x_3701_, v___x_3694_);
v___y_3668_ = v___x_3702_;
goto v___jp_3667_;
}
}
v___jp_3640_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = l_Lean_Fmt_TaggedDoc_nested(v_app_3641_);
v___x_3643_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3642_);
return v___x_3643_;
}
v___jp_3644_:
{
lean_object* v_app_3646_; size_t v_sz_3647_; size_t v___x_3648_; lean_object* v_terms_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_inc_ref_n(v_fillableTerms_3645_, 2);
v_app_3646_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(v_fillableTerms_3645_);
v_sz_3647_ = lean_array_size(v_fillableTerms_3645_);
v___x_3648_ = ((size_t)0ULL);
v_terms_3649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_3647_, v___x_3648_, v_fillableTerms_3645_);
v___x_3650_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
lean_inc_ref(v_terms_3649_);
lean_inc_ref(v_app_3646_);
v___x_3651_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3646_, v_fillableTerms_3645_, v_terms_3649_, v___x_3650_);
if (lean_obj_tag(v___x_3651_) == 1)
{
lean_object* v_val_3652_; 
lean_dec_ref(v_terms_3649_);
lean_dec_ref(v_app_3646_);
lean_dec_ref(v_fillableTerms_3645_);
v_val_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_val_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v_app_3641_ = v_val_3652_;
goto v___jp_3640_;
}
else
{
lean_object* v___x_3653_; 
lean_dec(v___x_3651_);
lean_inc_ref(v_terms_3649_);
lean_inc_ref(v_app_3646_);
v___x_3653_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3639_, v_app_3646_, v_terms_3649_);
if (lean_obj_tag(v___x_3653_) == 1)
{
lean_object* v_val_3654_; 
lean_dec_ref(v_terms_3649_);
lean_dec_ref(v_app_3646_);
lean_dec_ref(v_fillableTerms_3645_);
v_val_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_val_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v_app_3641_ = v_val_3654_;
goto v___jp_3640_;
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_dec(v___x_3653_);
v___x_3655_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
lean_inc_ref(v_app_3646_);
v___x_3656_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3646_, v_fillableTerms_3645_, v_terms_3649_, v___x_3655_);
lean_dec_ref(v_fillableTerms_3645_);
if (lean_obj_tag(v___x_3656_) == 1)
{
lean_object* v_val_3657_; 
lean_dec_ref(v_app_3646_);
v_val_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_val_3657_);
lean_dec_ref_known(v___x_3656_, 1);
v_app_3641_ = v_val_3657_;
goto v___jp_3640_;
}
else
{
lean_dec(v___x_3656_);
v_app_3641_ = v_app_3646_;
goto v___jp_3640_;
}
}
}
}
v___jp_3658_:
{
uint8_t v_parenthesize_3661_; 
v_parenthesize_3661_ = lean_ctor_get_uint8(v_format_3639_, 2);
if (v_parenthesize_3661_ == 0)
{
lean_dec(v___y_3659_);
v_fillableTerms_3645_ = v_fillableTerms_3660_;
goto v___jp_3644_;
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = lean_array_get_size(v_fillableTerms_3660_);
v___x_3663_ = lean_nat_sub(v___x_3662_, v___y_3659_);
v___x_3664_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v___x_3663_, v___y_3659_, v_fillableTerms_3660_);
lean_dec(v___x_3663_);
v_fillableTerms_3645_ = v___x_3664_;
goto v___jp_3644_;
}
}
v___jp_3667_:
{
lean_object* v___x_3669_; uint8_t v___x_3670_; 
v___x_3669_ = lean_array_get_size(v___y_3668_);
v___x_3670_ = lean_nat_dec_eq(v___x_3669_, v___x_3666_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; uint8_t v___x_3672_; 
v___x_3671_ = lean_unsigned_to_nat(1u);
v___x_3672_ = lean_nat_dec_eq(v___x_3669_, v___x_3671_);
if (v___x_3672_ == 0)
{
uint8_t v___x_3673_; 
v___x_3673_ = lean_nat_dec_lt(v___x_3671_, v___x_3669_);
if (v___x_3673_ == 0)
{
v___y_3659_ = v___x_3671_;
v_fillableTerms_3660_ = v___y_3668_;
goto v___jp_3658_;
}
else
{
uint8_t v_hardNestedFirstTerm_3674_; 
v_hardNestedFirstTerm_3674_ = lean_ctor_get_uint8(v_format_3639_, 0);
if (v_hardNestedFirstTerm_3674_ == 0)
{
v___y_3659_ = v___x_3671_;
v_fillableTerms_3660_ = v___y_3668_;
goto v___jp_3658_;
}
else
{
uint8_t v___x_3675_; 
v___x_3675_ = lean_nat_dec_lt(v___x_3666_, v___x_3669_);
if (v___x_3675_ == 0)
{
v___y_3659_ = v___x_3671_;
v_fillableTerms_3660_ = v___y_3668_;
goto v___jp_3658_;
}
else
{
lean_object* v_v_3676_; lean_object* v_v_3677_; uint8_t v_allowFill_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3689_; 
v_v_3676_ = lean_array_fget(v___y_3668_, v___x_3666_);
v_v_3677_ = lean_ctor_get(v_v_3676_, 0);
v_allowFill_3678_ = lean_ctor_get_uint8(v_v_3676_, sizeof(void*)*1);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_v_3676_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3680_ = v_v_3676_;
v_isShared_3681_ = v_isSharedCheck_3689_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_v_3677_);
lean_dec(v_v_3676_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3689_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v_xs_x27_3683_; lean_object* v___x_3684_; lean_object* v___x_3686_; 
v___x_3682_ = lean_box(0);
v_xs_x27_3683_ = lean_array_fset(v___y_3668_, v___x_3666_, v___x_3682_);
v___x_3684_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3677_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3684_);
v___x_3686_ = v___x_3680_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, sizeof(void*)*1, v_allowFill_3678_);
v___x_3686_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
lean_object* v___x_3687_; 
v___x_3687_ = lean_array_fset(v_xs_x27_3683_, v___x_3666_, v___x_3686_);
v___y_3659_ = v___x_3671_;
v_fillableTerms_3660_ = v___x_3687_;
goto v___jp_3658_;
}
}
}
}
}
}
else
{
lean_object* v___x_3690_; lean_object* v_v_3691_; 
v___x_3690_ = lean_array_get(v___x_3665_, v___y_3668_, v___x_3666_);
lean_dec_ref(v___y_3668_);
v_v_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_v_3691_);
lean_dec(v___x_3690_);
return v_v_3691_;
}
}
else
{
lean_object* v___x_3692_; 
lean_dec_ref(v___y_3668_);
v___x_3692_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___boxed(lean_object* v_terms_3703_, lean_object* v_format_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v_terms_3703_, v_format_3704_);
lean_dec_ref(v_format_3704_);
lean_dec_ref(v_terms_3703_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(lean_object* v_upperBound_3706_, lean_object* v_inst_3707_, lean_object* v_R_3708_, lean_object* v_a_3709_, lean_object* v_b_3710_, lean_object* v_c_3711_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3706_, v_a_3709_, v_b_3710_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___boxed(lean_object* v_upperBound_3713_, lean_object* v_inst_3714_, lean_object* v_R_3715_, lean_object* v_a_3716_, lean_object* v_b_3717_, lean_object* v_c_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(v_upperBound_3713_, v_inst_3714_, v_R_3715_, v_a_3716_, v_b_3717_, v_c_3718_);
lean_dec(v_upperBound_3713_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(size_t v_sz_3720_, size_t v_i_3721_, lean_object* v_bs_3722_){
_start:
{
uint8_t v___x_3723_; 
v___x_3723_ = lean_usize_dec_lt(v_i_3721_, v_sz_3720_);
if (v___x_3723_ == 0)
{
return v_bs_3722_;
}
else
{
lean_object* v_v_3724_; lean_object* v___x_3725_; lean_object* v_bs_x27_3726_; lean_object* v___x_3727_; size_t v___x_3728_; size_t v___x_3729_; lean_object* v___x_3730_; 
v_v_3724_ = lean_array_uget(v_bs_3722_, v_i_3721_);
v___x_3725_ = lean_unsigned_to_nat(0u);
v_bs_x27_3726_ = lean_array_uset(v_bs_3722_, v_i_3721_, v___x_3725_);
v___x_3727_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3727_, 0, v_v_3724_);
lean_ctor_set_uint8(v___x_3727_, sizeof(void*)*1, v___x_3723_);
v___x_3728_ = ((size_t)1ULL);
v___x_3729_ = lean_usize_add(v_i_3721_, v___x_3728_);
v___x_3730_ = lean_array_uset(v_bs_x27_3726_, v_i_3721_, v___x_3727_);
v_i_3721_ = v___x_3729_;
v_bs_3722_ = v___x_3730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0___boxed(lean_object* v_sz_3732_, lean_object* v_i_3733_, lean_object* v_bs_3734_){
_start:
{
size_t v_sz_boxed_3735_; size_t v_i_boxed_3736_; lean_object* v_res_3737_; 
v_sz_boxed_3735_ = lean_unbox_usize(v_sz_3732_);
lean_dec(v_sz_3732_);
v_i_boxed_3736_ = lean_unbox_usize(v_i_3733_);
lean_dec(v_i_3733_);
v_res_3737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_boxed_3735_, v_i_boxed_3736_, v_bs_3734_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application(lean_object* v_terms_3738_, lean_object* v_format_3739_){
_start:
{
size_t v_sz_3740_; size_t v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v_sz_3740_ = lean_array_size(v_terms_3738_);
v___x_3741_ = ((size_t)0ULL);
v___x_3742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_3740_, v___x_3741_, v_terms_3738_);
v___x_3743_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v___x_3742_, v_format_3739_);
lean_dec_ref(v___x_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application___boxed(lean_object* v_terms_3744_, lean_object* v_format_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_Fmt_Layouts_application(v_terms_3744_, v_format_3745_);
lean_dec_ref(v_format_3745_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(lean_object* v_f_3747_){
_start:
{
uint8_t v_hardNestedFirstTerm_3748_; uint8_t v_sparse_3749_; uint8_t v_parenthesize_3750_; uint8_t v_respectPseudoAlignment_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
v_hardNestedFirstTerm_3748_ = lean_ctor_get_uint8(v_f_3747_, 0);
v_sparse_3749_ = lean_ctor_get_uint8(v_f_3747_, 1);
v_parenthesize_3750_ = lean_ctor_get_uint8(v_f_3747_, 2);
v_respectPseudoAlignment_3751_ = lean_ctor_get_uint8(v_f_3747_, 3);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_f_3747_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v_f_3747_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_dec(v_f_3747_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, 0, v_hardNestedFirstTerm_3748_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, 1, v_sparse_3749_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, 2, v_parenthesize_3750_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, 3, v_respectPseudoAlignment_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object* v_terms_3759_, lean_object* v_format_3760_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(v_format_3760_);
v___x_3762_ = l_Lean_Fmt_Layouts_application(v_terms_3759_, v___x_3761_);
lean_dec_ref(v___x_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(lean_object* v_x_3763_){
_start:
{
if (lean_obj_tag(v_x_3763_) == 0)
{
lean_object* v___x_3764_; 
v___x_3764_ = lean_unsigned_to_nat(0u);
return v___x_3764_;
}
else
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_unsigned_to_nat(1u);
return v___x_3765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___boxed(lean_object* v_x_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(v_x_3766_);
lean_dec_ref(v_x_3766_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(lean_object* v_t_3768_, lean_object* v_k_3769_){
_start:
{
lean_object* v_doc_3770_; lean_object* v___x_3771_; 
v_doc_3770_ = lean_ctor_get(v_t_3768_, 0);
lean_inc_ref(v_doc_3770_);
lean_dec_ref(v_t_3768_);
v___x_3771_ = lean_apply_1(v_k_3769_, v_doc_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(lean_object* v_motive_3772_, lean_object* v_ctorIdx_3773_, lean_object* v_t_3774_, lean_object* v_h_3775_, lean_object* v_k_3776_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3774_, v_k_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___boxed(lean_object* v_motive_3778_, lean_object* v_ctorIdx_3779_, lean_object* v_t_3780_, lean_object* v_h_3781_, lean_object* v_k_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(v_motive_3778_, v_ctorIdx_3779_, v_t_3780_, v_h_3781_, v_k_3782_);
lean_dec(v_ctorIdx_3779_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim___redArg(lean_object* v_t_3784_, lean_object* v_sep_3785_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3784_, v_sep_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim(lean_object* v_motive_3787_, lean_object* v_t_3788_, lean_object* v_h_3789_, lean_object* v_sep_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3788_, v_sep_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim___redArg(lean_object* v_t_3792_, lean_object* v_elems_3793_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3792_, v_elems_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim(lean_object* v_motive_3795_, lean_object* v_t_3796_, lean_object* v_h_3797_, lean_object* v_elems_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3796_, v_elems_3798_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(size_t v_sz_3800_, size_t v_i_3801_, lean_object* v_bs_3802_){
_start:
{
uint8_t v___x_3803_; 
v___x_3803_ = lean_usize_dec_lt(v_i_3801_, v_sz_3800_);
if (v___x_3803_ == 0)
{
return v_bs_3802_;
}
else
{
lean_object* v_v_3804_; lean_object* v___x_3805_; lean_object* v_bs_x27_3806_; lean_object* v___y_3808_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_v_3804_ = lean_array_uget(v_bs_3802_, v_i_3801_);
v___x_3805_ = lean_unsigned_to_nat(0u);
v_bs_x27_3806_ = lean_array_uset(v_bs_3802_, v_i_3801_, v___x_3805_);
v___x_3813_ = lean_usize_to_nat(v_i_3801_);
v___x_3814_ = lean_unsigned_to_nat(2u);
v___x_3815_ = lean_nat_mod(v___x_3813_, v___x_3814_);
lean_dec(v___x_3813_);
v___x_3816_ = lean_nat_dec_eq(v___x_3815_, v___x_3805_);
lean_dec(v___x_3815_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; 
v___x_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3817_, 0, v_v_3804_);
v___y_3808_ = v___x_3817_;
goto v___jp_3807_;
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3818_ = lean_unsigned_to_nat(1u);
v___x_3819_ = lean_mk_empty_array_with_capacity(v___x_3818_);
v___x_3820_ = lean_array_push(v___x_3819_, v_v_3804_);
v___x_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
v___y_3808_ = v___x_3821_;
goto v___jp_3807_;
}
v___jp_3807_:
{
size_t v___x_3809_; size_t v___x_3810_; lean_object* v___x_3811_; 
v___x_3809_ = ((size_t)1ULL);
v___x_3810_ = lean_usize_add(v_i_3801_, v___x_3809_);
v___x_3811_ = lean_array_uset(v_bs_x27_3806_, v_i_3801_, v___y_3808_);
v_i_3801_ = v___x_3810_;
v_bs_3802_ = v___x_3811_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg___boxed(lean_object* v_sz_3822_, lean_object* v_i_3823_, lean_object* v_bs_3824_){
_start:
{
size_t v_sz_boxed_3825_; size_t v_i_boxed_3826_; lean_object* v_res_3827_; 
v_sz_boxed_3825_ = lean_unbox_usize(v_sz_3822_);
lean_dec(v_sz_3822_);
v_i_boxed_3826_ = lean_unbox_usize(v_i_3823_);
lean_dec(v_i_3823_);
v_res_3827_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_boxed_3825_, v_i_boxed_3826_, v_bs_3824_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object* v_elems_3828_){
_start:
{
size_t v_sz_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v_sz_3829_ = lean_array_size(v_elems_3828_);
v___x_3830_ = ((size_t)0ULL);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3829_, v___x_3830_, v_elems_3828_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(lean_object* v_s_3832_, lean_object* v_elems_3833_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_elems_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___boxed(lean_object* v_s_3835_, lean_object* v_elems_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(v_s_3835_, v_elems_3836_);
lean_dec_ref(v_s_3835_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(lean_object* v_as_3838_, size_t v_sz_3839_, size_t v_i_3840_, lean_object* v_bs_3841_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3839_, v_i_3840_, v_bs_3841_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___boxed(lean_object* v_as_3843_, lean_object* v_sz_3844_, lean_object* v_i_3845_, lean_object* v_bs_3846_){
_start:
{
size_t v_sz_boxed_3847_; size_t v_i_boxed_3848_; lean_object* v_res_3849_; 
v_sz_boxed_3847_ = lean_unbox_usize(v_sz_3844_);
lean_dec(v_sz_3844_);
v_i_boxed_3848_ = lean_unbox_usize(v_i_3845_);
lean_dec(v_i_3845_);
v_res_3849_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(v_as_3843_, v_sz_boxed_3847_, v_i_boxed_3848_, v_bs_3846_);
lean_dec_ref(v_as_3843_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(size_t v_sz_3852_, size_t v_i_3853_, lean_object* v_bs_3854_){
_start:
{
uint8_t v___x_3855_; 
v___x_3855_ = lean_usize_dec_lt(v_i_3853_, v_sz_3852_);
if (v___x_3855_ == 0)
{
return v_bs_3854_;
}
else
{
lean_object* v_v_3856_; lean_object* v___x_3857_; lean_object* v_bs_x27_3858_; lean_object* v___y_3860_; 
v_v_3856_ = lean_array_uget(v_bs_3854_, v_i_3853_);
v___x_3857_ = lean_unsigned_to_nat(0u);
v_bs_x27_3858_ = lean_array_uset(v_bs_3854_, v_i_3853_, v___x_3857_);
if (lean_obj_tag(v_v_3856_) == 0)
{
v___y_3860_ = v_v_3856_;
goto v___jp_3859_;
}
else
{
lean_object* v_docs_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3887_; 
v_docs_3865_ = lean_ctor_get(v_v_3856_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_v_3856_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3867_ = v_v_3856_;
v_isShared_3868_ = v_isSharedCheck_3887_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_docs_3865_);
lean_dec(v_v_3856_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3887_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; uint8_t v___x_3871_; 
v___x_3869_ = lean_array_get_size(v_docs_3865_);
v___x_3870_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_3871_ = lean_nat_dec_lt(v___x_3857_, v___x_3869_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; 
lean_del_object(v___x_3867_);
lean_dec_ref(v_docs_3865_);
v___x_3872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_3860_ = v___x_3872_;
goto v___jp_3859_;
}
else
{
uint8_t v___x_3873_; 
v___x_3873_ = lean_nat_dec_le(v___x_3869_, v___x_3869_);
if (v___x_3873_ == 0)
{
if (v___x_3871_ == 0)
{
lean_object* v___x_3874_; 
lean_del_object(v___x_3867_);
lean_dec_ref(v_docs_3865_);
v___x_3874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_3860_ = v___x_3874_;
goto v___jp_3859_;
}
else
{
size_t v___x_3875_; size_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3875_ = ((size_t)0ULL);
v___x_3876_ = lean_usize_of_nat(v___x_3869_);
v___x_3877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_docs_3865_, v___x_3875_, v___x_3876_, v___x_3870_);
lean_dec_ref(v_docs_3865_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 0, v___x_3877_);
v___x_3879_ = v___x_3867_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
v___y_3860_ = v___x_3879_;
goto v___jp_3859_;
}
}
}
else
{
size_t v___x_3881_; size_t v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3885_; 
v___x_3881_ = ((size_t)0ULL);
v___x_3882_ = lean_usize_of_nat(v___x_3869_);
v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_docs_3865_, v___x_3881_, v___x_3882_, v___x_3870_);
lean_dec_ref(v_docs_3865_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 0, v___x_3883_);
v___x_3885_ = v___x_3867_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
v___y_3860_ = v___x_3885_;
goto v___jp_3859_;
}
}
}
}
}
v___jp_3859_:
{
size_t v___x_3861_; size_t v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = ((size_t)1ULL);
v___x_3862_ = lean_usize_add(v_i_3853_, v___x_3861_);
v___x_3863_ = lean_array_uset(v_bs_x27_3858_, v_i_3853_, v___y_3860_);
v_i_3853_ = v___x_3862_;
v_bs_3854_ = v___x_3863_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___boxed(lean_object* v_sz_3888_, lean_object* v_i_3889_, lean_object* v_bs_3890_){
_start:
{
size_t v_sz_boxed_3891_; size_t v_i_boxed_3892_; lean_object* v_res_3893_; 
v_sz_boxed_3891_ = lean_unbox_usize(v_sz_3888_);
lean_dec(v_sz_3888_);
v_i_boxed_3892_ = lean_unbox_usize(v_i_3889_);
lean_dec(v_i_3889_);
v_res_3893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_boxed_3891_, v_i_boxed_3892_, v_bs_3890_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(lean_object* v_as_3894_, lean_object* v_j_3895_){
_start:
{
lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3900_ = lean_array_get_size(v_as_3894_);
v___x_3901_ = lean_nat_dec_lt(v_j_3895_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; 
lean_dec(v_j_3895_);
v___x_3902_ = lean_box(0);
return v___x_3902_;
}
else
{
lean_object* v___x_3903_; 
v___x_3903_ = lean_array_fget(v_as_3894_, v_j_3895_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_dec_ref_known(v___x_3903_, 1);
goto v___jp_3896_;
}
else
{
lean_object* v_docs_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3914_; 
v_docs_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3914_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_docs_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3914_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v___x_3908_ = lean_array_get_size(v_docs_3904_);
lean_dec_ref(v_docs_3904_);
v___x_3909_ = lean_unsigned_to_nat(0u);
v___x_3910_ = lean_nat_dec_eq(v___x_3908_, v___x_3909_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3912_; 
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v_j_3895_);
v___x_3912_ = v___x_3906_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_j_3895_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
else
{
lean_del_object(v___x_3906_);
goto v___jp_3896_;
}
}
}
}
v___jp_3896_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_unsigned_to_nat(1u);
v___x_3898_ = lean_nat_add(v_j_3895_, v___x_3897_);
lean_dec(v_j_3895_);
v_j_3895_ = v___x_3898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2___boxed(lean_object* v_as_3915_, lean_object* v_j_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_as_3915_, v_j_3916_);
lean_dec_ref(v_as_3915_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(size_t v_sz_3918_, size_t v_i_3919_, lean_object* v_bs_3920_){
_start:
{
uint8_t v___x_3921_; 
v___x_3921_ = lean_usize_dec_lt(v_i_3919_, v_sz_3918_);
if (v___x_3921_ == 0)
{
return v_bs_3920_;
}
else
{
lean_object* v_v_3922_; lean_object* v___x_3923_; lean_object* v_bs_x27_3924_; lean_object* v___y_3926_; 
v_v_3922_ = lean_array_uget(v_bs_3920_, v_i_3919_);
v___x_3923_ = lean_unsigned_to_nat(0u);
v_bs_x27_3924_ = lean_array_uset(v_bs_3920_, v_i_3919_, v___x_3923_);
if (lean_obj_tag(v_v_3922_) == 0)
{
lean_object* v_doc_3931_; 
v_doc_3931_ = lean_ctor_get(v_v_3922_, 0);
lean_inc_ref(v_doc_3931_);
lean_dec_ref_known(v_v_3922_, 1);
v___y_3926_ = v_doc_3931_;
goto v___jp_3925_;
}
else
{
lean_object* v_docs_3932_; lean_object* v___x_3933_; 
v_docs_3932_ = lean_ctor_get(v_v_3922_, 0);
lean_inc_ref(v_docs_3932_);
lean_dec_ref_known(v_v_3922_, 1);
v___x_3933_ = l_Lean_Fmt_Layouts_fill(v_docs_3932_);
lean_dec_ref(v_docs_3932_);
v___y_3926_ = v___x_3933_;
goto v___jp_3925_;
}
v___jp_3925_:
{
size_t v___x_3927_; size_t v___x_3928_; lean_object* v___x_3929_; 
v___x_3927_ = ((size_t)1ULL);
v___x_3928_ = lean_usize_add(v_i_3919_, v___x_3927_);
v___x_3929_ = lean_array_uset(v_bs_x27_3924_, v_i_3919_, v___y_3926_);
v_i_3919_ = v___x_3928_;
v_bs_3920_ = v___x_3929_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0___boxed(lean_object* v_sz_3934_, lean_object* v_i_3935_, lean_object* v_bs_3936_){
_start:
{
size_t v_sz_boxed_3937_; size_t v_i_boxed_3938_; lean_object* v_res_3939_; 
v_sz_boxed_3937_ = lean_unbox_usize(v_sz_3934_);
lean_dec(v_sz_3934_);
v_i_boxed_3938_ = lean_unbox_usize(v_i_3935_);
lean_dec(v_i_3935_);
v_res_3939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_boxed_3937_, v_i_boxed_3938_, v_bs_3936_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object* v_lb_3941_, lean_object* v_terms_3942_, lean_object* v_rb_3943_){
_start:
{
lean_object* v_terms_3945_; size_t v_sz_3953_; size_t v___x_3954_; lean_object* v_terms_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v_sz_3953_ = lean_array_size(v_terms_3942_);
v___x_3954_ = ((size_t)0ULL);
v_terms_3955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_3953_, v___x_3954_, v_terms_3942_);
v___x_3956_ = lean_unsigned_to_nat(1u);
v___x_3957_ = lean_array_get_size(v_terms_3955_);
v___x_3958_ = lean_nat_dec_lt(v___x_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
v_terms_3945_ = v_terms_3955_;
goto v___jp_3944_;
}
else
{
lean_object* v___x_3959_; lean_object* v_firstElemsIdx_x3f_3960_; 
v___x_3959_ = lean_unsigned_to_nat(0u);
v_firstElemsIdx_x3f_3960_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_terms_3955_, v___x_3959_);
if (lean_obj_tag(v_firstElemsIdx_x3f_3960_) == 1)
{
lean_object* v_val_3961_; uint8_t v___x_3962_; 
v_val_3961_ = lean_ctor_get(v_firstElemsIdx_x3f_3960_, 0);
lean_inc(v_val_3961_);
lean_dec_ref_known(v_firstElemsIdx_x3f_3960_, 1);
v___x_3962_ = lean_nat_dec_lt(v_val_3961_, v___x_3957_);
if (v___x_3962_ == 0)
{
lean_dec(v_val_3961_);
v_terms_3945_ = v_terms_3955_;
goto v___jp_3944_;
}
else
{
lean_object* v_v_3963_; lean_object* v___x_3964_; lean_object* v_xs_x27_3965_; lean_object* v___y_3967_; 
v_v_3963_ = lean_array_fget(v_terms_3955_, v_val_3961_);
v___x_3964_ = lean_box(0);
v_xs_x27_3965_ = lean_array_fset(v_terms_3955_, v_val_3961_, v___x_3964_);
if (lean_obj_tag(v_v_3963_) == 0)
{
v___y_3967_ = v_v_3963_;
goto v___jp_3966_;
}
else
{
lean_object* v_docs_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
v_docs_3969_ = lean_ctor_get(v_v_3963_, 0);
v___x_3970_ = lean_array_get_size(v_docs_3969_);
v___x_3971_ = lean_nat_dec_lt(v___x_3959_, v___x_3970_);
if (v___x_3971_ == 0)
{
v___y_3967_ = v_v_3963_;
goto v___jp_3966_;
}
else
{
lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3982_; 
lean_inc_ref(v_docs_3969_);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_v_3963_);
if (v_isSharedCheck_3982_ == 0)
{
lean_object* v_unused_3983_; 
v_unused_3983_ = lean_ctor_get(v_v_3963_, 0);
lean_dec(v_unused_3983_);
v___x_3973_ = v_v_3963_;
v_isShared_3974_ = v_isSharedCheck_3982_;
goto v_resetjp_3972_;
}
else
{
lean_dec(v_v_3963_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3982_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v_v_3975_; lean_object* v_xs_x27_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3980_; 
v_v_3975_ = lean_array_fget(v_docs_3969_, v___x_3959_);
v_xs_x27_3976_ = lean_array_fset(v_docs_3969_, v___x_3959_, v___x_3964_);
v___x_3977_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3975_);
v___x_3978_ = lean_array_fset(v_xs_x27_3976_, v___x_3959_, v___x_3977_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3978_);
v___x_3980_ = v___x_3973_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
v___y_3967_ = v___x_3980_;
goto v___jp_3966_;
}
}
}
}
v___jp_3966_:
{
lean_object* v___x_3968_; 
v___x_3968_ = lean_array_fset(v_xs_x27_3965_, v_val_3961_, v___y_3967_);
lean_dec(v_val_3961_);
v_terms_3945_ = v___x_3968_;
goto v___jp_3944_;
}
}
}
else
{
lean_dec(v_firstElemsIdx_x3f_3960_);
v_terms_3945_ = v_terms_3955_;
goto v___jp_3944_;
}
}
v___jp_3944_:
{
lean_object* v___x_3946_; size_t v_sz_3947_; size_t v___x_3948_; lean_object* v_terms_x27_3949_; lean_object* v_terms_x27_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3946_ = ((lean_object*)(l_Lean_Fmt_Layouts_metaApplication___closed__0));
v_sz_3947_ = lean_array_size(v_terms_3945_);
v___x_3948_ = ((size_t)0ULL);
v_terms_x27_3949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_3947_, v___x_3948_, v_terms_3945_);
v_terms_x27_3950_ = l_Lean_Fmt_Layouts_sepFill(v___x_3946_, v_terms_x27_3949_);
lean_dec_ref(v_terms_x27_3949_);
v___x_3951_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_3952_ = l_Lean_Fmt_Layouts_bracketed(v_lb_3941_, v_terms_x27_3950_, v_rb_3943_, v___x_3951_);
return v___x_3952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object* v_chain_3986_){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3987_ = ((lean_object*)(l_Lean_Fmt_Layouts_pipeOperator___closed__0));
v___x_3988_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_3986_, v___x_3987_);
return v___x_3988_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0(void){
_start:
{
uint8_t v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = 1;
v___x_3990_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3991_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set_uint8(v___x_3991_, sizeof(void*)*1, v___x_3989_);
return v___x_3991_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default(void){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_obj_once(&l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0, &l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0);
return v___x_3992_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock(void){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0(lean_object* v_block_3994_){
_start:
{
uint8_t v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = 1;
v___x_3996_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3996_, 0, v_block_3994_);
lean_ctor_set_uint8(v___x_3996_, sizeof(void*)*1, v___x_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(lean_object* v_val_3999_, uint8_t v___x_4000_, lean_object* v___x_4001_, lean_object* v_____r_4002_, lean_object* v_stickyAcc_4003_){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_3999_, v___x_4000_);
v___x_4005_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v___x_4001_, v_stickyAcc_4003_, v___x_4004_);
lean_dec(v___x_4004_);
v___x_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1___boxed(lean_object* v_val_4007_, lean_object* v___x_4008_, lean_object* v___x_4009_, lean_object* v_____r_4010_, lean_object* v_stickyAcc_4011_){
_start:
{
uint8_t v___x_1444__boxed_4012_; lean_object* v_res_4013_; 
v___x_1444__boxed_4012_ = lean_unbox(v___x_4008_);
v_res_4013_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4007_, v___x_1444__boxed_4012_, v___x_4009_, v_____r_4010_, v_stickyAcc_4011_);
lean_dec_ref(v_val_4007_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(lean_object* v_upperBound_4014_, lean_object* v___y_4015_, lean_object* v___x_4016_, lean_object* v_a_4017_, lean_object* v_b_4018_){
_start:
{
uint8_t v___x_4019_; 
v___x_4019_ = lean_nat_dec_lt(v_a_4017_, v_upperBound_4014_);
if (v___x_4019_ == 0)
{
lean_dec(v_a_4017_);
return v_b_4018_;
}
else
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v_block_4022_; uint8_t v_hardNestedIfFirst_4023_; lean_object* v___x_4024_; lean_object* v_a_4026_; lean_object* v___y_4030_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4020_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4021_ = lean_array_get_borrowed(v___x_4020_, v___y_4015_, v_a_4017_);
v_block_4022_ = lean_ctor_get(v___x_4021_, 0);
v_hardNestedIfFirst_4023_ = lean_ctor_get_uint8(v___x_4021_, sizeof(void*)*1);
v___x_4024_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_b_4018_);
v___x_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4033_, 0, v_b_4018_);
v___x_4034_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_4035_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4033_, v___x_4034_);
v___x_4036_ = lean_box(0);
lean_inc_ref_n(v_block_4022_, 2);
v___x_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4037_, 0, v_block_4022_);
v___x_4038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4036_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
lean_ctor_set(v___x_4038_, 2, v___x_4036_);
v___x_4039_ = lean_unsigned_to_nat(2u);
v___x_4040_ = lean_mk_empty_array_with_capacity(v___x_4039_);
lean_inc_ref(v___x_4040_);
v___x_4041_ = lean_array_push(v___x_4040_, v___x_4035_);
v___x_4042_ = lean_array_push(v___x_4041_, v___x_4038_);
v___x_4043_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4042_);
lean_dec_ref(v___x_4042_);
v___x_4044_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4043_);
v___x_4045_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_block_4022_);
if (lean_obj_tag(v___x_4045_) == 1)
{
lean_object* v_val_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4070_; 
v_val_4046_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4048_ = v___x_4045_;
v_isShared_4049_ = v_isSharedCheck_4070_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_val_4046_);
lean_dec(v___x_4045_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4070_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v_stickyVariant_4050_; lean_object* v___x_4051_; lean_object* v___x_4053_; 
v_stickyVariant_4050_ = lean_ctor_get(v_val_4046_, 0);
v___x_4051_ = l_Lean_Fmt_TaggedDoc_flattened(v_b_4018_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v___x_4051_);
v___x_4053_ = v___x_4048_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4051_);
v___x_4053_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4055_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4053_, v___x_4054_);
lean_inc_ref(v_stickyVariant_4050_);
v___x_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4056_, 0, v_stickyVariant_4050_);
v___x_4057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4036_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
lean_ctor_set(v___x_4057_, 2, v___x_4036_);
v___x_4058_ = lean_array_push(v___x_4040_, v___x_4055_);
v___x_4059_ = lean_array_push(v___x_4058_, v___x_4057_);
v___x_4060_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4059_);
lean_dec_ref(v___x_4059_);
if (v_hardNestedIfFirst_4023_ == 0)
{
goto v___jp_4061_;
}
else
{
lean_object* v___x_4064_; uint8_t v___x_4065_; 
v___x_4064_ = lean_nat_sub(v___x_4016_, v___x_4024_);
v___x_4065_ = lean_nat_dec_lt(v_a_4017_, v___x_4064_);
lean_dec(v___x_4064_);
if (v___x_4065_ == 0)
{
goto v___jp_4061_;
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_4060_);
v___x_4067_ = lean_box(0);
v___x_4068_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4046_, v___x_4019_, v___x_4044_, v___x_4067_, v___x_4066_);
lean_dec(v_val_4046_);
v___y_4030_ = v___x_4068_;
goto v___jp_4029_;
}
}
v___jp_4061_:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4062_ = lean_box(0);
v___x_4063_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4046_, v___x_4019_, v___x_4044_, v___x_4062_, v___x_4060_);
lean_dec(v_val_4046_);
v___y_4030_ = v___x_4063_;
goto v___jp_4029_;
}
}
}
}
else
{
lean_dec(v___x_4045_);
lean_dec_ref(v___x_4040_);
lean_dec_ref(v_b_4018_);
v_a_4026_ = v___x_4044_;
goto v___jp_4025_;
}
v___jp_4025_:
{
lean_object* v___x_4027_; 
v___x_4027_ = lean_nat_add(v_a_4017_, v___x_4024_);
lean_dec(v_a_4017_);
v_a_4017_ = v___x_4027_;
v_b_4018_ = v_a_4026_;
goto _start;
}
v___jp_4029_:
{
if (lean_obj_tag(v___y_4030_) == 0)
{
lean_object* v_a_4031_; 
lean_dec(v_a_4017_);
v_a_4031_ = lean_ctor_get(v___y_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___y_4030_, 1);
return v_a_4031_;
}
else
{
lean_object* v_a_4032_; 
v_a_4032_ = lean_ctor_get(v___y_4030_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___y_4030_, 1);
v_a_4026_ = v_a_4032_;
goto v___jp_4025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___boxed(lean_object* v_upperBound_4071_, lean_object* v___y_4072_, lean_object* v___x_4073_, lean_object* v_a_4074_, lean_object* v_b_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4071_, v___y_4072_, v___x_4073_, v_a_4074_, v_b_4075_);
lean_dec(v___x_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v_upperBound_4071_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(lean_object* v_as_4077_, size_t v_i_4078_, size_t v_stop_4079_, lean_object* v_b_4080_){
_start:
{
lean_object* v___y_4082_; uint8_t v___x_4086_; 
v___x_4086_ = lean_usize_dec_eq(v_i_4078_, v_stop_4079_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; lean_object* v_block_4088_; uint8_t v___x_4089_; 
v___x_4087_ = lean_array_uget_borrowed(v_as_4077_, v_i_4078_);
v_block_4088_ = lean_ctor_get(v___x_4087_, 0);
v___x_4089_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_block_4088_);
if (v___x_4089_ == 0)
{
lean_object* v___x_4090_; 
lean_inc(v___x_4087_);
v___x_4090_ = lean_array_push(v_b_4080_, v___x_4087_);
v___y_4082_ = v___x_4090_;
goto v___jp_4081_;
}
else
{
v___y_4082_ = v_b_4080_;
goto v___jp_4081_;
}
}
else
{
return v_b_4080_;
}
v___jp_4081_:
{
size_t v___x_4083_; size_t v___x_4084_; 
v___x_4083_ = ((size_t)1ULL);
v___x_4084_ = lean_usize_add(v_i_4078_, v___x_4083_);
v_i_4078_ = v___x_4084_;
v_b_4080_ = v___y_4082_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1___boxed(lean_object* v_as_4091_, lean_object* v_i_4092_, lean_object* v_stop_4093_, lean_object* v_b_4094_){
_start:
{
size_t v_i_boxed_4095_; size_t v_stop_boxed_4096_; lean_object* v_res_4097_; 
v_i_boxed_4095_ = lean_unbox_usize(v_i_4092_);
lean_dec(v_i_4092_);
v_stop_boxed_4096_ = lean_unbox_usize(v_stop_4093_);
lean_dec(v_stop_4093_);
v_res_4097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_as_4091_, v_i_boxed_4095_, v_stop_boxed_4096_, v_b_4094_);
lean_dec_ref(v_as_4091_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks(lean_object* v_blocks_4100_, uint8_t v_format_4101_){
_start:
{
lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___y_4112_; lean_object* v___x_4122_; lean_object* v___x_4123_; uint8_t v___x_4124_; 
v___x_4109_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4110_ = lean_unsigned_to_nat(0u);
v___x_4122_ = lean_array_get_size(v_blocks_4100_);
v___x_4123_ = ((lean_object*)(l_Lean_Fmt_Layouts_blocks___closed__0));
v___x_4124_ = lean_nat_dec_lt(v___x_4110_, v___x_4122_);
if (v___x_4124_ == 0)
{
v___y_4112_ = v___x_4123_;
goto v___jp_4111_;
}
else
{
uint8_t v___x_4125_; 
v___x_4125_ = lean_nat_dec_le(v___x_4122_, v___x_4122_);
if (v___x_4125_ == 0)
{
if (v___x_4124_ == 0)
{
v___y_4112_ = v___x_4123_;
goto v___jp_4111_;
}
else
{
size_t v___x_4126_; size_t v___x_4127_; lean_object* v___x_4128_; 
v___x_4126_ = ((size_t)0ULL);
v___x_4127_ = lean_usize_of_nat(v___x_4122_);
v___x_4128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4100_, v___x_4126_, v___x_4127_, v___x_4123_);
v___y_4112_ = v___x_4128_;
goto v___jp_4111_;
}
}
else
{
size_t v___x_4129_; size_t v___x_4130_; lean_object* v___x_4131_; 
v___x_4129_ = ((size_t)0ULL);
v___x_4130_ = lean_usize_of_nat(v___x_4122_);
v___x_4131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4100_, v___x_4129_, v___x_4130_, v___x_4123_);
v___y_4112_ = v___x_4131_;
goto v___jp_4111_;
}
}
v___jp_4102_:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v___y_4105_, v___y_4104_, v___y_4105_, v___y_4103_, v___y_4106_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4105_);
if (v_format_4101_ == 0)
{
return v___x_4107_;
}
else
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4107_);
return v___x_4108_;
}
}
v___jp_4111_:
{
lean_object* v___x_4113_; uint8_t v___x_4114_; 
v___x_4113_ = lean_array_get_size(v___y_4112_);
v___x_4114_ = lean_nat_dec_eq(v___x_4113_, v___x_4110_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4115_; lean_object* v_block_4116_; uint8_t v_hardNestedIfFirst_4117_; lean_object* v___x_4118_; uint8_t v___x_4119_; 
v___x_4115_ = lean_array_get_borrowed(v___x_4109_, v___y_4112_, v___x_4110_);
v_block_4116_ = lean_ctor_get(v___x_4115_, 0);
v_hardNestedIfFirst_4117_ = lean_ctor_get_uint8(v___x_4115_, sizeof(void*)*1);
v___x_4118_ = lean_unsigned_to_nat(1u);
v___x_4119_ = lean_nat_dec_eq(v___x_4113_, v___x_4118_);
if (v___x_4119_ == 0)
{
if (v_hardNestedIfFirst_4117_ == 0)
{
lean_inc_ref(v_block_4116_);
v___y_4103_ = v___x_4118_;
v___y_4104_ = v___y_4112_;
v___y_4105_ = v___x_4113_;
v___y_4106_ = v_block_4116_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4120_; 
lean_inc_ref(v_block_4116_);
v___x_4120_ = l_Lean_Fmt_TaggedDoc_hardNested(v_block_4116_);
v___y_4103_ = v___x_4118_;
v___y_4104_ = v___y_4112_;
v___y_4105_ = v___x_4113_;
v___y_4106_ = v___x_4120_;
goto v___jp_4102_;
}
}
else
{
lean_inc_ref(v_block_4116_);
lean_dec_ref(v___y_4112_);
return v_block_4116_;
}
}
else
{
lean_object* v___x_4121_; 
lean_dec_ref(v___y_4112_);
v___x_4121_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_4121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks___boxed(lean_object* v_blocks_4132_, lean_object* v_format_4133_){
_start:
{
uint8_t v_format_boxed_4134_; lean_object* v_res_4135_; 
v_format_boxed_4134_ = lean_unbox(v_format_4133_);
v_res_4135_ = l_Lean_Fmt_Layouts_blocks(v_blocks_4132_, v_format_boxed_4134_);
lean_dec_ref(v_blocks_4132_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(lean_object* v_upperBound_4136_, lean_object* v___y_4137_, lean_object* v___x_4138_, lean_object* v_inst_4139_, lean_object* v_R_4140_, lean_object* v_a_4141_, lean_object* v_b_4142_, lean_object* v_c_4143_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4136_, v___y_4137_, v___x_4138_, v_a_4141_, v_b_4142_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___boxed(lean_object* v_upperBound_4145_, lean_object* v___y_4146_, lean_object* v___x_4147_, lean_object* v_inst_4148_, lean_object* v_R_4149_, lean_object* v_a_4150_, lean_object* v_b_4151_, lean_object* v_c_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(v_upperBound_4145_, v___y_4146_, v___x_4147_, v_inst_4148_, v_R_4149_, v_a_4150_, v_b_4151_, v_c_4152_);
lean_dec(v___x_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v_upperBound_4145_);
return v_res_4153_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_tuple___closed__0(void){
_start:
{
uint8_t v___x_4154_; uint8_t v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4154_ = 0;
v___x_4155_ = 1;
v___x_4156_ = l_Lean_Fmt_TaggedDoc_break;
v___x_4157_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
lean_ctor_set_uint8(v___x_4157_, sizeof(void*)*1, v___x_4155_);
lean_ctor_set_uint8(v___x_4157_, sizeof(void*)*1 + 1, v___x_4154_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple(lean_object* v_sep_4158_, lean_object* v_lb_4159_, lean_object* v_fields_4160_, lean_object* v_rb_4161_){
_start:
{
uint8_t v___x_4162_; lean_object* v_fields_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; uint8_t v___x_4166_; 
v___x_4162_ = 1;
lean_inc_ref(v_sep_4158_);
v_fields_4163_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4158_, v_fields_4160_, v___x_4162_);
v___x_4164_ = lean_array_get_size(v_fields_4163_);
v___x_4165_ = lean_unsigned_to_nat(1u);
v___x_4166_ = lean_nat_dec_eq(v___x_4164_, v___x_4165_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; lean_object* v_fields_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4167_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v_fields_4168_ = l_Lean_Fmt_Layouts_sepArray(v_sep_4158_, v_fields_4163_, v___x_4167_);
lean_dec_ref(v_fields_4163_);
v___x_4169_ = lean_obj_once(&l_Lean_Fmt_Layouts_tuple___closed__0, &l_Lean_Fmt_Layouts_tuple___closed__0_once, _init_l_Lean_Fmt_Layouts_tuple___closed__0);
v___x_4170_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4159_, v_fields_4168_, v_rb_4161_, v___x_4169_);
return v___x_4170_;
}
else
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_dec_ref(v_sep_4158_);
v___x_4171_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4172_ = lean_unsigned_to_nat(0u);
v___x_4173_ = lean_array_get(v___x_4171_, v_fields_4163_, v___x_4172_);
lean_dec_ref(v_fields_4163_);
v___x_4174_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_4175_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4159_, v___x_4173_, v_rb_4161_, v___x_4174_);
return v___x_4175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple___boxed(lean_object* v_sep_4176_, lean_object* v_lb_4177_, lean_object* v_fields_4178_, lean_object* v_rb_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_Fmt_Layouts_tuple(v_sep_4176_, v_lb_4177_, v_fields_4178_, v_rb_4179_);
lean_dec_ref(v_fields_4178_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection(lean_object* v_sep_4181_, lean_object* v_lb_4182_, lean_object* v_elems_4183_, lean_object* v_rb_4184_, lean_object* v_format_4185_){
_start:
{
uint8_t v_spacing_4186_; uint8_t v_unindentedRb_4187_; uint8_t v___x_4188_; lean_object* v_elems_4189_; lean_object* v___y_4191_; 
v_spacing_4186_ = lean_ctor_get_uint8(v_format_4185_, 0);
v_unindentedRb_4187_ = lean_ctor_get_uint8(v_format_4185_, 1);
v___x_4188_ = 1;
lean_inc_ref(v_sep_4181_);
v_elems_4189_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4181_, v_elems_4183_, v___x_4188_);
if (v_spacing_4186_ == 0)
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_Fmt_TaggedDoc_break;
v___y_4191_ = v___x_4196_;
goto v___jp_4190_;
}
else
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4191_ = v___x_4197_;
goto v___jp_4190_;
}
v___jp_4190_:
{
lean_object* v_fields_4192_; uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v_fields_4192_ = l_Lean_Fmt_Layouts_sepFill(v_sep_4181_, v_elems_4189_);
lean_dec_ref(v_elems_4189_);
v___x_4193_ = 1;
lean_inc_ref(v___y_4191_);
v___x_4194_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4194_, 0, v___y_4191_);
lean_ctor_set_uint8(v___x_4194_, sizeof(void*)*1, v_unindentedRb_4187_);
lean_ctor_set_uint8(v___x_4194_, sizeof(void*)*1 + 1, v___x_4193_);
v___x_4195_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4182_, v_fields_4192_, v_rb_4184_, v___x_4194_);
return v___x_4195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection___boxed(lean_object* v_sep_4198_, lean_object* v_lb_4199_, lean_object* v_elems_4200_, lean_object* v_rb_4201_, lean_object* v_format_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_Fmt_Layouts_collection(v_sep_4198_, v_lb_4199_, v_elems_4200_, v_rb_4201_, v_format_4202_);
lean_dec_ref(v_format_4202_);
lean_dec_ref(v_elems_4200_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0(lean_object* v_keyword_4204_, lean_object* v_collection_4205_){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4206_ = lean_unsigned_to_nat(2u);
v___x_4207_ = lean_mk_empty_array_with_capacity(v___x_4206_);
v___x_4208_ = lean_array_push(v___x_4207_, v_keyword_4204_);
v___x_4209_ = lean_array_push(v___x_4208_, v_collection_4205_);
v___x_4210_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4209_);
lean_dec_ref(v___x_4209_);
v___x_4211_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object* v_sep_4212_, lean_object* v_keyword_4213_, lean_object* v_lb_4214_, lean_object* v_elems_4215_, lean_object* v_rb_4216_, lean_object* v_format_4217_){
_start:
{
lean_object* v___f_4218_; lean_object* v_collection_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___f_4218_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0), 2, 1);
lean_closure_set(v___f_4218_, 0, v_keyword_4213_);
v_collection_4219_ = l_Lean_Fmt_Layouts_collection(v_sep_4212_, v_lb_4214_, v_elems_4215_, v_rb_4216_, v_format_4217_);
v___x_4220_ = lean_box(0);
v___x_4221_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_collection_4219_, v___f_4218_, v___x_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___boxed(lean_object* v_sep_4222_, lean_object* v_keyword_4223_, lean_object* v_lb_4224_, lean_object* v_elems_4225_, lean_object* v_rb_4226_, lean_object* v_format_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_Fmt_Layouts_keywordPrefixedCollection(v_sep_4222_, v_keyword_4223_, v_lb_4224_, v_elems_4225_, v_rb_4226_, v_format_4227_);
lean_dec_ref(v_format_4227_);
lean_dec_ref(v_elems_4225_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(lean_object* v_x_4229_){
_start:
{
if (lean_obj_tag(v_x_4229_) == 0)
{
lean_object* v___x_4230_; 
v___x_4230_ = lean_unsigned_to_nat(0u);
return v___x_4230_;
}
else
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_unsigned_to_nat(1u);
return v___x_4231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___boxed(lean_object* v_x_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(v_x_4232_);
lean_dec(v_x_4232_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object* v_t_4234_, lean_object* v_k_4235_){
_start:
{
if (lean_obj_tag(v_t_4234_) == 0)
{
uint8_t v_respectPseudoAlignment_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v_respectPseudoAlignment_4236_ = lean_ctor_get_uint8(v_t_4234_, 0);
v___x_4237_ = lean_box(v_respectPseudoAlignment_4236_);
v___x_4238_ = lean_apply_1(v_k_4235_, v___x_4237_);
return v___x_4238_;
}
else
{
return v_k_4235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object* v_t_4239_, lean_object* v_k_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4239_, v_k_4240_);
lean_dec(v_t_4239_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object* v_motive_4242_, lean_object* v_ctorIdx_4243_, lean_object* v_t_4244_, lean_object* v_h_4245_, lean_object* v_k_4246_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4244_, v_k_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object* v_motive_4248_, lean_object* v_ctorIdx_4249_, lean_object* v_t_4250_, lean_object* v_h_4251_, lean_object* v_k_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(v_motive_4248_, v_ctorIdx_4249_, v_t_4250_, v_h_4251_, v_k_4252_);
lean_dec(v_t_4250_);
lean_dec(v_ctorIdx_4249_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object* v_t_4254_, lean_object* v_local_4255_){
_start:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4254_, v_local_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object* v_t_4257_, lean_object* v_local_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(v_t_4257_, v_local_4258_);
lean_dec(v_t_4257_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object* v_motive_4260_, lean_object* v_t_4261_, lean_object* v_h_4262_, lean_object* v_local_4263_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4261_, v_local_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object* v_motive_4265_, lean_object* v_t_4266_, lean_object* v_h_4267_, lean_object* v_local_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(v_motive_4265_, v_t_4266_, v_h_4267_, v_local_4268_);
lean_dec(v_t_4266_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object* v_t_4270_, lean_object* v_global_4271_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4270_, v_global_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object* v_t_4273_, lean_object* v_global_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(v_t_4273_, v_global_4274_);
lean_dec(v_t_4273_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object* v_motive_4276_, lean_object* v_t_4277_, lean_object* v_h_4278_, lean_object* v_global_4279_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4277_, v_global_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object* v_motive_4281_, lean_object* v_t_4282_, lean_object* v_h_4283_, lean_object* v_global_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(v_motive_4281_, v_t_4282_, v_h_4283_, v_global_4284_);
lean_dec(v_t_4282_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(lean_object* v_as_4286_, size_t v_i_4287_, size_t v_stop_4288_, lean_object* v_b_4289_){
_start:
{
lean_object* v___y_4291_; uint8_t v___x_4295_; 
v___x_4295_ = lean_usize_dec_eq(v_i_4287_, v_stop_4288_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; uint8_t v___x_4297_; 
v___x_4296_ = lean_array_uget_borrowed(v_as_4286_, v_i_4287_);
v___x_4297_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_4296_);
if (v___x_4297_ == 0)
{
lean_object* v___x_4298_; 
lean_inc(v___x_4296_);
v___x_4298_ = lean_array_push(v_b_4289_, v___x_4296_);
v___y_4291_ = v___x_4298_;
goto v___jp_4290_;
}
else
{
v___y_4291_ = v_b_4289_;
goto v___jp_4290_;
}
}
else
{
return v_b_4289_;
}
v___jp_4290_:
{
size_t v___x_4292_; size_t v___x_4293_; lean_object* v___x_4294_; 
v___x_4292_ = ((size_t)1ULL);
v___x_4293_ = lean_usize_add(v_i_4287_, v___x_4292_);
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_as_4286_, v___x_4293_, v_stop_4288_, v___y_4291_);
return v___x_4294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object* v_as_4299_, lean_object* v_i_4300_, lean_object* v_stop_4301_, lean_object* v_b_4302_){
_start:
{
size_t v_i_boxed_4303_; size_t v_stop_boxed_4304_; lean_object* v_res_4305_; 
v_i_boxed_4303_ = lean_unbox_usize(v_i_4300_);
lean_dec(v_i_4300_);
v_stop_boxed_4304_ = lean_unbox_usize(v_stop_4301_);
lean_dec(v_stop_4301_);
v_res_4305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_as_4299_, v_i_boxed_4303_, v_stop_boxed_4304_, v_b_4302_);
lean_dec_ref(v_as_4299_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(size_t v_sz_4306_, size_t v_i_4307_, lean_object* v_bs_4308_){
_start:
{
uint8_t v___x_4309_; 
v___x_4309_ = lean_usize_dec_lt(v_i_4307_, v_sz_4306_);
if (v___x_4309_ == 0)
{
return v_bs_4308_;
}
else
{
lean_object* v_v_4310_; lean_object* v___x_4311_; lean_object* v_bs_x27_4312_; lean_object* v___x_4313_; size_t v___x_4314_; size_t v___x_4315_; lean_object* v___x_4316_; 
v_v_4310_ = lean_array_uget(v_bs_4308_, v_i_4307_);
v___x_4311_ = lean_unsigned_to_nat(0u);
v_bs_x27_4312_ = lean_array_uset(v_bs_4308_, v_i_4307_, v___x_4311_);
v___x_4313_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(v_v_4310_);
v___x_4314_ = ((size_t)1ULL);
v___x_4315_ = lean_usize_add(v_i_4307_, v___x_4314_);
v___x_4316_ = lean_array_uset(v_bs_x27_4312_, v_i_4307_, v___x_4313_);
v_i_4307_ = v___x_4315_;
v_bs_4308_ = v___x_4316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3___boxed(lean_object* v_sz_4318_, lean_object* v_i_4319_, lean_object* v_bs_4320_){
_start:
{
size_t v_sz_boxed_4321_; size_t v_i_boxed_4322_; lean_object* v_res_4323_; 
v_sz_boxed_4321_ = lean_unbox_usize(v_sz_4318_);
lean_dec(v_sz_4318_);
v_i_boxed_4322_ = lean_unbox_usize(v_i_4319_);
lean_dec(v_i_4319_);
v_res_4323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(v_sz_boxed_4321_, v_i_boxed_4322_, v_bs_4320_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(lean_object* v_as_4324_, size_t v_i_4325_, size_t v_stop_4326_, lean_object* v_b_4327_){
_start:
{
lean_object* v___y_4329_; uint8_t v___x_4333_; 
v___x_4333_ = lean_usize_dec_eq(v_i_4325_, v_stop_4326_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; lean_object* v___y_4336_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; uint8_t v___x_4343_; 
v___x_4334_ = lean_unsigned_to_nat(0u);
v___x_4340_ = lean_array_uget_borrowed(v_as_4324_, v_i_4325_);
v___x_4341_ = lean_array_get_size(v___x_4340_);
v___x_4342_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4343_ = lean_nat_dec_lt(v___x_4334_, v___x_4341_);
if (v___x_4343_ == 0)
{
v___y_4336_ = v___x_4342_;
goto v___jp_4335_;
}
else
{
uint8_t v___x_4344_; 
v___x_4344_ = lean_nat_dec_le(v___x_4341_, v___x_4341_);
if (v___x_4344_ == 0)
{
if (v___x_4343_ == 0)
{
v___y_4336_ = v___x_4342_;
goto v___jp_4335_;
}
else
{
size_t v___x_4345_; size_t v___x_4346_; lean_object* v___x_4347_; 
v___x_4345_ = ((size_t)0ULL);
v___x_4346_ = lean_usize_of_nat(v___x_4341_);
v___x_4347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v___x_4340_, v___x_4345_, v___x_4346_, v___x_4342_);
v___y_4336_ = v___x_4347_;
goto v___jp_4335_;
}
}
else
{
size_t v___x_4348_; size_t v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = ((size_t)0ULL);
v___x_4349_ = lean_usize_of_nat(v___x_4341_);
v___x_4350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v___x_4340_, v___x_4348_, v___x_4349_, v___x_4342_);
v___y_4336_ = v___x_4350_;
goto v___jp_4335_;
}
}
v___jp_4335_:
{
lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4337_ = lean_array_get_size(v___y_4336_);
v___x_4338_ = lean_nat_dec_eq(v___x_4337_, v___x_4334_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; 
v___x_4339_ = lean_array_push(v_b_4327_, v___y_4336_);
v___y_4329_ = v___x_4339_;
goto v___jp_4328_;
}
else
{
lean_dec_ref(v___y_4336_);
v___y_4329_ = v_b_4327_;
goto v___jp_4328_;
}
}
}
else
{
return v_b_4327_;
}
v___jp_4328_:
{
size_t v___x_4330_; size_t v___x_4331_; 
v___x_4330_ = ((size_t)1ULL);
v___x_4331_ = lean_usize_add(v_i_4325_, v___x_4330_);
v_i_4325_ = v___x_4331_;
v_b_4327_ = v___y_4329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1___boxed(lean_object* v_as_4351_, lean_object* v_i_4352_, lean_object* v_stop_4353_, lean_object* v_b_4354_){
_start:
{
size_t v_i_boxed_4355_; size_t v_stop_boxed_4356_; lean_object* v_res_4357_; 
v_i_boxed_4355_ = lean_unbox_usize(v_i_4352_);
lean_dec(v_i_4352_);
v_stop_boxed_4356_ = lean_unbox_usize(v_stop_4353_);
lean_dec(v_stop_4353_);
v_res_4357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4351_, v_i_boxed_4355_, v_stop_boxed_4356_, v_b_4354_);
lean_dec_ref(v_as_4351_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(lean_object* v_as_4360_, lean_object* v_start_4361_, lean_object* v_stop_4362_){
_start:
{
lean_object* v___x_4363_; uint8_t v___x_4364_; 
v___x_4363_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0));
v___x_4364_ = lean_nat_dec_lt(v_start_4361_, v_stop_4362_);
if (v___x_4364_ == 0)
{
return v___x_4363_;
}
else
{
lean_object* v___x_4365_; uint8_t v___x_4366_; 
v___x_4365_ = lean_array_get_size(v_as_4360_);
v___x_4366_ = lean_nat_dec_le(v_stop_4362_, v___x_4365_);
if (v___x_4366_ == 0)
{
uint8_t v___x_4367_; 
v___x_4367_ = lean_nat_dec_lt(v_start_4361_, v___x_4365_);
if (v___x_4367_ == 0)
{
return v___x_4363_;
}
else
{
size_t v___x_4368_; size_t v___x_4369_; lean_object* v___x_4370_; 
v___x_4368_ = lean_usize_of_nat(v_start_4361_);
v___x_4369_ = lean_usize_of_nat(v___x_4365_);
v___x_4370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4360_, v___x_4368_, v___x_4369_, v___x_4363_);
return v___x_4370_;
}
}
else
{
size_t v___x_4371_; size_t v___x_4372_; lean_object* v___x_4373_; 
v___x_4371_ = lean_usize_of_nat(v_start_4361_);
v___x_4372_ = lean_usize_of_nat(v_stop_4362_);
v___x_4373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__1(v_as_4360_, v___x_4371_, v___x_4372_, v___x_4363_);
return v___x_4373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___boxed(lean_object* v_as_4374_, lean_object* v_start_4375_, lean_object* v_stop_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v_as_4374_, v_start_4375_, v_stop_4376_);
lean_dec(v_stop_4376_);
lean_dec(v_start_4375_);
lean_dec_ref(v_as_4374_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(lean_object* v_as_4378_, size_t v_i_4379_, size_t v_stop_4380_, lean_object* v_b_4381_){
_start:
{
lean_object* v___y_4383_; uint8_t v___x_4387_; 
v___x_4387_ = lean_usize_dec_eq(v_i_4379_, v_stop_4380_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v_group_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v___x_4388_ = lean_unsigned_to_nat(0u);
v___x_4389_ = lean_array_uget_borrowed(v_as_4378_, v_i_4379_);
v___x_4390_ = lean_array_get_size(v___x_4389_);
v_group_4391_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v___x_4389_, v___x_4388_, v___x_4390_);
v___x_4392_ = lean_array_get_size(v_group_4391_);
v___x_4393_ = lean_nat_dec_eq(v___x_4392_, v___x_4388_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4394_; 
v___x_4394_ = lean_array_push(v_b_4381_, v_group_4391_);
v___y_4383_ = v___x_4394_;
goto v___jp_4382_;
}
else
{
lean_dec_ref(v_group_4391_);
v___y_4383_ = v_b_4381_;
goto v___jp_4382_;
}
}
else
{
return v_b_4381_;
}
v___jp_4382_:
{
size_t v___x_4384_; size_t v___x_4385_; 
v___x_4384_ = ((size_t)1ULL);
v___x_4385_ = lean_usize_add(v_i_4379_, v___x_4384_);
v_i_4379_ = v___x_4385_;
v_b_4381_ = v___y_4383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3___boxed(lean_object* v_as_4395_, lean_object* v_i_4396_, lean_object* v_stop_4397_, lean_object* v_b_4398_){
_start:
{
size_t v_i_boxed_4399_; size_t v_stop_boxed_4400_; lean_object* v_res_4401_; 
v_i_boxed_4399_ = lean_unbox_usize(v_i_4396_);
lean_dec(v_i_4396_);
v_stop_boxed_4400_ = lean_unbox_usize(v_stop_4397_);
lean_dec(v_stop_4397_);
v_res_4401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4395_, v_i_boxed_4399_, v_stop_boxed_4400_, v_b_4398_);
lean_dec_ref(v_as_4395_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(lean_object* v_as_4404_, lean_object* v_start_4405_, lean_object* v_stop_4406_){
_start:
{
lean_object* v___x_4407_; uint8_t v___x_4408_; 
v___x_4407_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___closed__0));
v___x_4408_ = lean_nat_dec_lt(v_start_4405_, v_stop_4406_);
if (v___x_4408_ == 0)
{
return v___x_4407_;
}
else
{
lean_object* v___x_4409_; uint8_t v___x_4410_; 
v___x_4409_ = lean_array_get_size(v_as_4404_);
v___x_4410_ = lean_nat_dec_le(v_stop_4406_, v___x_4409_);
if (v___x_4410_ == 0)
{
uint8_t v___x_4411_; 
v___x_4411_ = lean_nat_dec_lt(v_start_4405_, v___x_4409_);
if (v___x_4411_ == 0)
{
return v___x_4407_;
}
else
{
size_t v___x_4412_; size_t v___x_4413_; lean_object* v___x_4414_; 
v___x_4412_ = lean_usize_of_nat(v_start_4405_);
v___x_4413_ = lean_usize_of_nat(v___x_4409_);
v___x_4414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4404_, v___x_4412_, v___x_4413_, v___x_4407_);
return v___x_4414_;
}
}
else
{
size_t v___x_4415_; size_t v___x_4416_; lean_object* v___x_4417_; 
v___x_4415_ = lean_usize_of_nat(v_start_4405_);
v___x_4416_ = lean_usize_of_nat(v_stop_4406_);
v___x_4417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2_spec__3(v_as_4404_, v___x_4415_, v___x_4416_, v___x_4407_);
return v___x_4417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___boxed(lean_object* v_as_4418_, lean_object* v_start_4419_, lean_object* v_stop_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_as_4418_, v_start_4419_, v_stop_4420_);
lean_dec(v_stop_4420_);
lean_dec(v_start_4419_);
lean_dec_ref(v_as_4418_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object* v_lvals_4422_, lean_object* v_binderGroups_4423_, lean_object* v_typeAscriptionTk_4424_, lean_object* v_type_4425_, lean_object* v_kind_4426_, lean_object* v_lvalsLayout_4427_){
_start:
{
lean_object* v___y_4429_; uint8_t v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; uint8_t v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___x_4454_; lean_object* v___y_4456_; lean_object* v___y_4457_; uint8_t v___y_4458_; lean_object* v___y_4468_; lean_object* v___x_4478_; lean_object* v___x_4479_; uint8_t v___x_4480_; 
v___x_4454_ = lean_unsigned_to_nat(0u);
v___x_4478_ = lean_array_get_size(v_lvals_4422_);
v___x_4479_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4480_ = lean_nat_dec_lt(v___x_4454_, v___x_4478_);
if (v___x_4480_ == 0)
{
v___y_4468_ = v___x_4479_;
goto v___jp_4467_;
}
else
{
uint8_t v___x_4481_; 
v___x_4481_ = lean_nat_dec_le(v___x_4478_, v___x_4478_);
if (v___x_4481_ == 0)
{
if (v___x_4480_ == 0)
{
v___y_4468_ = v___x_4479_;
goto v___jp_4467_;
}
else
{
size_t v___x_4482_; size_t v___x_4483_; lean_object* v___x_4484_; 
v___x_4482_ = ((size_t)0ULL);
v___x_4483_ = lean_usize_of_nat(v___x_4478_);
v___x_4484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_lvals_4422_, v___x_4482_, v___x_4483_, v___x_4479_);
v___y_4468_ = v___x_4484_;
goto v___jp_4467_;
}
}
else
{
size_t v___x_4485_; size_t v___x_4486_; lean_object* v___x_4487_; 
v___x_4485_ = ((size_t)0ULL);
v___x_4486_ = lean_usize_of_nat(v___x_4478_);
v___x_4487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_lvals_4422_, v___x_4485_, v___x_4486_, v___x_4479_);
v___y_4468_ = v___x_4487_;
goto v___jp_4467_;
}
}
v___jp_4428_:
{
size_t v_sz_4433_; size_t v___x_4434_; lean_object* v___x_4435_; lean_object* v_binderGroups_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v_sz_4433_ = lean_array_size(v___y_4431_);
v___x_4434_ = ((size_t)0ULL);
v___x_4435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__3(v_sz_4433_, v___x_4434_, v___y_4431_);
v_binderGroups_4436_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4435_, v___y_4430_);
lean_dec_ref(v___x_4435_);
v___x_4437_ = lean_apply_1(v_lvalsLayout_4427_, v___y_4429_);
v___x_4438_ = lean_unsigned_to_nat(2u);
v___x_4439_ = lean_mk_empty_array_with_capacity(v___x_4438_);
v___x_4440_ = lean_array_push(v___x_4439_, v___x_4437_);
v___x_4441_ = lean_array_push(v___x_4440_, v_binderGroups_4436_);
v___x_4442_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4441_, v___y_4430_);
lean_dec_ref(v___x_4441_);
v___x_4443_ = l_Lean_Fmt_Layouts_typeAscription(v___x_4442_, v_typeAscriptionTk_4424_, v_type_4425_, v___y_4432_);
lean_dec_ref(v___y_4432_);
v___x_4444_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4443_);
return v___x_4444_;
}
v___jp_4445_:
{
if (lean_obj_tag(v_kind_4426_) == 0)
{
uint8_t v_respectPseudoAlignment_4449_; uint8_t v___x_4450_; lean_object* v___x_4451_; 
v_respectPseudoAlignment_4449_ = lean_ctor_get_uint8(v_kind_4426_, 0);
v___x_4450_ = 0;
v___x_4451_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4451_, 0, v___x_4450_);
lean_ctor_set_uint8(v___x_4451_, 1, v___x_4450_);
lean_ctor_set_uint8(v___x_4451_, 2, v___y_4446_);
lean_ctor_set_uint8(v___x_4451_, 3, v_respectPseudoAlignment_4449_);
v___y_4429_ = v___y_4448_;
v___y_4430_ = v___y_4446_;
v___y_4431_ = v___y_4447_;
v___y_4432_ = v___x_4451_;
goto v___jp_4428_;
}
else
{
uint8_t v___x_4452_; lean_object* v___x_4453_; 
v___x_4452_ = 0;
v___x_4453_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_4453_, 0, v___x_4452_);
lean_ctor_set_uint8(v___x_4453_, 1, v___x_4452_);
lean_ctor_set_uint8(v___x_4453_, 2, v___y_4446_);
lean_ctor_set_uint8(v___x_4453_, 3, v___x_4452_);
lean_ctor_set_uint8(v___x_4453_, 4, v___x_4452_);
v___y_4429_ = v___y_4448_;
v___y_4430_ = v___y_4446_;
v___y_4431_ = v___y_4447_;
v___y_4432_ = v___x_4453_;
goto v___jp_4428_;
}
}
v___jp_4455_:
{
uint8_t v___x_4459_; 
v___x_4459_ = 1;
if (v___y_4458_ == 0)
{
lean_object* v___x_4460_; uint8_t v___x_4461_; 
v___x_4460_ = lean_array_get_size(v___y_4456_);
v___x_4461_ = lean_nat_dec_lt(v___x_4454_, v___x_4460_);
if (v___x_4461_ == 0)
{
v___y_4446_ = v___x_4459_;
v___y_4447_ = v___y_4457_;
v___y_4448_ = v___y_4456_;
goto v___jp_4445_;
}
else
{
lean_object* v_v_4462_; lean_object* v___x_4463_; lean_object* v_xs_x27_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v_v_4462_ = lean_array_fget(v___y_4456_, v___x_4454_);
v___x_4463_ = lean_box(0);
v_xs_x27_4464_ = lean_array_fset(v___y_4456_, v___x_4454_, v___x_4463_);
v___x_4465_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4462_);
v___x_4466_ = lean_array_fset(v_xs_x27_4464_, v___x_4454_, v___x_4465_);
v___y_4446_ = v___x_4459_;
v___y_4447_ = v___y_4457_;
v___y_4448_ = v___x_4466_;
goto v___jp_4445_;
}
}
else
{
v___y_4446_ = v___x_4459_;
v___y_4447_ = v___y_4457_;
v___y_4448_ = v___y_4456_;
goto v___jp_4445_;
}
}
v___jp_4467_:
{
lean_object* v___x_4469_; lean_object* v_binderGroups_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; uint8_t v___x_4473_; 
v___x_4469_ = lean_array_get_size(v_binderGroups_4423_);
v_binderGroups_4470_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_binderGroups_4423_, v___x_4454_, v___x_4469_);
v___x_4471_ = lean_array_get_size(v___y_4468_);
v___x_4472_ = lean_unsigned_to_nat(1u);
v___x_4473_ = lean_nat_dec_le(v___x_4471_, v___x_4472_);
if (v___x_4473_ == 0)
{
v___y_4456_ = v___y_4468_;
v___y_4457_ = v_binderGroups_4470_;
v___y_4458_ = v___x_4473_;
goto v___jp_4455_;
}
else
{
uint8_t v___x_4474_; 
v___x_4474_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_type_4425_);
if (v___x_4474_ == 0)
{
v___y_4456_ = v___y_4468_;
v___y_4457_ = v_binderGroups_4470_;
v___y_4458_ = v___x_4474_;
goto v___jp_4455_;
}
else
{
uint8_t v___x_4475_; 
v___x_4475_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_typeAscriptionTk_4424_);
if (v___x_4475_ == 0)
{
v___y_4456_ = v___y_4468_;
v___y_4457_ = v_binderGroups_4470_;
v___y_4458_ = v___x_4475_;
goto v___jp_4455_;
}
else
{
lean_object* v___x_4476_; uint8_t v___x_4477_; 
v___x_4476_ = lean_array_get_size(v_binderGroups_4470_);
v___x_4477_ = lean_nat_dec_eq(v___x_4476_, v___x_4454_);
v___y_4456_ = v___y_4468_;
v___y_4457_ = v_binderGroups_4470_;
v___y_4458_ = v___x_4477_;
goto v___jp_4455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object* v_lvals_4488_, lean_object* v_binderGroups_4489_, lean_object* v_typeAscriptionTk_4490_, lean_object* v_type_4491_, lean_object* v_kind_4492_, lean_object* v_lvalsLayout_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4488_, v_binderGroups_4489_, v_typeAscriptionTk_4490_, v_type_4491_, v_kind_4492_, v_lvalsLayout_4493_);
lean_dec(v_kind_4492_);
lean_dec_ref(v_binderGroups_4489_);
lean_dec_ref(v_lvals_4488_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(uint8_t v___x_4495_, lean_object* v_terms_4496_){
_start:
{
lean_object* v___x_4497_; 
v___x_4497_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4496_, v___x_4495_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object* v___x_4498_, lean_object* v_terms_4499_){
_start:
{
uint8_t v___x_9__boxed_4500_; lean_object* v_res_4501_; 
v___x_9__boxed_4500_ = lean_unbox(v___x_4498_);
v_res_4501_ = l_Lean_Fmt_Layouts_localSignature___lam__0(v___x_9__boxed_4500_, v_terms_4499_);
lean_dec_ref(v_terms_4499_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object* v_lvals_4507_, lean_object* v_binderGroups_4508_, lean_object* v_typeAscriptionTk_4509_, lean_object* v_type_4510_){
_start:
{
lean_object* v___f_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___f_4511_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__0));
v___x_4512_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__1));
v___x_4513_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4507_, v_binderGroups_4508_, v_typeAscriptionTk_4509_, v_type_4510_, v___x_4512_, v___f_4511_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object* v_lvals_4514_, lean_object* v_binderGroups_4515_, lean_object* v_typeAscriptionTk_4516_, lean_object* v_type_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_Fmt_Layouts_localSignature(v_lvals_4514_, v_binderGroups_4515_, v_typeAscriptionTk_4516_, v_type_4517_);
lean_dec_ref(v_binderGroups_4515_);
lean_dec_ref(v_lvals_4514_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0(lean_object* v_terms_4519_){
_start:
{
uint8_t v___x_4520_; lean_object* v___x_4521_; 
v___x_4520_ = 1;
v___x_4521_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4519_, v___x_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0___boxed(lean_object* v_terms_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Lean_Fmt_Layouts_globalSignature___lam__0(v_terms_4522_);
lean_dec_ref(v_terms_4522_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object* v_lvals_4525_, lean_object* v_binderGroups_4526_, lean_object* v_typeAscriptionTk_4527_, lean_object* v_type_4528_){
_start:
{
lean_object* v___f_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___f_4529_ = ((lean_object*)(l_Lean_Fmt_Layouts_globalSignature___closed__0));
v___x_4530_ = lean_box(1);
v___x_4531_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4525_, v_binderGroups_4526_, v_typeAscriptionTk_4527_, v_type_4528_, v___x_4530_, v___f_4529_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object* v_lvals_4532_, lean_object* v_binderGroups_4533_, lean_object* v_typeAscriptionTk_4534_, lean_object* v_type_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_Fmt_Layouts_globalSignature(v_lvals_4532_, v_binderGroups_4533_, v_typeAscriptionTk_4534_, v_type_4535_);
lean_dec_ref(v_binderGroups_4533_);
lean_dec_ref(v_lvals_4532_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object* v_signature_4537_, lean_object* v_separationTk_4538_, lean_object* v_body_4539_, uint8_t v_sticky_4540_){
_start:
{
uint8_t v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; uint8_t v___y_4546_; uint8_t v___y_4550_; lean_object* v___y_4551_; uint8_t v___y_4575_; uint8_t v___x_4591_; 
v___x_4591_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_separationTk_4538_);
if (v___x_4591_ == 0)
{
v___y_4575_ = v___x_4591_;
goto v___jp_4574_;
}
else
{
uint8_t v___x_4592_; 
v___x_4592_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4539_);
v___y_4575_ = v___x_4592_;
goto v___jp_4574_;
}
v___jp_4541_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
lean_inc_ref(v___y_4544_);
v___x_4547_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___y_4545_, v___y_4544_, v_body_4539_, v___y_4546_);
v___x_4548_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_4543_, v___x_4547_, v___y_4542_);
return v___x_4548_;
}
v___jp_4549_:
{
lean_object* v_doc_4552_; 
v_doc_4552_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___y_4551_);
if (v_sticky_4540_ == 0)
{
lean_dec_ref(v_body_4539_);
lean_dec_ref(v_separationTk_4538_);
lean_dec_ref(v_signature_4537_);
return v_doc_4552_;
}
else
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v_lhs_4564_; lean_object* v___x_4565_; 
v___x_4553_ = l_Lean_Fmt_TaggedDoc_flattened(v_signature_4537_);
v___x_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
v___x_4555_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_4556_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4554_, v___x_4555_);
v___x_4557_ = lean_box(0);
v___x_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4558_, 0, v_separationTk_4538_);
v___x_4559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4557_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
lean_ctor_set(v___x_4559_, 2, v___x_4557_);
v___x_4560_ = lean_unsigned_to_nat(2u);
v___x_4561_ = lean_mk_empty_array_with_capacity(v___x_4560_);
v___x_4562_ = lean_array_push(v___x_4561_, v___x_4556_);
v___x_4563_ = lean_array_push(v___x_4562_, v___x_4559_);
v_lhs_4564_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4563_);
lean_dec_ref(v___x_4563_);
lean_inc_ref(v_body_4539_);
v___x_4565_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_body_4539_);
if (lean_obj_tag(v___x_4565_) == 1)
{
lean_object* v_val_4566_; uint8_t v_kind_4567_; lean_object* v___x_4568_; 
v_val_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_val_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v_kind_4567_ = lean_ctor_get_uint8(v_val_4566_, sizeof(void*)*1);
lean_dec(v_val_4566_);
v___x_4568_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
if (v_kind_4567_ == 1)
{
uint8_t v___x_4569_; 
v___x_4569_ = 0;
v___y_4542_ = v_kind_4567_;
v___y_4543_ = v_doc_4552_;
v___y_4544_ = v___x_4568_;
v___y_4545_ = v_lhs_4564_;
v___y_4546_ = v___x_4569_;
goto v___jp_4541_;
}
else
{
v___y_4542_ = v_kind_4567_;
v___y_4543_ = v_doc_4552_;
v___y_4544_ = v___x_4568_;
v___y_4545_ = v_lhs_4564_;
v___y_4546_ = v_sticky_4540_;
goto v___jp_4541_;
}
}
else
{
lean_object* v___x_4570_; lean_object* v___x_4571_; uint8_t v___x_4572_; lean_object* v___x_4573_; 
lean_dec(v___x_4565_);
v___x_4570_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4571_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4564_, v___x_4570_, v_body_4539_, v___y_4550_);
v___x_4572_ = 0;
v___x_4573_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4552_, v___x_4571_, v___x_4572_);
return v___x_4573_;
}
}
}
v___jp_4574_:
{
uint8_t v___x_4576_; 
v___x_4576_ = 1;
if (v___y_4575_ == 0)
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v_lhs_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
lean_inc_ref(v_signature_4537_);
v___x_4577_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4537_);
v___x_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
v___x_4579_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_4580_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4578_, v___x_4579_);
v___x_4581_ = lean_box(0);
lean_inc_ref(v_separationTk_4538_);
v___x_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4582_, 0, v_separationTk_4538_);
v___x_4583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4581_);
lean_ctor_set(v___x_4583_, 1, v___x_4582_);
lean_ctor_set(v___x_4583_, 2, v___x_4581_);
v___x_4584_ = lean_unsigned_to_nat(2u);
v___x_4585_ = lean_mk_empty_array_with_capacity(v___x_4584_);
v___x_4586_ = lean_array_push(v___x_4585_, v___x_4580_);
v___x_4587_ = lean_array_push(v___x_4586_, v___x_4583_);
v_lhs_4588_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4587_);
lean_dec_ref(v___x_4587_);
v___x_4589_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_body_4539_);
v___x_4590_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4588_, v___x_4589_, v_body_4539_, v___x_4576_);
v___y_4550_ = v___x_4576_;
v___y_4551_ = v___x_4590_;
goto v___jp_4549_;
}
else
{
lean_inc_ref(v_signature_4537_);
v___y_4550_ = v___x_4576_;
v___y_4551_ = v_signature_4537_;
goto v___jp_4549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object* v_signature_4593_, lean_object* v_separationTk_4594_, lean_object* v_body_4595_, lean_object* v_sticky_4596_){
_start:
{
uint8_t v_sticky_boxed_4597_; lean_object* v_res_4598_; 
v_sticky_boxed_4597_ = lean_unbox(v_sticky_4596_);
v_res_4598_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_signature_4593_, v_separationTk_4594_, v_body_4595_, v_sticky_boxed_4597_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object* v_signature_4599_, lean_object* v_matchAlts_4600_){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4601_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4599_);
v___x_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
v___x_4603_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4604_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4602_, v___x_4603_);
v___x_4605_ = lean_box(0);
v___x_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4606_, 0, v_matchAlts_4600_);
v___x_4607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4605_);
lean_ctor_set(v___x_4607_, 1, v___x_4606_);
lean_ctor_set(v___x_4607_, 2, v___x_4605_);
v___x_4608_ = lean_unsigned_to_nat(2u);
v___x_4609_ = lean_mk_empty_array_with_capacity(v___x_4608_);
v___x_4610_ = lean_array_push(v___x_4609_, v___x_4604_);
v___x_4611_ = lean_array_push(v___x_4610_, v___x_4607_);
v___x_4612_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4611_);
lean_dec_ref(v___x_4611_);
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object* v_signature_4613_, lean_object* v_whereTk_4614_, lean_object* v_body_4615_){
_start:
{
uint8_t v___x_4616_; 
v___x_4616_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4615_);
if (v___x_4616_ == 0)
{
uint8_t v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v_lhs_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4617_ = 1;
v___x_4618_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4613_);
v___x_4619_ = lean_unsigned_to_nat(2u);
v___x_4620_ = lean_mk_empty_array_with_capacity(v___x_4619_);
v___x_4621_ = lean_array_push(v___x_4620_, v___x_4618_);
v___x_4622_ = lean_array_push(v___x_4621_, v_whereTk_4614_);
v_lhs_4623_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4622_);
lean_dec_ref(v___x_4622_);
v___x_4624_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4625_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4623_, v___x_4624_, v_body_4615_, v___x_4617_);
v___x_4626_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4625_);
return v___x_4626_;
}
else
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
lean_dec_ref(v_body_4615_);
v___x_4627_ = lean_unsigned_to_nat(2u);
v___x_4628_ = lean_mk_empty_array_with_capacity(v___x_4627_);
v___x_4629_ = lean_array_push(v___x_4628_, v_signature_4613_);
v___x_4630_ = lean_array_push(v___x_4629_, v_whereTk_4614_);
v___x_4631_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4630_);
lean_dec_ref(v___x_4630_);
return v___x_4631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object* v_lbs_4633_, lean_object* v_lhses_4634_, lean_object* v_subBinderGroups_4635_, lean_object* v_typeAscriptionTk_x3f_4636_, lean_object* v_type_x3f_4637_, lean_object* v_colonEqTk_x3f_4638_, lean_object* v_default_x3f_4639_, lean_object* v_rbs_4640_, lean_object* v_kind_4641_){
_start:
{
lean_object* v_lbs_4642_; lean_object* v___x_4643_; lean_object* v_binderSignature_4644_; uint8_t v___x_4645_; lean_object* v_simpleBinder_4646_; lean_object* v_rbs_4647_; lean_object* v___x_4648_; 
v_lbs_4642_ = l_Lean_Fmt_Layouts_atomic(v_lbs_4633_);
v___x_4643_ = ((lean_object*)(l_Lean_Fmt_Layouts_binder___closed__0));
v_binderSignature_4644_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lhses_4634_, v_subBinderGroups_4635_, v_typeAscriptionTk_x3f_4636_, v_type_x3f_4637_, v_kind_4641_, v___x_4643_);
v___x_4645_ = 0;
v_simpleBinder_4646_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_binderSignature_4644_, v_colonEqTk_x3f_4638_, v_default_x3f_4639_, v___x_4645_);
v_rbs_4647_ = l_Lean_Fmt_Layouts_atomic(v_rbs_4640_);
v___x_4648_ = l_Lean_Fmt_Layouts_parens(v_lbs_4642_, v_simpleBinder_4646_, v_rbs_4647_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder___boxed(lean_object* v_lbs_4649_, lean_object* v_lhses_4650_, lean_object* v_subBinderGroups_4651_, lean_object* v_typeAscriptionTk_x3f_4652_, lean_object* v_type_x3f_4653_, lean_object* v_colonEqTk_x3f_4654_, lean_object* v_default_x3f_4655_, lean_object* v_rbs_4656_, lean_object* v_kind_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Lean_Fmt_Layouts_binder(v_lbs_4649_, v_lhses_4650_, v_subBinderGroups_4651_, v_typeAscriptionTk_x3f_4652_, v_type_x3f_4653_, v_colonEqTk_x3f_4654_, v_default_x3f_4655_, v_rbs_4656_, v_kind_4657_);
lean_dec(v_kind_4657_);
lean_dec_ref(v_rbs_4656_);
lean_dec_ref(v_subBinderGroups_4651_);
lean_dec_ref(v_lhses_4650_);
lean_dec_ref(v_lbs_4649_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object* v_keywordTk_4662_, lean_object* v_config_4663_, lean_object* v_decl_4664_, uint8_t v_format_4665_){
_start:
{
lean_object* v___f_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v_signature_4672_; lean_object* v___y_4674_; 
v___f_4666_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_4667_ = lean_unsigned_to_nat(2u);
v___x_4668_ = lean_mk_empty_array_with_capacity(v___x_4667_);
lean_inc_ref(v___x_4668_);
v___x_4669_ = lean_array_push(v___x_4668_, v_keywordTk_4662_);
v___x_4670_ = lean_array_push(v___x_4669_, v_config_4663_);
v___x_4671_ = ((lean_object*)(l_Lean_Fmt_Layouts_letDecl___closed__0));
v_signature_4672_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4670_, v___x_4671_);
if (v_format_4665_ == 0)
{
lean_object* v___x_4686_; 
v___x_4686_ = l_Lean_Fmt_TaggedDoc_space;
v___y_4674_ = v___x_4686_;
goto v___jp_4673_;
}
else
{
lean_object* v___x_4687_; 
v___x_4687_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4674_ = v___x_4687_;
goto v___jp_4673_;
}
v___jp_4673_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4675_, 0, v_signature_4672_);
lean_inc_ref(v___y_4674_);
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v___y_4674_);
lean_ctor_set(v___x_4676_, 1, v___f_4666_);
v___x_4677_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4675_, v___x_4676_);
v___x_4678_ = lean_box(0);
v___x_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4679_, 0, v_decl_4664_);
v___x_4680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4678_);
lean_ctor_set(v___x_4680_, 1, v___x_4679_);
lean_ctor_set(v___x_4680_, 2, v___x_4678_);
v___x_4681_ = lean_array_push(v___x_4668_, v___x_4677_);
v___x_4682_ = lean_array_push(v___x_4681_, v___x_4680_);
v___x_4683_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4682_);
lean_dec_ref(v___x_4682_);
v___x_4684_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4683_);
v___x_4685_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4684_);
return v___x_4685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl___boxed(lean_object* v_keywordTk_4688_, lean_object* v_config_4689_, lean_object* v_decl_4690_, lean_object* v_format_4691_){
_start:
{
uint8_t v_format_boxed_4692_; lean_object* v_res_4693_; 
v_format_boxed_4692_ = lean_unbox(v_format_4691_);
v_res_4693_ = l_Lean_Fmt_Layouts_letDecl(v_keywordTk_4688_, v_config_4689_, v_decl_4690_, v_format_boxed_4692_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(size_t v_sz_4694_, size_t v_i_4695_, lean_object* v_bs_4696_){
_start:
{
uint8_t v___x_4697_; 
v___x_4697_ = lean_usize_dec_lt(v_i_4695_, v_sz_4694_);
if (v___x_4697_ == 0)
{
return v_bs_4696_;
}
else
{
lean_object* v_v_4698_; lean_object* v_quantifier_4699_; lean_object* v_binderGroups_4700_; lean_object* v_typeAscriptionTk_x3f_4701_; lean_object* v_type_x3f_4702_; lean_object* v_separationTk_4703_; lean_object* v___x_4704_; lean_object* v_bs_x27_4705_; lean_object* v___x_4706_; lean_object* v_signature_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; lean_object* v___x_4714_; size_t v___x_4715_; size_t v___x_4716_; lean_object* v___x_4717_; 
v_v_4698_ = lean_array_uget_borrowed(v_bs_4696_, v_i_4695_);
v_quantifier_4699_ = lean_ctor_get(v_v_4698_, 0);
lean_inc_ref(v_quantifier_4699_);
v_binderGroups_4700_ = lean_ctor_get(v_v_4698_, 1);
lean_inc_ref(v_binderGroups_4700_);
v_typeAscriptionTk_x3f_4701_ = lean_ctor_get(v_v_4698_, 2);
lean_inc_ref(v_typeAscriptionTk_x3f_4701_);
v_type_x3f_4702_ = lean_ctor_get(v_v_4698_, 3);
lean_inc_ref(v_type_x3f_4702_);
v_separationTk_4703_ = lean_ctor_get(v_v_4698_, 4);
lean_inc_ref(v_separationTk_4703_);
v___x_4704_ = lean_unsigned_to_nat(0u);
v_bs_x27_4705_ = lean_array_uset(v_bs_4696_, v_i_4695_, v___x_4704_);
v___x_4706_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v_signature_4707_ = l_Lean_Fmt_Layouts_localSignature(v___x_4706_, v_binderGroups_4700_, v_typeAscriptionTk_x3f_4701_, v_type_x3f_4702_);
lean_dec_ref(v_binderGroups_4700_);
v___x_4708_ = lean_unsigned_to_nat(2u);
v___x_4709_ = lean_mk_empty_array_with_capacity(v___x_4708_);
v___x_4710_ = lean_array_push(v___x_4709_, v_signature_4707_);
v___x_4711_ = lean_array_push(v___x_4710_, v_separationTk_4703_);
v___x_4712_ = l_Lean_Fmt_Layouts_atomic(v___x_4711_);
lean_dec_ref(v___x_4711_);
v___x_4713_ = 2;
v___x_4714_ = l_Lean_Fmt_Layouts_prefixOperator(v_quantifier_4699_, v___x_4712_, v___x_4713_);
v___x_4715_ = ((size_t)1ULL);
v___x_4716_ = lean_usize_add(v_i_4695_, v___x_4715_);
v___x_4717_ = lean_array_uset(v_bs_x27_4705_, v_i_4695_, v___x_4714_);
v_i_4695_ = v___x_4716_;
v_bs_4696_ = v___x_4717_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0___boxed(lean_object* v_sz_4719_, lean_object* v_i_4720_, lean_object* v_bs_4721_){
_start:
{
size_t v_sz_boxed_4722_; size_t v_i_boxed_4723_; lean_object* v_res_4724_; 
v_sz_boxed_4722_ = lean_unbox_usize(v_sz_4719_);
lean_dec(v_sz_4719_);
v_i_boxed_4723_ = lean_unbox_usize(v_i_4720_);
lean_dec(v_i_4720_);
v_res_4724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_boxed_4722_, v_i_boxed_4723_, v_bs_4721_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(size_t v_sz_4725_, size_t v_i_4726_, lean_object* v_bs_4727_){
_start:
{
uint8_t v___x_4728_; 
v___x_4728_ = lean_usize_dec_lt(v_i_4726_, v_sz_4725_);
if (v___x_4728_ == 0)
{
return v_bs_4727_;
}
else
{
lean_object* v_v_4729_; lean_object* v___x_4730_; lean_object* v_bs_x27_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; size_t v___x_4734_; size_t v___x_4735_; lean_object* v___x_4736_; 
v_v_4729_ = lean_array_uget(v_bs_4727_, v_i_4726_);
v___x_4730_ = lean_unsigned_to_nat(0u);
v_bs_x27_4731_ = lean_array_uset(v_bs_4727_, v_i_4726_, v___x_4730_);
v___x_4732_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4729_);
v___x_4733_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
lean_ctor_set_uint8(v___x_4733_, sizeof(void*)*1, v___x_4728_);
v___x_4734_ = ((size_t)1ULL);
v___x_4735_ = lean_usize_add(v_i_4726_, v___x_4734_);
v___x_4736_ = lean_array_uset(v_bs_x27_4731_, v_i_4726_, v___x_4733_);
v_i_4726_ = v___x_4735_;
v_bs_4727_ = v___x_4736_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1___boxed(lean_object* v_sz_4738_, lean_object* v_i_4739_, lean_object* v_bs_4740_){
_start:
{
size_t v_sz_boxed_4741_; size_t v_i_boxed_4742_; lean_object* v_res_4743_; 
v_sz_boxed_4741_ = lean_unbox_usize(v_sz_4738_);
lean_dec(v_sz_4738_);
v_i_boxed_4742_ = lean_unbox_usize(v_i_4739_);
lean_dec(v_i_4739_);
v_res_4743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_boxed_4741_, v_i_boxed_4742_, v_bs_4740_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_quantified(lean_object* v_quantifierHeads_4744_, lean_object* v_body_4745_){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v___x_4746_ = lean_array_get_size(v_quantifierHeads_4744_);
v___x_4747_ = lean_unsigned_to_nat(0u);
v___x_4748_ = lean_nat_dec_eq(v___x_4746_, v___x_4747_);
if (v___x_4748_ == 0)
{
size_t v_sz_4749_; size_t v___x_4750_; lean_object* v_quantifierHeads_4751_; size_t v_sz_4752_; lean_object* v_quantifierHeads_4753_; lean_object* v___x_4754_; lean_object* v_components_4755_; lean_object* v___x_4756_; lean_object* v_quantifiers_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v_sz_4749_ = lean_array_size(v_quantifierHeads_4744_);
v___x_4750_ = ((size_t)0ULL);
v_quantifierHeads_4751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_4749_, v___x_4750_, v_quantifierHeads_4744_);
v_sz_4752_ = lean_array_size(v_quantifierHeads_4751_);
v_quantifierHeads_4753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_4752_, v___x_4750_, v_quantifierHeads_4751_);
v___x_4754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4754_, 0, v_body_4745_);
lean_ctor_set_uint8(v___x_4754_, sizeof(void*)*1, v___x_4748_);
v_components_4755_ = lean_array_push(v_quantifierHeads_4753_, v___x_4754_);
v___x_4756_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_quantifiers_4757_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(v_components_4755_, v___x_4756_);
v___x_4758_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_quantifiers_4757_);
v___x_4759_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4758_);
return v___x_4759_;
}
else
{
lean_dec_ref(v_quantifierHeads_4744_);
return v_body_4745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_subtype(lean_object* v_lbTk_4763_, lean_object* v_lhs_4764_, lean_object* v_sepTk_4765_, lean_object* v_rhs_4766_, lean_object* v_rbTk_4767_, lean_object* v_format_4768_){
_start:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v_body_4776_; lean_object* v___x_4777_; 
v___x_4769_ = lean_unsigned_to_nat(3u);
v___x_4770_ = lean_mk_empty_array_with_capacity(v___x_4769_);
v___x_4771_ = lean_array_push(v___x_4770_, v_lhs_4764_);
v___x_4772_ = lean_array_push(v___x_4771_, v_sepTk_4765_);
v___x_4773_ = lean_array_push(v___x_4772_, v_rhs_4766_);
v___x_4774_ = ((lean_object*)(l_Lean_Fmt_Layouts_subtype___closed__0));
v___x_4775_ = l_Lean_Fmt_Layouts_infixOperator(v___x_4773_, v___x_4774_);
v_body_4776_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4775_);
v___x_4777_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_4763_, v_body_4776_, v_rbTk_4767_, v_format_4768_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(lean_object* v_tk_4778_, lean_object* v_block_4779_, uint8_t v_allowFlattening_4780_){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4782_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_tk_4778_, v___x_4781_, v_block_4779_, v_allowFlattening_4780_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken___boxed(lean_object* v_tk_4783_, lean_object* v_block_4784_, lean_object* v_allowFlattening_4785_){
_start:
{
uint8_t v_allowFlattening_boxed_4786_; lean_object* v_res_4787_; 
v_allowFlattening_boxed_4786_ = lean_unbox(v_allowFlattening_4785_);
v_res_4787_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_tk_4783_, v_block_4784_, v_allowFlattening_boxed_4786_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(uint8_t v_allowFlattening_4788_, size_t v_sz_4789_, size_t v_i_4790_, lean_object* v_bs_4791_){
_start:
{
uint8_t v___x_4792_; 
v___x_4792_ = lean_usize_dec_lt(v_i_4790_, v_sz_4789_);
if (v___x_4792_ == 0)
{
return v_bs_4791_;
}
else
{
lean_object* v_v_4793_; lean_object* v_elseTk_4794_; lean_object* v_ifTk_4795_; lean_object* v_cond_4796_; lean_object* v_thenTk_4797_; lean_object* v_thenBlock_4798_; lean_object* v___x_4799_; lean_object* v_bs_x27_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v_tk_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; lean_object* v___x_4809_; lean_object* v_head_4810_; lean_object* v_then_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v_trailingThen_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v_leadingThen_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; size_t v___x_4831_; size_t v___x_4832_; lean_object* v___x_4833_; 
v_v_4793_ = lean_array_uget_borrowed(v_bs_4791_, v_i_4790_);
v_elseTk_4794_ = lean_ctor_get(v_v_4793_, 0);
lean_inc_ref(v_elseTk_4794_);
v_ifTk_4795_ = lean_ctor_get(v_v_4793_, 1);
lean_inc_ref(v_ifTk_4795_);
v_cond_4796_ = lean_ctor_get(v_v_4793_, 2);
lean_inc_ref(v_cond_4796_);
v_thenTk_4797_ = lean_ctor_get(v_v_4793_, 3);
lean_inc_ref(v_thenTk_4797_);
v_thenBlock_4798_ = lean_ctor_get(v_v_4793_, 4);
lean_inc_ref(v_thenBlock_4798_);
v___x_4799_ = lean_unsigned_to_nat(0u);
v_bs_x27_4800_ = lean_array_uset(v_bs_4791_, v_i_4790_, v___x_4799_);
v___x_4801_ = lean_unsigned_to_nat(2u);
v___x_4802_ = lean_mk_empty_array_with_capacity(v___x_4801_);
lean_inc_ref_n(v___x_4802_, 4);
v___x_4803_ = lean_array_push(v___x_4802_, v_elseTk_4794_);
v___x_4804_ = lean_array_push(v___x_4803_, v_ifTk_4795_);
v_tk_4805_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4804_);
lean_dec_ref(v___x_4804_);
v___x_4806_ = lean_array_push(v___x_4802_, v_tk_4805_);
v___x_4807_ = lean_array_push(v___x_4806_, v_cond_4796_);
v___x_4808_ = 0;
v___x_4809_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4809_, 0, v___x_4792_);
lean_ctor_set_uint8(v___x_4809_, 1, v___x_4808_);
lean_ctor_set_uint8(v___x_4809_, 2, v___x_4808_);
lean_ctor_set_uint8(v___x_4809_, 3, v___x_4808_);
v_head_4810_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4807_, v___x_4809_);
v_then_4811_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_thenTk_4797_, v_thenBlock_4798_, v_allowFlattening_4788_);
lean_inc_ref(v_head_4810_);
v___x_4812_ = l_Lean_Fmt_TaggedDoc_flattened(v_head_4810_);
v___x_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4812_);
v___x_4814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4815_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4813_, v___x_4814_);
v___x_4816_ = lean_box(0);
v___x_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4817_, 0, v_then_4811_);
v___x_4818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4816_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
lean_ctor_set(v___x_4818_, 2, v___x_4816_);
v___x_4819_ = lean_array_push(v___x_4802_, v___x_4815_);
lean_inc_ref(v___x_4818_);
v___x_4820_ = lean_array_push(v___x_4819_, v___x_4818_);
v_trailingThen_4821_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4820_);
lean_dec_ref(v___x_4820_);
v___x_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4822_, 0, v_head_4810_);
v___x_4823_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_4824_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4822_, v___x_4823_);
v___x_4825_ = lean_array_push(v___x_4802_, v___x_4824_);
v___x_4826_ = lean_array_push(v___x_4825_, v___x_4818_);
v_leadingThen_4827_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4826_);
lean_dec_ref(v___x_4826_);
v___x_4828_ = lean_array_push(v___x_4802_, v_trailingThen_4821_);
v___x_4829_ = lean_array_push(v___x_4828_, v_leadingThen_4827_);
v___x_4830_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_4829_);
v___x_4831_ = ((size_t)1ULL);
v___x_4832_ = lean_usize_add(v_i_4790_, v___x_4831_);
v___x_4833_ = lean_array_uset(v_bs_x27_4800_, v_i_4790_, v___x_4830_);
v_i_4790_ = v___x_4832_;
v_bs_4791_ = v___x_4833_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0___boxed(lean_object* v_allowFlattening_4835_, lean_object* v_sz_4836_, lean_object* v_i_4837_, lean_object* v_bs_4838_){
_start:
{
uint8_t v_allowFlattening_boxed_4839_; size_t v_sz_boxed_4840_; size_t v_i_boxed_4841_; lean_object* v_res_4842_; 
v_allowFlattening_boxed_4839_ = lean_unbox(v_allowFlattening_4835_);
v_sz_boxed_4840_ = lean_unbox_usize(v_sz_4836_);
lean_dec(v_sz_4836_);
v_i_boxed_4841_ = lean_unbox_usize(v_i_4837_);
lean_dec(v_i_4837_);
v_res_4842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_boxed_4839_, v_sz_boxed_4840_, v_i_boxed_4841_, v_bs_4838_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(lean_object* v_elseIfs_4843_, lean_object* v_elseTk_4844_, lean_object* v_elseBlock_4845_, uint8_t v_allowFlattening_4846_){
_start:
{
size_t v_sz_4847_; size_t v___x_4848_; lean_object* v_elseIfs_4849_; lean_object* v_else_4850_; lean_object* v_blocks_4851_; size_t v_sz_4852_; lean_object* v_blocks_4853_; lean_object* v_conditional_4854_; lean_object* v___x_4855_; 
v_sz_4847_ = lean_array_size(v_elseIfs_4843_);
v___x_4848_ = ((size_t)0ULL);
v_elseIfs_4849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_4846_, v_sz_4847_, v___x_4848_, v_elseIfs_4843_);
v_else_4850_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_elseTk_4844_, v_elseBlock_4845_, v_allowFlattening_4846_);
v_blocks_4851_ = lean_array_push(v_elseIfs_4849_, v_else_4850_);
v_sz_4852_ = lean_array_size(v_blocks_4851_);
v_blocks_4853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_4852_, v___x_4848_, v_blocks_4851_);
v_conditional_4854_ = l_Lean_Fmt_TaggedDoc_combine(v_blocks_4853_);
lean_dec_ref(v_blocks_4853_);
v___x_4855_ = l_Lean_Fmt_TaggedDoc_aligned(v_conditional_4854_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk___boxed(lean_object* v_elseIfs_4856_, lean_object* v_elseTk_4857_, lean_object* v_elseBlock_4858_, lean_object* v_allowFlattening_4859_){
_start:
{
uint8_t v_allowFlattening_boxed_4860_; lean_object* v_res_4861_; 
v_allowFlattening_boxed_4860_ = lean_unbox(v_allowFlattening_4859_);
v_res_4861_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4856_, v_elseTk_4857_, v_elseBlock_4858_, v_allowFlattening_boxed_4860_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(lean_object* v_as_4862_, size_t v_i_4863_, size_t v_stop_4864_, lean_object* v_b_4865_){
_start:
{
lean_object* v___y_4867_; uint8_t v___x_4871_; 
v___x_4871_ = lean_usize_dec_eq(v_i_4863_, v_stop_4864_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; uint8_t v___y_4874_; lean_object* v_elseTk_4885_; lean_object* v_ifTk_4886_; uint8_t v___x_4887_; 
v___x_4872_ = lean_array_uget_borrowed(v_as_4862_, v_i_4863_);
v_elseTk_4885_ = lean_ctor_get(v___x_4872_, 0);
v_ifTk_4886_ = lean_ctor_get(v___x_4872_, 1);
v___x_4887_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_elseTk_4885_);
if (v___x_4887_ == 0)
{
v___y_4874_ = v___x_4887_;
goto v___jp_4873_;
}
else
{
uint8_t v___x_4888_; 
v___x_4888_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_ifTk_4886_);
v___y_4874_ = v___x_4888_;
goto v___jp_4873_;
}
v___jp_4873_:
{
if (v___y_4874_ == 0)
{
lean_object* v___x_4875_; 
lean_inc(v___x_4872_);
v___x_4875_ = lean_array_push(v_b_4865_, v___x_4872_);
v___y_4867_ = v___x_4875_;
goto v___jp_4866_;
}
else
{
lean_object* v_cond_4876_; lean_object* v_thenTk_4877_; lean_object* v_thenBlock_4878_; uint8_t v___x_4879_; 
v_cond_4876_ = lean_ctor_get(v___x_4872_, 2);
v_thenTk_4877_ = lean_ctor_get(v___x_4872_, 3);
v_thenBlock_4878_ = lean_ctor_get(v___x_4872_, 4);
v___x_4879_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_cond_4876_);
if (v___x_4879_ == 0)
{
lean_object* v___x_4880_; 
lean_inc(v___x_4872_);
v___x_4880_ = lean_array_push(v_b_4865_, v___x_4872_);
v___y_4867_ = v___x_4880_;
goto v___jp_4866_;
}
else
{
uint8_t v___x_4881_; 
v___x_4881_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenTk_4877_);
if (v___x_4881_ == 0)
{
lean_object* v___x_4882_; 
lean_inc(v___x_4872_);
v___x_4882_ = lean_array_push(v_b_4865_, v___x_4872_);
v___y_4867_ = v___x_4882_;
goto v___jp_4866_;
}
else
{
uint8_t v___x_4883_; 
v___x_4883_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenBlock_4878_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; 
lean_inc(v___x_4872_);
v___x_4884_ = lean_array_push(v_b_4865_, v___x_4872_);
v___y_4867_ = v___x_4884_;
goto v___jp_4866_;
}
else
{
v___y_4867_ = v_b_4865_;
goto v___jp_4866_;
}
}
}
}
}
}
else
{
return v_b_4865_;
}
v___jp_4866_:
{
size_t v___x_4868_; size_t v___x_4869_; 
v___x_4868_ = ((size_t)1ULL);
v___x_4869_ = lean_usize_add(v_i_4863_, v___x_4868_);
v_i_4863_ = v___x_4869_;
v_b_4865_ = v___y_4867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0___boxed(lean_object* v_as_4889_, lean_object* v_i_4890_, lean_object* v_stop_4891_, lean_object* v_b_4892_){
_start:
{
size_t v_i_boxed_4893_; size_t v_stop_boxed_4894_; lean_object* v_res_4895_; 
v_i_boxed_4893_ = lean_unbox_usize(v_i_4890_);
lean_dec(v_i_4890_);
v_stop_boxed_4894_ = lean_unbox_usize(v_stop_4891_);
lean_dec(v_stop_4891_);
v_res_4895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_as_4889_, v_i_boxed_4893_, v_stop_boxed_4894_, v_b_4892_);
lean_dec_ref(v_as_4889_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional(lean_object* v_ifTk_4898_, lean_object* v_cond_4899_, lean_object* v_thenTk_4900_, lean_object* v_thenBlock_4901_, lean_object* v_elseIfs_4902_, lean_object* v_elseTk_4903_, lean_object* v_elseBlock_4904_, uint8_t v_allowFlattening_4905_){
_start:
{
lean_object* v___y_4907_; uint8_t v___y_4908_; lean_object* v___y_4927_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; uint8_t v___x_4934_; 
v___x_4931_ = lean_unsigned_to_nat(0u);
v___x_4932_ = lean_array_get_size(v_elseIfs_4902_);
v___x_4933_ = ((lean_object*)(l_Lean_Fmt_Layouts_conditional___closed__0));
v___x_4934_ = lean_nat_dec_lt(v___x_4931_, v___x_4932_);
if (v___x_4934_ == 0)
{
v___y_4927_ = v___x_4933_;
goto v___jp_4926_;
}
else
{
uint8_t v___x_4935_; 
v___x_4935_ = lean_nat_dec_le(v___x_4932_, v___x_4932_);
if (v___x_4935_ == 0)
{
if (v___x_4934_ == 0)
{
v___y_4927_ = v___x_4933_;
goto v___jp_4926_;
}
else
{
size_t v___x_4936_; size_t v___x_4937_; lean_object* v___x_4938_; 
v___x_4936_ = ((size_t)0ULL);
v___x_4937_ = lean_usize_of_nat(v___x_4932_);
v___x_4938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_4902_, v___x_4936_, v___x_4937_, v___x_4933_);
v___y_4927_ = v___x_4938_;
goto v___jp_4926_;
}
}
else
{
size_t v___x_4939_; size_t v___x_4940_; lean_object* v___x_4941_; 
v___x_4939_ = ((size_t)0ULL);
v___x_4940_ = lean_usize_of_nat(v___x_4932_);
v___x_4941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_4902_, v___x_4939_, v___x_4940_, v___x_4933_);
v___y_4927_ = v___x_4941_;
goto v___jp_4926_;
}
}
v___jp_4906_:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v_elseIfs_4914_; 
v___x_4909_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_4910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4909_);
lean_ctor_set(v___x_4910_, 1, v_ifTk_4898_);
lean_ctor_set(v___x_4910_, 2, v_cond_4899_);
lean_ctor_set(v___x_4910_, 3, v_thenTk_4900_);
lean_ctor_set(v___x_4910_, 4, v_thenBlock_4901_);
v___x_4911_ = lean_unsigned_to_nat(1u);
v___x_4912_ = lean_mk_empty_array_with_capacity(v___x_4911_);
v___x_4913_ = lean_array_push(v___x_4912_, v___x_4910_);
v_elseIfs_4914_ = l_Array_append___redArg(v___x_4913_, v___y_4907_);
lean_dec_ref(v___y_4907_);
if (v___y_4908_ == 0)
{
lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4915_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4914_, v_elseTk_4903_, v_elseBlock_4904_, v___y_4908_);
v___x_4916_ = l_Lean_Fmt_TaggedDoc_unflattenable(v___x_4915_);
return v___x_4916_;
}
else
{
lean_object* v___x_4917_; lean_object* v___x_4918_; uint8_t v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; 
lean_inc_ref(v_elseBlock_4904_);
lean_inc_ref(v_elseTk_4903_);
lean_inc_ref(v_elseIfs_4914_);
v___x_4917_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4914_, v_elseTk_4903_, v_elseBlock_4904_, v___y_4908_);
v___x_4918_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_4917_);
v___x_4919_ = 0;
v___x_4920_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4914_, v_elseTk_4903_, v_elseBlock_4904_, v___x_4919_);
v___x_4921_ = lean_unsigned_to_nat(2u);
v___x_4922_ = lean_mk_empty_array_with_capacity(v___x_4921_);
v___x_4923_ = lean_array_push(v___x_4922_, v___x_4918_);
v___x_4924_ = lean_array_push(v___x_4923_, v___x_4920_);
v___x_4925_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_4924_);
return v___x_4925_;
}
}
v___jp_4926_:
{
if (v_allowFlattening_4905_ == 0)
{
v___y_4907_ = v___y_4927_;
v___y_4908_ = v_allowFlattening_4905_;
goto v___jp_4906_;
}
else
{
lean_object* v___x_4928_; lean_object* v___x_4929_; uint8_t v___x_4930_; 
v___x_4928_ = lean_array_get_size(v___y_4927_);
v___x_4929_ = lean_unsigned_to_nat(0u);
v___x_4930_ = lean_nat_dec_eq(v___x_4928_, v___x_4929_);
v___y_4907_ = v___y_4927_;
v___y_4908_ = v___x_4930_;
goto v___jp_4906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional___boxed(lean_object* v_ifTk_4942_, lean_object* v_cond_4943_, lean_object* v_thenTk_4944_, lean_object* v_thenBlock_4945_, lean_object* v_elseIfs_4946_, lean_object* v_elseTk_4947_, lean_object* v_elseBlock_4948_, lean_object* v_allowFlattening_4949_){
_start:
{
uint8_t v_allowFlattening_boxed_4950_; lean_object* v_res_4951_; 
v_allowFlattening_boxed_4950_ = lean_unbox(v_allowFlattening_4949_);
v_res_4951_ = l_Lean_Fmt_Layouts_conditional(v_ifTk_4942_, v_cond_4943_, v_thenTk_4944_, v_thenBlock_4945_, v_elseIfs_4946_, v_elseTk_4947_, v_elseBlock_4948_, v_allowFlattening_boxed_4950_);
lean_dec_ref(v_elseIfs_4946_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_strLit(lean_object* v_prefix_4952_, lean_object* v_str_4953_){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; uint8_t v___x_4959_; lean_object* v___x_4960_; 
v___x_4954_ = lean_unsigned_to_nat(2u);
v___x_4955_ = lean_mk_empty_array_with_capacity(v___x_4954_);
v___x_4956_ = lean_array_push(v___x_4955_, v_prefix_4952_);
v___x_4957_ = lean_array_push(v___x_4956_, v_str_4953_);
v___x_4958_ = l_Lean_Fmt_Layouts_atomic(v___x_4957_);
lean_dec_ref(v___x_4957_);
v___x_4959_ = 0;
v___x_4960_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_4958_, v___x_4959_);
return v___x_4960_;
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
