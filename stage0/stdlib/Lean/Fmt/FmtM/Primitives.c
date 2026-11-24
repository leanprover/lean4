// Lean compiler output
// Module: Lean.Fmt.FmtM.Primitives
// Imports: public import Lean.Fmt.FmtM.Attribute import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_hardNl___redArg();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_DefaultCost_ofOverflowFallbackPenalty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_fillWith___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_List_findSome_x3f___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t, lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Fmt_Doc_isAtomic___redArg(lean_object*);
lean_object* l_Lean_Fmt_DefaultCost_ofFailureFallbackPenalty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Fmt_Doc_isCompoundAtomic___redArg(lean_object*);
lean_object* l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_break___redArg();
lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___boxed(lean_object*);
lean_object* l_Lean_Fmt_Doc_empty___redArg();
uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_final___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_nl___redArg();
lean_object* l_Lean_Fmt_Doc_newline___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_nested(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_hardNested(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_initial___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_fill___redArg___boxed(lean_object*);
lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_multiLineRawTagId;
LEAN_EXPORT lean_object* l_Lean_Fmt_firstSyntaxTagId;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedRaw___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedRaw___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedRaw(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedRaw___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isTagged(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isTagged___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_markMultiLineRaw(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateMetaData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_failure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_failure___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_failure;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_newline(lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_nl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_nl___closed__0;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_nl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_nl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_nl;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_break___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_break___closed__0;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_break___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_break___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_break;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_hardNl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_hardNl___closed__0;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_hardNl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_hardNl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_empty___closed__0;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_empty;
static const lean_string_object l_Lean_Fmt_TaggedDoc_space___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Fmt_TaggedDoc_space___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_space___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_space___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_space___closed__1;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_space___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_space___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_space;
static const lean_closure_object l_Lean_Fmt_TaggedDoc_nested___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_nested, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_TaggedDoc_nested___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_nested___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_hardNested___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_hardNested, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_TaggedDoc_hardNested___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_hardNested___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_doublyNested(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_unflattenable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_unflattenable___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_unflattenable___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_unflattenable___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_flattened___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_flattened___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_flattened___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_flattened___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_maybeFlattened, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_final___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_final___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_final___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_final___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_final(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_initial___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_initial___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_initial___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_initial___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_initial(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_free___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_free___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_free___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_free___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_free(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_either(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_oneOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_oneOf___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_oneOf___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_oneOf___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnFailure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnHeight(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_softSpace___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_softSpace___closed__0;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_softSpace___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_softSpace___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_softSpace;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_append(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_join___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_join___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_join___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_join___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_fill___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_fill___redArg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_fill___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_fill___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_fillUsingSpace___redArg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0;
static const lean_array_object l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isCompoundAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isCompoundAtomic___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAtomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instAppend___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instAppend___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instAppend___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instAppend = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind;
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instBEqStickynessKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instBEqStickynessKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instBEqStickynessKind___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedSticky;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "TaggedDoc"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__3_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Sticky"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__3_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__3_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__3_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(205, 5, 96, 39, 91, 152, 112, 68)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNameSticky = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_sticky___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_sticky___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_sticky___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_sticky___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instCoeSep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeSep___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeSep___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___lam__0(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_pushElem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SelfDelimited"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(34, 26, 55, 159, 203, 232, 93, 63)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNameSelfDelimited = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value;
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isSelfDelimited___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isBracketed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isBracketed___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "RawFallback"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(140, 220, 156, 110, 255, 164, 127, 186)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNameRawFallback = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isRawFallback___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PseudoAligned"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(150, 251, 114, 148, 186, 139, 99, 103)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNamePseudoAligned = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_needsAppBrackets___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "PseudoDedented"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(219, 198, 72, 169, 175, 159, 157, 176)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNamePseudoDedented = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value;
static const lean_closure_object l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_propagateMetaData, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoDedented_x3f(lean_object*);
static lean_object* _init_l_Lean_Fmt_multiLineRawTagId(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(0u);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Fmt_firstSyntaxTagId(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(1u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object* v_doc_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v_doc_3_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(lean_object* v_freshTagId_6_, uint8_t v_kind_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_mk_empty_array_with_capacity(v___x_9_);
v___x_11_ = lean_array_push(v___x_10_, v_freshTagId_6_);
v___x_12_ = lean_box(v_kind_7_);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_11_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_32_; 
v_val_15_ = lean_ctor_get(v_x_8_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v_x_8_);
if (v_isSharedCheck_32_ == 0)
{
v___x_17_ = v_x_8_;
v_isShared_18_ = v_isSharedCheck_32_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_val_15_);
lean_dec(v_x_8_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_32_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_fst_19_; lean_object* v_snd_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_31_; 
v_fst_19_ = lean_ctor_get(v_val_15_, 0);
v_snd_20_ = lean_ctor_get(v_val_15_, 1);
v_isSharedCheck_31_ = !lean_is_exclusive(v_val_15_);
if (v_isSharedCheck_31_ == 0)
{
v___x_22_ = v_val_15_;
v_isShared_23_ = v_isSharedCheck_31_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_snd_20_);
lean_inc(v_fst_19_);
lean_dec(v_val_15_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_31_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_24_ = lean_array_push(v_fst_19_, v_freshTagId_6_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_24_);
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_snd_20_);
v___x_26_ = v_reuseFailAlloc_30_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_28_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v___x_26_);
v___x_28_ = v___x_17_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0___boxed(lean_object* v_freshTagId_33_, lean_object* v_kind_34_, lean_object* v_x_35_){
_start:
{
uint8_t v_kind_boxed_36_; lean_object* v_res_37_; 
v_kind_boxed_36_ = lean_unbox(v_kind_34_);
v_res_37_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(v_freshTagId_33_, v_kind_boxed_36_, v_x_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(lean_object* v_freshTagId_38_, uint8_t v_kind_39_, lean_object* v_a_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_val_44_; lean_object* v___x_45_; 
v___x_42_ = lean_box(0);
v___x_43_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(v_freshTagId_38_, v_kind_39_, v___x_42_);
v_val_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_val_44_);
lean_dec(v___x_43_);
v___x_45_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_45_, 0, v_a_40_);
lean_ctor_set(v___x_45_, 1, v_val_44_);
lean_ctor_set(v___x_45_, 2, v_x_41_);
return v___x_45_;
}
else
{
lean_object* v_key_46_; lean_object* v_value_47_; lean_object* v_tail_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_63_; 
v_key_46_ = lean_ctor_get(v_x_41_, 0);
v_value_47_ = lean_ctor_get(v_x_41_, 1);
v_tail_48_ = lean_ctor_get(v_x_41_, 2);
v_isSharedCheck_63_ = !lean_is_exclusive(v_x_41_);
if (v_isSharedCheck_63_ == 0)
{
v___x_50_ = v_x_41_;
v_isShared_51_ = v_isSharedCheck_63_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_tail_48_);
lean_inc(v_value_47_);
lean_inc(v_key_46_);
lean_dec(v_x_41_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_63_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
uint8_t v___x_52_; 
v___x_52_ = l_Lean_Syntax_instBEqRange_beq(v_key_46_, v_a_40_);
if (v___x_52_ == 0)
{
lean_object* v_tail_53_; lean_object* v___x_55_; 
v_tail_53_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_38_, v_kind_39_, v_a_40_, v_tail_48_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 2, v_tail_53_);
v___x_55_ = v___x_50_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_key_46_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_value_47_);
lean_ctor_set(v_reuseFailAlloc_56_, 2, v_tail_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
else
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v_val_59_; lean_object* v___x_61_; 
lean_dec(v_key_46_);
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v_value_47_);
v___x_58_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(v_freshTagId_38_, v_kind_39_, v___x_57_);
v_val_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_val_59_);
lean_dec(v___x_58_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 1, v_val_59_);
lean_ctor_set(v___x_50_, 0, v_a_40_);
v___x_61_ = v___x_50_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_40_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_val_59_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v_tail_48_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___boxed(lean_object* v_freshTagId_64_, lean_object* v_kind_65_, lean_object* v_a_66_, lean_object* v_x_67_){
_start:
{
uint8_t v_kind_boxed_68_; lean_object* v_res_69_; 
v_kind_boxed_68_ = lean_unbox(v_kind_65_);
v_res_69_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_64_, v_kind_boxed_68_, v_a_66_, v_x_67_);
return v_res_69_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(lean_object* v_a_70_, lean_object* v_x_71_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
else
{
lean_object* v_key_73_; lean_object* v_tail_74_; uint8_t v___x_75_; 
v_key_73_ = lean_ctor_get(v_x_71_, 0);
v_tail_74_ = lean_ctor_get(v_x_71_, 2);
v___x_75_ = l_Lean_Syntax_instBEqRange_beq(v_key_73_, v_a_70_);
if (v___x_75_ == 0)
{
v_x_71_ = v_tail_74_;
goto _start;
}
else
{
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg___boxed(lean_object* v_a_77_, lean_object* v_x_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_77_, v_x_78_);
lean_dec(v_x_78_);
lean_dec_ref(v_a_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
return v_x_81_;
}
else
{
lean_object* v_key_83_; lean_object* v_value_84_; lean_object* v_tail_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_108_; 
v_key_83_ = lean_ctor_get(v_x_82_, 0);
v_value_84_ = lean_ctor_get(v_x_82_, 1);
v_tail_85_ = lean_ctor_get(v_x_82_, 2);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_108_ == 0)
{
v___x_87_ = v_x_82_;
v_isShared_88_ = v_isSharedCheck_108_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_tail_85_);
lean_inc(v_value_84_);
lean_inc(v_key_83_);
lean_dec(v_x_82_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_108_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; uint64_t v_fold_93_; uint64_t v___x_94_; uint64_t v___x_95_; uint64_t v___x_96_; size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_89_ = lean_array_get_size(v_x_81_);
v___x_90_ = l_Lean_Syntax_instHashableRange_hash(v_key_83_);
v___x_91_ = 32ULL;
v___x_92_ = lean_uint64_shift_right(v___x_90_, v___x_91_);
v_fold_93_ = lean_uint64_xor(v___x_90_, v___x_92_);
v___x_94_ = 16ULL;
v___x_95_ = lean_uint64_shift_right(v_fold_93_, v___x_94_);
v___x_96_ = lean_uint64_xor(v_fold_93_, v___x_95_);
v___x_97_ = lean_uint64_to_usize(v___x_96_);
v___x_98_ = lean_usize_of_nat(v___x_89_);
v___x_99_ = ((size_t)1ULL);
v___x_100_ = lean_usize_sub(v___x_98_, v___x_99_);
v___x_101_ = lean_usize_land(v___x_97_, v___x_100_);
v___x_102_ = lean_array_uget_borrowed(v_x_81_, v___x_101_);
lean_inc(v___x_102_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 2, v___x_102_);
v___x_104_ = v___x_87_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_key_83_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_value_84_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v___x_102_);
v___x_104_ = v_reuseFailAlloc_107_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; 
v___x_105_ = lean_array_uset(v_x_81_, v___x_101_, v___x_104_);
v_x_81_ = v___x_105_;
v_x_82_ = v_tail_85_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(lean_object* v_i_109_, lean_object* v_source_110_, lean_object* v_target_111_){
_start:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_array_get_size(v_source_110_);
v___x_113_ = lean_nat_dec_lt(v_i_109_, v___x_112_);
if (v___x_113_ == 0)
{
lean_dec_ref(v_source_110_);
lean_dec(v_i_109_);
return v_target_111_;
}
else
{
lean_object* v_es_114_; lean_object* v___x_115_; lean_object* v_source_116_; lean_object* v_target_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_es_114_ = lean_array_fget(v_source_110_, v_i_109_);
v___x_115_ = lean_box(0);
v_source_116_ = lean_array_fset(v_source_110_, v_i_109_, v___x_115_);
v_target_117_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(v_target_111_, v_es_114_);
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_add(v_i_109_, v___x_118_);
lean_dec(v_i_109_);
v_i_109_ = v___x_119_;
v_source_110_ = v_source_116_;
v_target_111_ = v_target_117_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(lean_object* v_data_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_nbuckets_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_122_ = lean_array_get_size(v_data_121_);
v___x_123_ = lean_unsigned_to_nat(2u);
v_nbuckets_124_ = lean_nat_mul(v___x_122_, v___x_123_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_box(0);
v___x_127_ = lean_mk_array(v_nbuckets_124_, v___x_126_);
v___x_128_ = lean_array_propagate_mark(v_data_121_, v___x_127_);
v___x_129_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(v___x_125_, v_data_121_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(lean_object* v_freshTagId_130_, uint8_t v_kind_131_, lean_object* v_m_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_size_134_; lean_object* v_buckets_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_187_; 
v_size_134_ = lean_ctor_get(v_m_132_, 0);
v_buckets_135_ = lean_ctor_get(v_m_132_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_m_132_);
if (v_isSharedCheck_187_ == 0)
{
v___x_137_ = v_m_132_;
v_isShared_138_ = v_isSharedCheck_187_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_buckets_135_);
lean_inc(v_size_134_);
lean_dec(v_m_132_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_187_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v_fold_143_; uint64_t v___x_144_; uint64_t v___x_145_; uint64_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; size_t v___x_151_; lean_object* v_bkt_152_; uint8_t v___x_153_; 
v___x_139_ = lean_array_get_size(v_buckets_135_);
v___x_140_ = l_Lean_Syntax_instHashableRange_hash(v_a_133_);
v___x_141_ = 32ULL;
v___x_142_ = lean_uint64_shift_right(v___x_140_, v___x_141_);
v_fold_143_ = lean_uint64_xor(v___x_140_, v___x_142_);
v___x_144_ = 16ULL;
v___x_145_ = lean_uint64_shift_right(v_fold_143_, v___x_144_);
v___x_146_ = lean_uint64_xor(v_fold_143_, v___x_145_);
v___x_147_ = lean_uint64_to_usize(v___x_146_);
v___x_148_ = lean_usize_of_nat(v___x_139_);
v___x_149_ = ((size_t)1ULL);
v___x_150_ = lean_usize_sub(v___x_148_, v___x_149_);
v___x_151_ = lean_usize_land(v___x_147_, v___x_150_);
v_bkt_152_ = lean_array_uget_borrowed(v_buckets_135_, v___x_151_);
v___x_153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_133_, v_bkt_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_size_x27_159_; lean_object* v___x_160_; lean_object* v_buckets_x27_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_mk_empty_array_with_capacity(v___x_154_);
v___x_156_ = lean_array_push(v___x_155_, v_freshTagId_130_);
v___x_157_ = lean_box(v_kind_131_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v_size_x27_159_ = lean_nat_add(v_size_134_, v___x_154_);
lean_dec(v_size_134_);
lean_inc(v_bkt_152_);
v___x_160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_160_, 0, v_a_133_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v_bkt_152_);
v_buckets_x27_161_ = lean_array_uset(v_buckets_135_, v___x_151_, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(4u);
v___x_163_ = lean_nat_mul(v_size_x27_159_, v___x_162_);
v___x_164_ = lean_unsigned_to_nat(3u);
v___x_165_ = lean_nat_div(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_array_get_size(v_buckets_x27_161_);
v___x_167_ = lean_nat_dec_le(v___x_165_, v___x_166_);
lean_dec(v___x_165_);
if (v___x_167_ == 0)
{
lean_object* v_val_168_; lean_object* v___x_170_; 
v_val_168_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(v_buckets_x27_161_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v_val_168_);
lean_ctor_set(v___x_137_, 0, v_size_x27_159_);
v___x_170_ = v___x_137_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_x27_159_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_val_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_object* v___x_173_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v_buckets_x27_161_);
lean_ctor_set(v___x_137_, 0, v_size_x27_159_);
v___x_173_ = v___x_137_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_size_x27_159_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_buckets_x27_161_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
else
{
lean_object* v___x_175_; lean_object* v_buckets_x27_176_; lean_object* v_bkt_x27_177_; lean_object* v___y_179_; uint8_t v___x_184_; 
lean_inc(v_bkt_152_);
v___x_175_ = lean_box(0);
v_buckets_x27_176_ = lean_array_uset(v_buckets_135_, v___x_151_, v___x_175_);
lean_inc_ref(v_a_133_);
v_bkt_x27_177_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_130_, v_kind_131_, v_a_133_, v_bkt_152_);
v___x_184_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_133_, v_bkt_x27_177_);
lean_dec_ref(v_a_133_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_sub(v_size_134_, v___x_185_);
lean_dec(v_size_134_);
v___y_179_ = v___x_186_;
goto v___jp_178_;
}
else
{
v___y_179_ = v_size_134_;
goto v___jp_178_;
}
v___jp_178_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = lean_array_uset(v_buckets_x27_176_, v___x_151_, v_bkt_x27_177_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_180_);
lean_ctor_set(v___x_137_, 0, v___y_179_);
v___x_182_ = v___x_137_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___y_179_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0___boxed(lean_object* v_freshTagId_188_, lean_object* v_kind_189_, lean_object* v_m_190_, lean_object* v_a_191_){
_start:
{
uint8_t v_kind_boxed_192_; lean_object* v_res_193_; 
v_kind_boxed_192_ = lean_unbox(v_kind_189_);
v_res_193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(v_freshTagId_188_, v_kind_boxed_192_, v_m_190_, v_a_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange(lean_object* v_freshTagId_194_, lean_object* v_tags_195_, lean_object* v_doc_196_, lean_object* v_range_197_, uint8_t v_kind_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_doc_201_; lean_object* v_tags_202_; lean_object* v___x_203_; lean_object* v_freshTagId_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_inc_n(v_freshTagId_194_, 2);
v___x_199_ = l_Lean_Fmt_Doc_tagged___override___redArg(v_freshTagId_194_, v_doc_196_);
v___x_200_ = lean_box(0);
v_doc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_doc_201_, 0, v___x_199_);
lean_ctor_set(v_doc_201_, 1, v___x_200_);
v_tags_202_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(v_freshTagId_194_, v_kind_198_, v_tags_195_, v_range_197_);
v___x_203_ = lean_unsigned_to_nat(1u);
v_freshTagId_204_ = lean_nat_add(v_freshTagId_194_, v___x_203_);
lean_dec(v_freshTagId_194_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v_tags_202_);
lean_ctor_set(v___x_205_, 1, v_doc_201_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_freshTagId_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange___boxed(lean_object* v_freshTagId_207_, lean_object* v_tags_208_, lean_object* v_doc_209_, lean_object* v_range_210_, lean_object* v_kind_211_){
_start:
{
uint8_t v_kind_boxed_212_; lean_object* v_res_213_; 
v_kind_boxed_212_ = lean_unbox(v_kind_211_);
v_res_213_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_207_, v_tags_208_, v_doc_209_, v_range_210_, v_kind_boxed_212_);
return v_res_213_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(lean_object* v_00_u03b2_214_, lean_object* v_a_215_, lean_object* v_x_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___boxed(lean_object* v_00_u03b2_218_, lean_object* v_a_219_, lean_object* v_x_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(v_00_u03b2_218_, v_a_219_, v_x_220_);
lean_dec(v_x_220_);
lean_dec_ref(v_a_219_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1(lean_object* v_00_u03b2_223_, lean_object* v_data_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(v_data_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_226_, lean_object* v_i_227_, lean_object* v_source_228_, lean_object* v_target_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(v_i_227_, v_source_228_, v_target_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(v_x_232_, v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object* v_doc_235_, lean_object* v_ref_236_, lean_object* v_a_237_){
_start:
{
uint8_t v___x_238_; lean_object* v___x_239_; 
v___x_238_ = 0;
v___x_239_ = l_Lean_Syntax_getRange_x3f(v_ref_236_, v___x_238_);
if (lean_obj_tag(v___x_239_) == 1)
{
lean_object* v_val_240_; lean_object* v_toBacktrackableState_241_; lean_object* v_shareCommonState_242_; lean_object* v_freshTagId_243_; lean_object* v_missingFormatters_244_; lean_object* v_partialFormatters_245_; lean_object* v_missingChoiceResolutions_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_266_; 
v_val_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v___x_239_, 1);
v_toBacktrackableState_241_ = lean_ctor_get(v_a_237_, 0);
v_shareCommonState_242_ = lean_ctor_get(v_a_237_, 1);
v_freshTagId_243_ = lean_ctor_get(v_a_237_, 2);
v_missingFormatters_244_ = lean_ctor_get(v_a_237_, 3);
v_partialFormatters_245_ = lean_ctor_get(v_a_237_, 4);
v_missingChoiceResolutions_246_ = lean_ctor_get(v_a_237_, 5);
v_isSharedCheck_266_ = !lean_is_exclusive(v_a_237_);
if (v_isSharedCheck_266_ == 0)
{
v___x_248_ = v_a_237_;
v_isShared_249_ = v_isSharedCheck_266_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_missingChoiceResolutions_246_);
lean_inc(v_partialFormatters_245_);
lean_inc(v_missingFormatters_244_);
lean_inc(v_freshTagId_243_);
lean_inc(v_shareCommonState_242_);
lean_inc(v_toBacktrackableState_241_);
lean_dec(v_a_237_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_266_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v_snd_252_; lean_object* v_fst_253_; lean_object* v_fst_254_; lean_object* v_snd_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_265_; 
v___x_250_ = 2;
v___x_251_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_243_, v_toBacktrackableState_241_, v_doc_235_, v_val_240_, v___x_250_);
v_snd_252_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_snd_252_);
v_fst_253_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_fst_253_);
lean_dec_ref(v___x_251_);
v_fst_254_ = lean_ctor_get(v_snd_252_, 0);
v_snd_255_ = lean_ctor_get(v_snd_252_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_snd_252_);
if (v_isSharedCheck_265_ == 0)
{
v___x_257_ = v_snd_252_;
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_snd_255_);
lean_inc(v_fst_254_);
lean_dec(v_snd_252_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 2, v_fst_253_);
lean_ctor_set(v___x_248_, 0, v_fst_254_);
v___x_260_ = v___x_248_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_fst_254_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_shareCommonState_242_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v_fst_253_);
lean_ctor_set(v_reuseFailAlloc_264_, 3, v_missingFormatters_244_);
lean_ctor_set(v_reuseFailAlloc_264_, 4, v_partialFormatters_245_);
lean_ctor_set(v_reuseFailAlloc_264_, 5, v_missingChoiceResolutions_246_);
v___x_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_260_);
lean_ctor_set(v___x_257_, 0, v_snd_255_);
v___x_262_ = v___x_257_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_snd_255_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v___x_239_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_doc_235_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_a_237_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg___boxed(lean_object* v_doc_270_, lean_object* v_ref_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_doc_270_, v_ref_271_, v_a_272_);
lean_dec(v_ref_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText(lean_object* v_doc_274_, lean_object* v_ref_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_doc_274_, v_ref_275_, v_a_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___boxed(lean_object* v_doc_279_, lean_object* v_ref_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Fmt_TaggedDoc_taggedText(v_doc_279_, v_ref_280_, v_a_281_, v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_ref_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object* v_doc_284_, lean_object* v_ref_285_, lean_object* v_a_286_){
_start:
{
uint8_t v___x_287_; lean_object* v___x_288_; 
v___x_287_ = 0;
v___x_288_ = l_Lean_Syntax_getRange_x3f(v_ref_285_, v___x_287_);
if (lean_obj_tag(v___x_288_) == 1)
{
lean_object* v_val_289_; lean_object* v_toBacktrackableState_290_; lean_object* v_shareCommonState_291_; lean_object* v_freshTagId_292_; lean_object* v_missingFormatters_293_; lean_object* v_partialFormatters_294_; lean_object* v_missingChoiceResolutions_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_315_; 
v_val_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_val_289_);
lean_dec_ref_known(v___x_288_, 1);
v_toBacktrackableState_290_ = lean_ctor_get(v_a_286_, 0);
v_shareCommonState_291_ = lean_ctor_get(v_a_286_, 1);
v_freshTagId_292_ = lean_ctor_get(v_a_286_, 2);
v_missingFormatters_293_ = lean_ctor_get(v_a_286_, 3);
v_partialFormatters_294_ = lean_ctor_get(v_a_286_, 4);
v_missingChoiceResolutions_295_ = lean_ctor_get(v_a_286_, 5);
v_isSharedCheck_315_ = !lean_is_exclusive(v_a_286_);
if (v_isSharedCheck_315_ == 0)
{
v___x_297_ = v_a_286_;
v_isShared_298_ = v_isSharedCheck_315_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_missingChoiceResolutions_295_);
lean_inc(v_partialFormatters_294_);
lean_inc(v_missingFormatters_293_);
lean_inc(v_freshTagId_292_);
lean_inc(v_shareCommonState_291_);
lean_inc(v_toBacktrackableState_290_);
lean_dec(v_a_286_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_315_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v_snd_301_; lean_object* v_fst_302_; lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_314_; 
v___x_299_ = 1;
v___x_300_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_292_, v_toBacktrackableState_290_, v_doc_284_, v_val_289_, v___x_299_);
v_snd_301_ = lean_ctor_get(v___x_300_, 1);
lean_inc(v_snd_301_);
v_fst_302_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_fst_302_);
lean_dec_ref(v___x_300_);
v_fst_303_ = lean_ctor_get(v_snd_301_, 0);
v_snd_304_ = lean_ctor_get(v_snd_301_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_snd_301_);
if (v_isSharedCheck_314_ == 0)
{
v___x_306_ = v_snd_301_;
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_snd_304_);
lean_inc(v_fst_303_);
lean_dec(v_snd_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v_fst_302_);
lean_ctor_set(v___x_297_, 0, v_fst_303_);
v___x_309_ = v___x_297_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_fst_303_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_shareCommonState_291_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_fst_302_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_missingFormatters_293_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_partialFormatters_294_);
lean_ctor_set(v_reuseFailAlloc_313_, 5, v_missingChoiceResolutions_295_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___x_309_);
lean_ctor_set(v___x_306_, 0, v_snd_304_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_snd_304_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v___x_288_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_doc_284_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_a_286_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg___boxed(lean_object* v_doc_319_, lean_object* v_ref_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_319_, v_ref_320_, v_a_321_);
lean_dec(v_ref_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode(lean_object* v_doc_323_, lean_object* v_ref_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_323_, v_ref_324_, v_a_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___boxed(lean_object* v_doc_328_, lean_object* v_ref_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Fmt_TaggedDoc_taggedNode(v_doc_328_, v_ref_329_, v_a_330_, v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_ref_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedRaw___redArg(lean_object* v_doc_333_, lean_object* v_ref_334_, lean_object* v_a_335_){
_start:
{
uint8_t v___x_336_; lean_object* v___x_337_; 
v___x_336_ = 0;
v___x_337_ = l_Lean_Syntax_getRange_x3f(v_ref_334_, v___x_336_);
if (lean_obj_tag(v___x_337_) == 1)
{
lean_object* v_val_338_; lean_object* v_toBacktrackableState_339_; lean_object* v_shareCommonState_340_; lean_object* v_freshTagId_341_; lean_object* v_missingFormatters_342_; lean_object* v_partialFormatters_343_; lean_object* v_missingChoiceResolutions_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_364_; 
v_val_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_val_338_);
lean_dec_ref_known(v___x_337_, 1);
v_toBacktrackableState_339_ = lean_ctor_get(v_a_335_, 0);
v_shareCommonState_340_ = lean_ctor_get(v_a_335_, 1);
v_freshTagId_341_ = lean_ctor_get(v_a_335_, 2);
v_missingFormatters_342_ = lean_ctor_get(v_a_335_, 3);
v_partialFormatters_343_ = lean_ctor_get(v_a_335_, 4);
v_missingChoiceResolutions_344_ = lean_ctor_get(v_a_335_, 5);
v_isSharedCheck_364_ = !lean_is_exclusive(v_a_335_);
if (v_isSharedCheck_364_ == 0)
{
v___x_346_ = v_a_335_;
v_isShared_347_ = v_isSharedCheck_364_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_missingChoiceResolutions_344_);
lean_inc(v_partialFormatters_343_);
lean_inc(v_missingFormatters_342_);
lean_inc(v_freshTagId_341_);
lean_inc(v_shareCommonState_340_);
lean_inc(v_toBacktrackableState_339_);
lean_dec(v_a_335_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_364_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v_snd_350_; lean_object* v_fst_351_; lean_object* v_fst_352_; lean_object* v_snd_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_363_; 
v___x_348_ = 3;
v___x_349_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_341_, v_toBacktrackableState_339_, v_doc_333_, v_val_338_, v___x_348_);
v_snd_350_ = lean_ctor_get(v___x_349_, 1);
lean_inc(v_snd_350_);
v_fst_351_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_fst_351_);
lean_dec_ref(v___x_349_);
v_fst_352_ = lean_ctor_get(v_snd_350_, 0);
v_snd_353_ = lean_ctor_get(v_snd_350_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_snd_350_);
if (v_isSharedCheck_363_ == 0)
{
v___x_355_ = v_snd_350_;
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_snd_353_);
lean_inc(v_fst_352_);
lean_dec(v_snd_350_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 2, v_fst_351_);
lean_ctor_set(v___x_346_, 0, v_fst_352_);
v___x_358_ = v___x_346_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_fst_352_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_shareCommonState_340_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_fst_351_);
lean_ctor_set(v_reuseFailAlloc_362_, 3, v_missingFormatters_342_);
lean_ctor_set(v_reuseFailAlloc_362_, 4, v_partialFormatters_343_);
lean_ctor_set(v_reuseFailAlloc_362_, 5, v_missingChoiceResolutions_344_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v___x_358_);
lean_ctor_set(v___x_355_, 0, v_snd_353_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_snd_353_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v___x_337_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_doc_333_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_a_335_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedRaw___redArg___boxed(lean_object* v_doc_368_, lean_object* v_ref_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Fmt_TaggedDoc_taggedRaw___redArg(v_doc_368_, v_ref_369_, v_a_370_);
lean_dec(v_ref_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedRaw(lean_object* v_doc_372_, lean_object* v_ref_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Fmt_TaggedDoc_taggedRaw___redArg(v_doc_372_, v_ref_373_, v_a_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedRaw___boxed(lean_object* v_doc_377_, lean_object* v_ref_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Fmt_TaggedDoc_taggedRaw(v_doc_377_, v_ref_378_, v_a_379_, v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_ref_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(lean_object* v_doc_382_, lean_object* v_range_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_toBacktrackableState_385_; lean_object* v_shareCommonState_386_; lean_object* v_freshTagId_387_; lean_object* v_missingFormatters_388_; lean_object* v_partialFormatters_389_; lean_object* v_missingChoiceResolutions_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_410_; 
v_toBacktrackableState_385_ = lean_ctor_get(v_a_384_, 0);
v_shareCommonState_386_ = lean_ctor_get(v_a_384_, 1);
v_freshTagId_387_ = lean_ctor_get(v_a_384_, 2);
v_missingFormatters_388_ = lean_ctor_get(v_a_384_, 3);
v_partialFormatters_389_ = lean_ctor_get(v_a_384_, 4);
v_missingChoiceResolutions_390_ = lean_ctor_get(v_a_384_, 5);
v_isSharedCheck_410_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_410_ == 0)
{
v___x_392_ = v_a_384_;
v_isShared_393_ = v_isSharedCheck_410_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_missingChoiceResolutions_390_);
lean_inc(v_partialFormatters_389_);
lean_inc(v_missingFormatters_388_);
lean_inc(v_freshTagId_387_);
lean_inc(v_shareCommonState_386_);
lean_inc(v_toBacktrackableState_385_);
lean_dec(v_a_384_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_410_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v_snd_396_; lean_object* v_fst_397_; lean_object* v_fst_398_; lean_object* v_snd_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v___x_394_ = 0;
v___x_395_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_387_, v_toBacktrackableState_385_, v_doc_382_, v_range_383_, v___x_394_);
v_snd_396_ = lean_ctor_get(v___x_395_, 1);
lean_inc(v_snd_396_);
v_fst_397_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_fst_397_);
lean_dec_ref(v___x_395_);
v_fst_398_ = lean_ctor_get(v_snd_396_, 0);
v_snd_399_ = lean_ctor_get(v_snd_396_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_snd_396_);
if (v_isSharedCheck_409_ == 0)
{
v___x_401_ = v_snd_396_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_snd_399_);
lean_inc(v_fst_398_);
lean_dec(v_snd_396_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 2, v_fst_397_);
lean_ctor_set(v___x_392_, 0, v_fst_398_);
v___x_404_ = v___x_392_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_fst_398_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_shareCommonState_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_fst_397_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_missingFormatters_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_partialFormatters_389_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_missingChoiceResolutions_390_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v___x_404_);
lean_ctor_set(v___x_401_, 0, v_snd_399_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_snd_399_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace(lean_object* v_doc_411_, lean_object* v_range_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(v_doc_411_, v_range_412_, v_a_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___boxed(lean_object* v_doc_416_, lean_object* v_range_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace(v_doc_416_, v_range_417_, v_a_418_, v_a_419_);
lean_dec_ref(v_a_418_);
return v_res_420_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isTagged(lean_object* v_d_421_){
_start:
{
lean_object* v_doc_422_; 
v_doc_422_ = lean_ctor_get(v_d_421_, 0);
if (lean_obj_tag(v_doc_422_) == 3)
{
uint8_t v___x_423_; 
v___x_423_ = 1;
return v___x_423_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isTagged___boxed(lean_object* v_d_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l_Lean_Fmt_TaggedDoc_isTagged(v_d_425_);
lean_dec_ref(v_d_425_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_markMultiLineRaw(lean_object* v_d_428_){
_start:
{
lean_object* v_doc_429_; lean_object* v_metaData_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_439_; 
v_doc_429_ = lean_ctor_get(v_d_428_, 0);
v_metaData_430_ = lean_ctor_get(v_d_428_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_d_428_);
if (v_isSharedCheck_439_ == 0)
{
v___x_432_ = v_d_428_;
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_metaData_430_);
lean_inc(v_doc_429_);
lean_dec(v_d_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = l_Lean_Fmt_Doc_tagged___override___redArg(v___x_434_, v_doc_429_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_435_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_metaData_430_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg(lean_object* v_d_440_, lean_object* v_ref_441_, lean_object* v_a_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = l_Lean_Fmt_TaggedDoc_isTagged(v_d_440_);
if (v___x_443_ == 0)
{
lean_object* v_doc_444_; lean_object* v_metaData_445_; lean_object* v___x_446_; lean_object* v_a_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_464_; 
v_doc_444_ = lean_ctor_get(v_d_440_, 0);
lean_inc(v_doc_444_);
v_metaData_445_ = lean_ctor_get(v_d_440_, 1);
lean_inc(v_metaData_445_);
lean_dec_ref(v_d_440_);
v___x_446_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_444_, v_ref_441_, v_a_442_);
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_a_448_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_464_ == 0)
{
v___x_450_ = v___x_446_;
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_doc_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_462_; 
v_doc_452_ = lean_ctor_get(v_a_447_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_447_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v_a_447_, 1);
lean_dec(v_unused_463_);
v___x_454_ = v_a_447_;
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_doc_452_);
lean_dec(v_a_447_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v_metaData_445_);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_doc_452_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_metaData_445_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_457_);
v___x_459_ = v___x_450_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_a_448_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
else
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v_d_440_);
lean_ctor_set(v___x_465_, 1, v_a_442_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg___boxed(lean_object* v_d_466_, lean_object* v_ref_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_d_466_, v_ref_467_, v_a_468_);
lean_dec(v_ref_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag(lean_object* v_d_470_, lean_object* v_ref_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_d_470_, v_ref_471_, v_a_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___boxed(lean_object* v_d_475_, lean_object* v_ref_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Fmt_TaggedDoc_tag(v_d_475_, v_ref_476_, v_a_477_, v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_ref_476_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(lean_object* v_inst_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_v_482_; lean_object* v___x_483_; 
v_v_482_ = lean_ctor_get(v_x_481_, 0);
v___x_483_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_v_482_, v_inst_480_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed(lean_object* v_inst_484_, lean_object* v_x_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(v_inst_484_, v_x_485_);
lean_dec_ref(v_x_485_);
lean_dec(v_inst_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(lean_object* v_inst_487_, lean_object* v_d_488_){
_start:
{
lean_object* v_metaData_489_; lean_object* v___f_490_; lean_object* v___x_491_; 
v_metaData_489_ = lean_ctor_get(v_d_488_, 1);
lean_inc(v_metaData_489_);
lean_dec_ref(v_d_488_);
v___f_490_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_490_, 0, v_inst_487_);
v___x_491_ = l_List_findSome_x3f___redArg(v___f_490_, v_metaData_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f(lean_object* v_00_u03b1_492_, lean_object* v_inst_493_, lean_object* v_d_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v_inst_493_, v_d_494_);
return v___x_495_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_499_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2));
v___x_500_ = lean_unsigned_to_nat(14u);
v___x_501_ = lean_unsigned_to_nat(22u);
v___x_502_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1));
v___x_503_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0));
v___x_504_ = l_mkPanicMessageWithDecl(v___x_503_, v___x_502_, v___x_501_, v___x_500_, v___x_499_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_propagate_507_, lean_object* v_v_508_, lean_object* v_f_509_){
_start:
{
lean_object* v___y_511_; lean_object* v___x_514_; 
v___x_514_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_v_508_, v_inst_506_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3);
v___x_516_ = l_panic___redArg(v_inst_505_, v___x_515_);
v___y_511_ = v___x_516_;
goto v___jp_510_;
}
else
{
lean_object* v_val_517_; 
v_val_517_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v___x_514_, 1);
v___y_511_ = v_val_517_;
goto v___jp_510_;
}
v___jp_510_:
{
lean_object* v_r_512_; lean_object* v___x_513_; 
v_r_512_ = lean_apply_2(v_propagate_507_, v___y_511_, v_f_509_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_inst_506_);
lean_ctor_set(v___x_513_, 1, v_r_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___boxed(lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_propagate_520_, lean_object* v_v_521_, lean_object* v_f_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(v_inst_518_, v_inst_519_, v_propagate_520_, v_v_521_, v_f_522_);
lean_dec(v_v_521_);
lean_dec(v_inst_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(lean_object* v_00_u03b1_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_propagate_527_, lean_object* v_v_528_, lean_object* v_f_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(v_inst_525_, v_inst_526_, v_propagate_527_, v_v_528_, v_f_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed(lean_object* v_00_u03b1_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_propagate_534_, lean_object* v_v_535_, lean_object* v_f_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(v_00_u03b1_531_, v_inst_532_, v_inst_533_, v_propagate_534_, v_v_535_, v_f_536_);
lean_dec(v_v_535_);
lean_dec(v_inst_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData___redArg(lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_d_540_, lean_object* v_metaData_541_, lean_object* v_propagate_542_){
_start:
{
lean_object* v_doc_543_; lean_object* v_metaData_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_555_; 
v_doc_543_ = lean_ctor_get(v_d_540_, 0);
v_metaData_544_ = lean_ctor_get(v_d_540_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_d_540_);
if (v_isSharedCheck_555_ == 0)
{
v___x_546_ = v_d_540_;
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_metaData_544_);
lean_inc(v_doc_543_);
lean_dec(v_d_540_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
lean_inc(v_inst_539_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_inst_539_);
lean_ctor_set(v___x_548_, 1, v_metaData_541_);
v___x_549_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed), 6, 4);
lean_closure_set(v___x_549_, 0, lean_box(0));
lean_closure_set(v___x_549_, 1, v_inst_538_);
lean_closure_set(v___x_549_, 2, v_inst_539_);
lean_closure_set(v___x_549_, 3, v_propagate_542_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_metaData_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_551_);
v___x_553_ = v___x_546_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_doc_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData(lean_object* v_00_u03b1_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_d_559_, lean_object* v_metaData_560_, lean_object* v_propagate_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v_inst_557_, v_inst_558_, v_d_559_, v_metaData_560_, v_propagate_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(lean_object* v_f_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
if (lean_obj_tag(v_a_564_) == 0)
{
lean_object* v___x_566_; 
lean_dec_ref(v_f_563_);
v___x_566_ = l_List_reverse___redArg(v_a_565_);
return v___x_566_;
}
else
{
lean_object* v_head_567_; lean_object* v_tail_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_586_; 
v_head_567_ = lean_ctor_get(v_a_564_, 0);
v_tail_568_ = lean_ctor_get(v_a_564_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_a_564_);
if (v_isSharedCheck_586_ == 0)
{
v___x_570_ = v_a_564_;
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_tail_568_);
lean_inc(v_head_567_);
lean_dec(v_a_564_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_v_572_; lean_object* v_propagate_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_585_; 
v_v_572_ = lean_ctor_get(v_head_567_, 0);
v_propagate_573_ = lean_ctor_get(v_head_567_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_head_567_);
if (v_isSharedCheck_585_ == 0)
{
v___x_575_ = v_head_567_;
v_isShared_576_ = v_isSharedCheck_585_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_propagate_573_);
lean_inc(v_v_572_);
lean_dec(v_head_567_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_585_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_579_; 
lean_inc(v_propagate_573_);
lean_inc_ref(v_f_563_);
v___x_577_ = lean_apply_2(v_propagate_573_, v_v_572_, v_f_563_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_577_);
v___x_579_ = v___x_575_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_propagate_573_);
v___x_579_ = v_reuseFailAlloc_584_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v_a_565_);
lean_ctor_set(v___x_570_, 0, v___x_579_);
v___x_581_ = v___x_570_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_a_565_);
v___x_581_ = v_reuseFailAlloc_583_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
v_a_564_ = v_tail_568_;
v_a_565_ = v___x_581_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateMetaData(lean_object* v_d_587_, lean_object* v_f_588_){
_start:
{
lean_object* v_doc_589_; lean_object* v_metaData_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_600_; 
v_doc_589_ = lean_ctor_get(v_d_587_, 0);
v_metaData_590_ = lean_ctor_get(v_d_587_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_d_587_);
if (v_isSharedCheck_600_ == 0)
{
v___x_592_ = v_d_587_;
v_isShared_593_ = v_isSharedCheck_600_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_metaData_590_);
lean_inc(v_doc_589_);
lean_dec(v_d_587_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_600_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
lean_inc_ref(v_f_588_);
v___x_594_ = lean_apply_1(v_f_588_, v_doc_589_);
v___x_595_ = lean_box(0);
v___x_596_ = l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(v_f_588_, v_metaData_590_, v___x_595_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_596_);
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(size_t v_sz_601_, size_t v_i_602_, lean_object* v_bs_603_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_lt(v_i_602_, v_sz_601_);
if (v___x_604_ == 0)
{
return v_bs_603_;
}
else
{
lean_object* v_v_605_; lean_object* v_doc_606_; lean_object* v___x_607_; lean_object* v_bs_x27_608_; size_t v___x_609_; size_t v___x_610_; lean_object* v___x_611_; 
v_v_605_ = lean_array_uget_borrowed(v_bs_603_, v_i_602_);
v_doc_606_ = lean_ctor_get(v_v_605_, 0);
lean_inc(v_doc_606_);
v___x_607_ = lean_unsigned_to_nat(0u);
v_bs_x27_608_ = lean_array_uset(v_bs_603_, v_i_602_, v___x_607_);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_add(v_i_602_, v___x_609_);
v___x_611_ = lean_array_uset(v_bs_x27_608_, v_i_602_, v_doc_606_);
v_i_602_ = v___x_610_;
v_bs_603_ = v___x_611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0___boxed(lean_object* v_sz_613_, lean_object* v_i_614_, lean_object* v_bs_615_){
_start:
{
size_t v_sz_boxed_616_; size_t v_i_boxed_617_; lean_object* v_res_618_; 
v_sz_boxed_616_ = lean_unbox_usize(v_sz_613_);
lean_dec(v_sz_613_);
v_i_boxed_617_ = lean_unbox_usize(v_i_614_);
lean_dec(v_i_614_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_boxed_616_, v_i_boxed_617_, v_bs_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(lean_object* v_ds_619_, lean_object* v_f_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = lean_array_get_size(v_ds_619_);
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_dec_eq(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
size_t v_sz_624_; size_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_sz_624_ = lean_array_size(v_ds_619_);
v___x_625_ = ((size_t)0ULL);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_624_, v___x_625_, v_ds_619_);
v___x_627_ = lean_apply_1(v_f_620_, v___x_626_);
v___x_628_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_627_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec_ref(v_f_620_);
v___x_629_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_array_get(v___x_629_, v_ds_619_, v___x_630_);
lean_dec_ref(v_ds_619_);
return v___x_631_;
}
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_failure___closed__0(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_box(0);
v___x_633_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_failure(void){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_failure___closed__0, &l_Lean_Fmt_TaggedDoc_failure___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_failure___closed__0);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_newline(lean_object* v_flattened_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = l_Lean_Fmt_Doc_newline___override___redArg(v_flattened_635_);
v___x_637_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl___closed__0(void){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Fmt_Doc_nl___redArg();
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl___closed__1(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_nl___closed__0, &l_Lean_Fmt_TaggedDoc_nl___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_nl___closed__0);
v___x_640_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_nl___closed__1, &l_Lean_Fmt_TaggedDoc_nl___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_nl___closed__1);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break___closed__0(void){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Fmt_Doc_break___redArg();
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break___closed__1(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_break___closed__0, &l_Lean_Fmt_TaggedDoc_break___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_break___closed__0);
v___x_644_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break(void){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_break___closed__1, &l_Lean_Fmt_TaggedDoc_break___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_break___closed__1);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__0(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__1(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_hardNl___closed__0, &l_Lean_Fmt_TaggedDoc_hardNl___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__0);
v___x_648_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl(void){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_hardNl___closed__1, &l_Lean_Fmt_TaggedDoc_hardNl___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__1);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object* v_s_650_, lean_object* v_ref_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_650_);
v___x_654_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_653_, v_ref_651_, v_a_652_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg___boxed(lean_object* v_s_655_, lean_object* v_ref_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Fmt_TaggedDoc_text___redArg(v_s_655_, v_ref_656_, v_a_657_);
lean_dec(v_ref_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text(lean_object* v_s_659_, lean_object* v_ref_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_Fmt_TaggedDoc_text___redArg(v_s_659_, v_ref_660_, v_a_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___boxed(lean_object* v_s_664_, lean_object* v_ref_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Fmt_TaggedDoc_text(v_s_664_, v_ref_665_, v_a_666_, v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_ref_665_);
return v_res_668_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty___closed__0(void){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Fmt_Doc_empty___redArg();
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty___closed__1(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_empty___closed__0, &l_Lean_Fmt_TaggedDoc_empty___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_empty___closed__0);
v___x_671_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty(void){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_empty___closed__1, &l_Lean_Fmt_TaggedDoc_empty___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_empty___closed__1);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space___closed__1(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_space___closed__0));
v___x_675_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space___closed__2(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_space___closed__1, &l_Lean_Fmt_TaggedDoc_space___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_space___closed__1);
v___x_677_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space(void){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_space___closed__2, &l_Lean_Fmt_TaggedDoc_space___closed__2_once, _init_l_Lean_Fmt_TaggedDoc_space___closed__2);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object* v_d_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_nested___closed__0));
v___x_682_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_680_, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object* v_d_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_hardNested___closed__0));
v___x_686_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_684_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_doublyNested(lean_object* v_d_687_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = l_Lean_Fmt_TaggedDoc_nested(v_d_687_);
v___x_689_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object* v_d_690_){
_start:
{
lean_object* v_doc_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_doc_691_ = lean_ctor_get(v_d_690_, 0);
lean_inc(v_doc_691_);
lean_dec_ref(v_d_690_);
v___x_692_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_691_);
v___x_693_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object* v_d_695_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; 
v___f_696_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_unflattenable___closed__0));
v___x_697_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_695_, v___f_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object* v_d_699_){
_start:
{
lean_object* v___f_700_; lean_object* v___x_701_; 
v___f_700_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_flattened___closed__0));
v___x_701_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_699_, v___f_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object* v_d_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0));
v___x_705_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_703_, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0(uint8_t v_onlyNonCumulative_706_, lean_object* v_d_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_706_, v_d_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed(lean_object* v_onlyNonCumulative_709_, lean_object* v_d_710_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_711_; lean_object* v_res_712_; 
v_onlyNonCumulative_boxed_711_ = lean_unbox(v_onlyNonCumulative_709_);
v_res_712_ = l_Lean_Fmt_TaggedDoc_unindented___lam__0(v_onlyNonCumulative_boxed_711_, v_d_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object* v_d_713_, uint8_t v_onlyNonCumulative_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___f_716_; lean_object* v___x_717_; 
v___x_715_ = lean_box(v_onlyNonCumulative_714_);
v___f_716_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed), 2, 1);
lean_closure_set(v___f_716_, 0, v___x_715_);
v___x_717_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_713_, v___f_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___boxed(lean_object* v_d_718_, lean_object* v_onlyNonCumulative_719_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_720_; lean_object* v_res_721_; 
v_onlyNonCumulative_boxed_720_ = lean_unbox(v_onlyNonCumulative_719_);
v_res_721_ = l_Lean_Fmt_TaggedDoc_unindented(v_d_718_, v_onlyNonCumulative_boxed_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_final(lean_object* v_d_723_){
_start:
{
lean_object* v___f_724_; lean_object* v___x_725_; 
v___f_724_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_final___closed__0));
v___x_725_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_723_, v___f_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_initial(lean_object* v_d_727_){
_start:
{
lean_object* v___f_728_; lean_object* v___x_729_; 
v___f_728_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_initial___closed__0));
v___x_729_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_727_, v___f_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_free(lean_object* v_d_731_){
_start:
{
lean_object* v___f_732_; lean_object* v___x_733_; 
v___f_732_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_free___closed__0));
v___x_733_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_731_, v___f_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded___lam__0(lean_object* v_p_734_, lean_object* v_d_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_734_, v_d_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object* v_p_737_, lean_object* v_d_738_){
_start:
{
lean_object* v___f_739_; lean_object* v___x_740_; 
v___f_739_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_guarded___lam__0), 2, 1);
lean_closure_set(v___f_739_, 0, v_p_737_);
v___x_740_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_738_, v___f_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0(lean_object* v_amount_741_, lean_object* v_d_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = l_Lean_Fmt_DefaultCost_ofFailureFallbackPenalty___redArg(v_amount_741_);
v___x_744_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_743_, v_d_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(lean_object* v_d_745_, lean_object* v_amount_746_){
_start:
{
lean_object* v___f_747_; lean_object* v___x_748_; 
v___f_747_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_747_, 0, v_amount_746_);
v___x_748_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_745_, v___f_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0(lean_object* v_amount_749_, lean_object* v_d_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = l_Lean_Fmt_DefaultCost_ofOverflowFallbackPenalty___redArg(v_amount_749_);
v___x_752_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_751_, v_d_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(lean_object* v_d_753_, lean_object* v_amount_754_){
_start:
{
lean_object* v___f_755_; lean_object* v___x_756_; 
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_755_, 0, v_amount_754_);
v___x_756_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_753_, v___f_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0(lean_object* v_amount_757_, lean_object* v_d_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(v_amount_757_);
v___x_760_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_759_, v_d_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(lean_object* v_d_761_, lean_object* v_amount_762_){
_start:
{
lean_object* v___f_763_; lean_object* v___x_764_; 
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_763_, 0, v_amount_762_);
v___x_764_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_761_, v___f_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_either(lean_object* v_a_765_, lean_object* v_b_766_){
_start:
{
lean_object* v_doc_767_; lean_object* v_doc_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_doc_767_ = lean_ctor_get(v_a_765_, 0);
lean_inc(v_doc_767_);
lean_dec_ref(v_a_765_);
v_doc_768_ = lean_ctor_get(v_b_766_, 0);
lean_inc(v_doc_768_);
lean_dec_ref(v_b_766_);
v___x_769_ = l_Lean_Fmt_Doc_either___override___redArg(v_doc_767_, v_doc_768_);
v___x_770_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object* v_ds_772_){
_start:
{
lean_object* v___f_773_; lean_object* v___x_774_; 
v___f_773_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_oneOf___closed__0));
v___x_774_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_772_, v___f_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnFailure(lean_object* v_d_775_, lean_object* v_fallback_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(v_fallback_776_, v___x_777_);
v___x_779_ = lean_unsigned_to_nat(2u);
v___x_780_ = lean_mk_empty_array_with_capacity(v___x_779_);
v___x_781_ = lean_array_push(v___x_780_, v_d_775_);
v___x_782_ = lean_array_push(v___x_781_, v___x_778_);
v___x_783_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(lean_object* v_d_784_, lean_object* v_fallback_785_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_fallback_785_, v___x_786_);
v___x_788_ = lean_unsigned_to_nat(2u);
v___x_789_ = lean_mk_empty_array_with_capacity(v___x_788_);
v___x_790_ = lean_array_push(v___x_789_, v_d_784_);
v___x_791_ = lean_array_push(v___x_790_, v___x_787_);
v___x_792_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnHeight(lean_object* v_d_793_, lean_object* v_fallback_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_795_ = lean_unsigned_to_nat(1u);
v___x_796_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v_fallback_794_, v___x_795_);
v___x_797_ = lean_unsigned_to_nat(2u);
v___x_798_ = lean_mk_empty_array_with_capacity(v___x_797_);
v___x_799_ = lean_array_push(v___x_798_, v_d_793_);
v___x_800_ = lean_array_push(v___x_799_, v___x_796_);
v___x_801_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__0(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_802_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_803_ = l_Lean_Fmt_TaggedDoc_space;
v___x_804_ = lean_unsigned_to_nat(2u);
v___x_805_ = lean_mk_empty_array_with_capacity(v___x_804_);
v___x_806_ = lean_array_push(v___x_805_, v___x_803_);
v___x_807_ = lean_array_push(v___x_806_, v___x_802_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__1(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_softSpace___closed__0, &l_Lean_Fmt_TaggedDoc_softSpace___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__0);
v___x_809_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace(void){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_softSpace___closed__1, &l_Lean_Fmt_TaggedDoc_softSpace___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__1);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_append(lean_object* v_a_811_, lean_object* v_b_812_){
_start:
{
lean_object* v_doc_813_; lean_object* v_doc_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_doc_813_ = lean_ctor_get(v_a_811_, 0);
lean_inc(v_doc_813_);
lean_dec_ref(v_a_811_);
v_doc_814_ = lean_ctor_get(v_b_812_, 0);
lean_inc(v_doc_814_);
lean_dec_ref(v_b_812_);
v___x_815_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_813_, v_doc_814_);
v___x_816_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object* v_ds_818_){
_start:
{
lean_object* v___f_819_; lean_object* v___x_820_; 
v___f_819_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_join___closed__0));
v___x_820_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_818_, v___f_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing___lam__0(lean_object* v_sep_821_, lean_object* v_x_822_){
_start:
{
lean_object* v_doc_823_; lean_object* v___x_824_; 
v_doc_823_ = lean_ctor_get(v_sep_821_, 0);
lean_inc(v_doc_823_);
lean_dec_ref(v_sep_821_);
v___x_824_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_doc_823_, v_x_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing(lean_object* v_sep_825_, lean_object* v_ds_826_){
_start:
{
lean_object* v___f_827_; lean_object* v___x_828_; 
v___f_827_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_joinUsing___lam__0), 2, 1);
lean_closure_set(v___f_827_, 0, v_sep_825_);
v___x_828_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_826_, v___f_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith___lam__0(lean_object* v_sep_829_, lean_object* v_i_830_){
_start:
{
lean_object* v___x_831_; lean_object* v_flat_832_; lean_object* v_broken_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_842_; 
v___x_831_ = lean_apply_1(v_sep_829_, v_i_830_);
v_flat_832_ = lean_ctor_get(v___x_831_, 0);
v_broken_833_ = lean_ctor_get(v___x_831_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_842_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_842_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_broken_833_);
lean_inc(v_flat_832_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_842_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_doc_837_; lean_object* v_doc_838_; lean_object* v___x_840_; 
v_doc_837_ = lean_ctor_get(v_flat_832_, 0);
lean_inc(v_doc_837_);
lean_dec(v_flat_832_);
v_doc_838_ = lean_ctor_get(v_broken_833_, 0);
lean_inc(v_doc_838_);
lean_dec(v_broken_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_doc_838_);
lean_ctor_set(v___x_835_, 0, v_doc_837_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_doc_837_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_doc_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith___lam__1(lean_object* v___f_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Fmt_Doc_fillWith___redArg(v_x_844_, v___f_843_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith___lam__1___boxed(lean_object* v___f_846_, lean_object* v_x_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Fmt_TaggedDoc_fillWith___lam__1(v___f_846_, v_x_847_);
lean_dec_ref(v_x_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith(lean_object* v_ds_849_, lean_object* v_sep_850_){
_start:
{
lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___x_853_; 
v___f_851_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWith___lam__0), 2, 1);
lean_closure_set(v___f_851_, 0, v_sep_850_);
v___f_852_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWith___lam__1___boxed), 2, 1);
lean_closure_set(v___f_852_, 0, v___f_851_);
v___x_853_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_849_, v___f_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object* v_ds_855_){
_start:
{
lean_object* v___f_856_; lean_object* v___x_857_; 
v___f_856_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fill___closed__0));
v___x_857_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_855_, v___f_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0(lean_object* v_wrap_858_, lean_object* v_d_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_doc_862_; 
v___x_860_ = l_Lean_Fmt_TaggedDoc_untagged(v_d_859_);
v___x_861_ = lean_apply_1(v_wrap_858_, v___x_860_);
v_doc_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_doc_862_);
lean_dec_ref(v___x_861_);
return v_doc_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1(lean_object* v___f_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_x_864_, v___f_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping(lean_object* v_ds_866_, lean_object* v_wrap_867_){
_start:
{
lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___x_870_; 
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_868_, 0, v_wrap_867_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1), 2, 1);
lean_closure_set(v___f_869_, 0, v___f_868_);
v___x_870_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_866_, v___f_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace(lean_object* v_ds_872_){
_start:
{
lean_object* v___f_873_; lean_object* v___x_874_; 
v___f_873_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0));
v___x_874_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_872_, v___f_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1(lean_object* v___f_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_x_876_, v___f_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(lean_object* v_ds_878_, lean_object* v_wrap_879_){
_start:
{
lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___x_882_; 
v___f_880_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_880_, 0, v_wrap_879_);
v___f_881_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1), 2, 1);
lean_closure_set(v___f_881_, 0, v___f_880_);
v___x_882_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_878_, v___f_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object* v_as_883_, size_t v_i_884_, size_t v_stop_885_, lean_object* v_b_886_){
_start:
{
uint8_t v___x_887_; 
v___x_887_ = lean_usize_dec_eq(v_i_884_, v_stop_885_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; size_t v___x_890_; size_t v___x_891_; 
v___x_888_ = lean_array_uget_borrowed(v_as_883_, v_i_884_);
v___x_889_ = l_Array_append___redArg(v_b_886_, v___x_888_);
v___x_890_ = ((size_t)1ULL);
v___x_891_ = lean_usize_add(v_i_884_, v___x_890_);
v_i_884_ = v___x_891_;
v_b_886_ = v___x_889_;
goto _start;
}
else
{
return v_b_886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1___boxed(lean_object* v_as_893_, lean_object* v_i_894_, lean_object* v_stop_895_, lean_object* v_b_896_){
_start:
{
size_t v_i_boxed_897_; size_t v_stop_boxed_898_; lean_object* v_res_899_; 
v_i_boxed_897_ = lean_unbox_usize(v_i_894_);
lean_dec(v_i_894_);
v_stop_boxed_898_ = lean_unbox_usize(v_stop_895_);
lean_dec(v_stop_895_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(v_as_893_, v_i_boxed_897_, v_stop_boxed_898_, v_b_896_);
lean_dec_ref(v_as_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(size_t v_sz_900_, size_t v_i_901_, lean_object* v_bs_902_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_usize_dec_lt(v_i_901_, v_sz_900_);
if (v___x_903_ == 0)
{
return v_bs_902_;
}
else
{
lean_object* v_v_904_; lean_object* v___x_905_; lean_object* v_bs_x27_906_; size_t v_sz_907_; size_t v___x_908_; lean_object* v___x_909_; size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; 
v_v_904_ = lean_array_uget(v_bs_902_, v_i_901_);
v___x_905_ = lean_unsigned_to_nat(0u);
v_bs_x27_906_ = lean_array_uset(v_bs_902_, v_i_901_, v___x_905_);
v_sz_907_ = lean_array_size(v_v_904_);
v___x_908_ = ((size_t)0ULL);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_907_, v___x_908_, v_v_904_);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_add(v_i_901_, v___x_910_);
v___x_912_ = lean_array_uset(v_bs_x27_906_, v_i_901_, v___x_909_);
v_i_901_ = v___x_911_;
v_bs_902_ = v___x_912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object* v_sz_914_, lean_object* v_i_915_, lean_object* v_bs_916_){
_start:
{
size_t v_sz_boxed_917_; size_t v_i_boxed_918_; lean_object* v_res_919_; 
v_sz_boxed_917_ = lean_unbox_usize(v_sz_914_);
lean_dec(v_sz_914_);
v_i_boxed_918_ = lean_unbox_usize(v_i_915_);
lean_dec(v_i_915_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(v_sz_boxed_917_, v_i_boxed_918_, v_bs_916_);
return v_res_919_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(lean_object* v_dss_924_){
_start:
{
lean_object* v___x_925_; lean_object* v___y_927_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_925_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1));
v___x_941_ = lean_array_get_size(v_dss_924_);
v___x_942_ = lean_nat_dec_lt(v___x_939_, v___x_941_);
if (v___x_942_ == 0)
{
v___y_927_ = v___x_940_;
goto v___jp_926_;
}
else
{
size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((size_t)0ULL);
v___x_944_ = lean_usize_of_nat(v___x_941_);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(v_dss_924_, v___x_943_, v___x_944_, v___x_940_);
v___y_927_ = v___x_945_;
goto v___jp_926_;
}
v___jp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = lean_array_get_size(v___y_927_);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_dec_eq(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; size_t v_sz_932_; size_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref(v___y_927_);
v___x_931_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0, &l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0);
v_sz_932_ = lean_array_size(v_dss_924_);
v___x_933_ = ((size_t)0ULL);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(v_sz_932_, v___x_933_, v_dss_924_);
v___x_935_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v___x_931_, v___x_934_);
lean_dec_ref(v___x_934_);
v___x_936_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_935_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec_ref(v_dss_924_);
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_array_get(v___x_925_, v___y_927_, v___x_937_);
lean_dec_ref(v___y_927_);
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0(size_t v_sz_946_, size_t v_i_947_, lean_object* v_bs_948_){
_start:
{
uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_lt(v_i_947_, v_sz_946_);
if (v___x_949_ == 0)
{
return v_bs_948_;
}
else
{
lean_object* v_v_950_; lean_object* v_v_951_; uint8_t v_allowFill_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_966_; 
v_v_950_ = lean_array_uget(v_bs_948_, v_i_947_);
v_v_951_ = lean_ctor_get(v_v_950_, 0);
v_allowFill_952_ = lean_ctor_get_uint8(v_v_950_, sizeof(void*)*1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_v_950_);
if (v_isSharedCheck_966_ == 0)
{
v___x_954_ = v_v_950_;
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_v_951_);
lean_dec(v_v_950_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_doc_956_; lean_object* v___x_957_; lean_object* v_bs_x27_958_; lean_object* v___x_960_; 
v_doc_956_ = lean_ctor_get(v_v_951_, 0);
lean_inc(v_doc_956_);
lean_dec(v_v_951_);
v___x_957_ = lean_unsigned_to_nat(0u);
v_bs_x27_958_ = lean_array_uset(v_bs_948_, v_i_947_, v___x_957_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v_doc_956_);
v___x_960_ = v___x_954_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_doc_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*1, v_allowFill_952_);
v___x_960_ = v_reuseFailAlloc_965_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; 
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_add(v_i_947_, v___x_961_);
v___x_963_ = lean_array_uset(v_bs_x27_958_, v_i_947_, v___x_960_);
v_i_947_ = v___x_962_;
v_bs_948_ = v___x_963_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0___boxed(lean_object* v_sz_967_, lean_object* v_i_968_, lean_object* v_bs_969_){
_start:
{
size_t v_sz_boxed_970_; size_t v_i_boxed_971_; lean_object* v_res_972_; 
v_sz_boxed_970_ = lean_unbox_usize(v_sz_967_);
lean_dec(v_sz_967_);
v_i_boxed_971_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0(v_sz_boxed_970_, v_i_boxed_971_, v_bs_969_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_974_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object* v_ds_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_976_ = lean_array_get_size(v_ds_975_);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_nat_dec_eq(v___x_976_, v___x_977_);
if (v___x_978_ == 0)
{
size_t v_sz_979_; size_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_sz_979_ = lean_array_size(v_ds_975_);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0(v_sz_979_, v___x_980_, v_ds_975_);
v___x_982_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v___x_981_);
v___x_983_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_982_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_v_987_; 
v___x_984_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_array_get(v___x_984_, v_ds_975_, v___x_985_);
lean_dec_ref(v_ds_975_);
v_v_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_v_987_);
lean_dec(v___x_986_);
return v_v_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object* v_ds_988_, lean_object* v_wrap_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_990_ = lean_array_get_size(v_ds_988_);
v___x_991_ = lean_unsigned_to_nat(1u);
v___x_992_ = lean_nat_dec_eq(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___f_993_; size_t v_sz_994_; size_t v___x_995_; lean_object* v_ds_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___f_993_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_993_, 0, v_wrap_989_);
v_sz_994_ = lean_array_size(v_ds_988_);
v___x_995_ = ((size_t)0ULL);
v_ds_996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0(v_sz_994_, v___x_995_, v_ds_988_);
v___x_997_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_996_, v___f_993_);
v___x_998_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_997_);
return v___x_998_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_v_1002_; 
lean_dec_ref(v_wrap_989_);
v___x_999_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0);
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_array_get(v___x_999_, v_ds_988_, v___x_1000_);
lean_dec_ref(v_ds_988_);
v_v_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_v_1002_);
lean_dec(v___x_1001_);
return v_v_1002_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object* v_d_1003_){
_start:
{
lean_object* v_doc_1004_; uint8_t v___x_1005_; 
v_doc_1004_ = lean_ctor_get(v_d_1003_, 0);
v___x_1005_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object* v_d_1006_){
_start:
{
uint8_t v_res_1007_; lean_object* v_r_1008_; 
v_res_1007_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_d_1006_);
lean_dec_ref(v_d_1006_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(lean_object* v_d_1009_){
_start:
{
lean_object* v_doc_1010_; uint8_t v___x_1011_; 
v_doc_1010_ = lean_ctor_get(v_d_1009_, 0);
v___x_1011_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_doc_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty___boxed(lean_object* v_d_1012_){
_start:
{
uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(v_d_1012_);
lean_dec_ref(v_d_1012_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isCompoundAtomic(lean_object* v_d_1015_){
_start:
{
lean_object* v_doc_1016_; uint8_t v___x_1017_; 
v_doc_1016_ = lean_ctor_get(v_d_1015_, 0);
v___x_1017_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_doc_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isCompoundAtomic___boxed(lean_object* v_d_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_d_1018_);
lean_dec_ref(v_d_1018_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object* v_d_1021_){
_start:
{
lean_object* v_doc_1022_; uint8_t v___x_1023_; 
v_doc_1022_ = lean_ctor_get(v_d_1021_, 0);
v___x_1023_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_doc_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAtomic___boxed(lean_object* v_d_1024_){
_start:
{
uint8_t v_res_1025_; lean_object* v_r_1026_; 
v_res_1025_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_d_1024_);
lean_dec_ref(v_d_1024_);
v_r_1026_ = lean_box(v_res_1025_);
return v_r_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instAppend___lam__0(lean_object* v_a_1027_, lean_object* v_b_1028_){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1027_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; 
v___x_1030_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_1028_);
if (v___x_1030_ == 0)
{
lean_object* v_doc_1031_; lean_object* v_doc_1032_; uint8_t v___x_1033_; 
v_doc_1031_ = lean_ctor_get(v_a_1027_, 0);
lean_inc(v_doc_1031_);
lean_dec_ref(v_a_1027_);
v_doc_1032_ = lean_ctor_get(v_b_1028_, 0);
lean_inc(v_doc_1032_);
lean_dec_ref(v_b_1028_);
v___x_1033_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1031_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1032_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1031_, v_doc_1032_);
v___x_1036_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1035_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_doc_1032_);
v___x_1037_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1031_);
return v___x_1037_;
}
}
else
{
lean_object* v___x_1038_; 
lean_dec(v_doc_1031_);
v___x_1038_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1032_);
return v___x_1038_;
}
}
else
{
lean_dec_ref(v_b_1028_);
return v_a_1027_;
}
}
else
{
lean_dec_ref(v_a_1027_);
return v_b_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___impl(uint8_t v_x_1041_){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_box(v_x_1041_);
v___x_1043_ = lean_obj_tag_nat(v___x_1042_);
lean_dec(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___impl___boxed(lean_object* v_x_1044_){
_start:
{
uint8_t v_x_4__boxed_1045_; lean_object* v_res_1046_; 
v_x_4__boxed_1045_ = lean_unbox(v_x_1044_);
v_res_1046_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___impl(v_x_4__boxed_1045_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(lean_object* v_k_1047_){
_start:
{
lean_inc(v_k_1047_);
return v_k_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg___boxed(lean_object* v_k_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(v_k_1048_);
lean_dec(v_k_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(lean_object* v_motive_1050_, lean_object* v_ctorIdx_1051_, uint8_t v_t_1052_, lean_object* v_h_1053_, lean_object* v_k_1054_){
_start:
{
lean_inc(v_k_1054_);
return v_k_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___boxed(lean_object* v_motive_1055_, lean_object* v_ctorIdx_1056_, lean_object* v_t_1057_, lean_object* v_h_1058_, lean_object* v_k_1059_){
_start:
{
uint8_t v_t_boxed_1060_; lean_object* v_res_1061_; 
v_t_boxed_1060_ = lean_unbox(v_t_1057_);
v_res_1061_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(v_motive_1055_, v_ctorIdx_1056_, v_t_boxed_1060_, v_h_1058_, v_k_1059_);
lean_dec(v_k_1059_);
lean_dec(v_ctorIdx_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(lean_object* v_coequal_1062_){
_start:
{
lean_inc(v_coequal_1062_);
return v_coequal_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg___boxed(lean_object* v_coequal_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(v_coequal_1063_);
lean_dec(v_coequal_1063_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(lean_object* v_motive_1065_, uint8_t v_t_1066_, lean_object* v_h_1067_, lean_object* v_coequal_1068_){
_start:
{
lean_inc(v_coequal_1068_);
return v_coequal_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___boxed(lean_object* v_motive_1069_, lean_object* v_t_1070_, lean_object* v_h_1071_, lean_object* v_coequal_1072_){
_start:
{
uint8_t v_t_boxed_1073_; lean_object* v_res_1074_; 
v_t_boxed_1073_ = lean_unbox(v_t_1070_);
v_res_1074_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(v_motive_1069_, v_t_boxed_1073_, v_h_1071_, v_coequal_1072_);
lean_dec(v_coequal_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(lean_object* v_preferSticky_1075_){
_start:
{
lean_inc(v_preferSticky_1075_);
return v_preferSticky_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg___boxed(lean_object* v_preferSticky_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(v_preferSticky_1076_);
lean_dec(v_preferSticky_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(lean_object* v_motive_1078_, uint8_t v_t_1079_, lean_object* v_h_1080_, lean_object* v_preferSticky_1081_){
_start:
{
lean_inc(v_preferSticky_1081_);
return v_preferSticky_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___boxed(lean_object* v_motive_1082_, lean_object* v_t_1083_, lean_object* v_h_1084_, lean_object* v_preferSticky_1085_){
_start:
{
uint8_t v_t_boxed_1086_; lean_object* v_res_1087_; 
v_t_boxed_1086_ = lean_unbox(v_t_1083_);
v_res_1087_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(v_motive_1082_, v_t_boxed_1086_, v_h_1084_, v_preferSticky_1085_);
lean_dec(v_preferSticky_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(lean_object* v_preferUnsticky_1088_){
_start:
{
lean_inc(v_preferUnsticky_1088_);
return v_preferUnsticky_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg___boxed(lean_object* v_preferUnsticky_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(v_preferUnsticky_1089_);
lean_dec(v_preferUnsticky_1089_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(lean_object* v_motive_1091_, uint8_t v_t_1092_, lean_object* v_h_1093_, lean_object* v_preferUnsticky_1094_){
_start:
{
lean_inc(v_preferUnsticky_1094_);
return v_preferUnsticky_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___boxed(lean_object* v_motive_1095_, lean_object* v_t_1096_, lean_object* v_h_1097_, lean_object* v_preferUnsticky_1098_){
_start:
{
uint8_t v_t_boxed_1099_; lean_object* v_res_1100_; 
v_t_boxed_1099_ = lean_unbox(v_t_1096_);
v_res_1100_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(v_motive_1095_, v_t_boxed_1099_, v_h_1097_, v_preferUnsticky_1098_);
lean_dec(v_preferUnsticky_1098_);
return v_res_1100_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default(void){
_start:
{
uint8_t v___x_1101_; 
v___x_1101_ = 0;
return v___x_1101_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind(void){
_start:
{
uint8_t v___x_1102_; 
v___x_1102_ = 0;
return v___x_1102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(uint8_t v_x_1103_, uint8_t v_y_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1105_ = lean_box(v_x_1103_);
v___x_1106_ = lean_obj_tag_nat(v___x_1105_);
lean_dec(v___x_1105_);
v___x_1107_ = lean_box(v_y_1104_);
v___x_1108_ = lean_obj_tag_nat(v___x_1107_);
lean_dec(v___x_1107_);
v___x_1109_ = lean_nat_dec_eq(v___x_1106_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq___boxed(lean_object* v_x_1110_, lean_object* v_y_1111_){
_start:
{
uint8_t v_x_24__boxed_1112_; uint8_t v_y_25__boxed_1113_; uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_x_24__boxed_1112_ = lean_unbox(v_x_1110_);
v_y_25__boxed_1113_ = lean_unbox(v_y_1111_);
v_res_1114_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_x_24__boxed_1112_, v_y_25__boxed_1113_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0(void){
_start:
{
uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = 0;
v___x_1119_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1120_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*1, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default(void){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0, &l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky(void){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___lam__0(lean_object* v_v_1134_, lean_object* v_f_1135_){
_start:
{
lean_object* v_stickyVariant_1136_; uint8_t v_kind_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1145_; 
v_stickyVariant_1136_ = lean_ctor_get(v_v_1134_, 0);
v_kind_1137_ = lean_ctor_get_uint8(v_v_1134_, sizeof(void*)*1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_v_1134_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1139_ = v_v_1134_;
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_stickyVariant_1136_);
lean_dec(v_v_1134_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_stickyVariant_1136_, v_f_1135_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1141_);
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1144_, sizeof(void*)*1, v_kind_1137_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object* v_nonStickyVariant_1147_, lean_object* v_stickyVariant_1148_, uint8_t v_kind_1149_){
_start:
{
lean_object* v___f_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___f_1150_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_sticky___closed__0));
v___x_1151_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_1152_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_1153_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1153_, 0, v_stickyVariant_1148_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*1, v_kind_1149_);
v___x_1154_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1151_, v___x_1152_, v_nonStickyVariant_1147_, v___x_1153_, v___f_1150_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___boxed(lean_object* v_nonStickyVariant_1155_, lean_object* v_stickyVariant_1156_, lean_object* v_kind_1157_){
_start:
{
uint8_t v_kind_boxed_1158_; lean_object* v_res_1159_; 
v_kind_boxed_1158_ = lean_unbox(v_kind_1157_);
v_res_1159_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_1155_, v_stickyVariant_1156_, v_kind_boxed_1158_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object* v_doc_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_1162_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1161_, v_doc_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(lean_object* v_doc_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_doc_1163_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_box(0);
return v___x_1165_;
}
else
{
lean_object* v_val_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1175_; 
v_val_1166_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1168_ = v___x_1164_;
v_isShared_1169_ = v_isSharedCheck_1175_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_val_1166_);
lean_dec(v___x_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1175_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
uint8_t v_kind_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v_kind_1170_ = lean_ctor_get_uint8(v_val_1166_, sizeof(void*)*1);
lean_dec(v_val_1166_);
v___x_1171_ = lean_box(v_kind_1170_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1171_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object* v_inner_1176_, lean_object* v_f_1177_, lean_object* v_kind_x3f_1178_){
_start:
{
lean_object* v_nonStickyOuter_1179_; lean_object* v___x_1180_; 
lean_inc_ref(v_f_1177_);
lean_inc_ref(v_inner_1176_);
v_nonStickyOuter_1179_ = lean_apply_1(v_f_1177_, v_inner_1176_);
v___x_1180_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_inner_1176_);
if (lean_obj_tag(v___x_1180_) == 1)
{
lean_object* v_val_1181_; lean_object* v_stickyVariant_1182_; uint8_t v_kind_1183_; lean_object* v_stickyOuter_1184_; 
v_val_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_val_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v_stickyVariant_1182_ = lean_ctor_get(v_val_1181_, 0);
lean_inc_ref(v_stickyVariant_1182_);
v_kind_1183_ = lean_ctor_get_uint8(v_val_1181_, sizeof(void*)*1);
lean_dec(v_val_1181_);
v_stickyOuter_1184_ = lean_apply_1(v_f_1177_, v_stickyVariant_1182_);
if (lean_obj_tag(v_kind_x3f_1178_) == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1179_, v_stickyOuter_1184_, v_kind_1183_);
return v___x_1185_;
}
else
{
lean_object* v_val_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; 
v_val_1186_ = lean_ctor_get(v_kind_x3f_1178_, 0);
v___x_1187_ = lean_unbox(v_val_1186_);
v___x_1188_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1179_, v_stickyOuter_1184_, v___x_1187_);
return v___x_1188_;
}
}
else
{
lean_dec(v___x_1180_);
lean_dec_ref(v_f_1177_);
return v_nonStickyOuter_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness___boxed(lean_object* v_inner_1189_, lean_object* v_f_1190_, lean_object* v_kind_x3f_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_inner_1189_, v_f_1190_, v_kind_x3f_1191_);
lean_dec(v_kind_x3f_1191_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___impl(lean_object* v_x_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_obj_tag_nat(v_x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___impl___boxed(lean_object* v_x_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___impl(v_x_1195_);
lean_dec(v_x_1195_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(lean_object* v_t_1197_, lean_object* v_k_1198_){
_start:
{
if (lean_obj_tag(v_t_1197_) == 2)
{
uint8_t v_allowFlattening_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_allowFlattening_1199_ = lean_ctor_get_uint8(v_t_1197_, 0);
v___x_1200_ = lean_box(v_allowFlattening_1199_);
v___x_1201_ = lean_apply_1(v_k_1198_, v___x_1200_);
return v___x_1201_;
}
else
{
return v_k_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg___boxed(lean_object* v_t_1202_, lean_object* v_k_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1202_, v_k_1203_);
lean_dec(v_t_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(lean_object* v_motive_1205_, lean_object* v_ctorIdx_1206_, lean_object* v_t_1207_, lean_object* v_h_1208_, lean_object* v_k_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1207_, v_k_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___boxed(lean_object* v_motive_1211_, lean_object* v_ctorIdx_1212_, lean_object* v_t_1213_, lean_object* v_h_1214_, lean_object* v_k_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(v_motive_1211_, v_ctorIdx_1212_, v_t_1213_, v_h_1214_, v_k_1215_);
lean_dec(v_t_1213_);
lean_dec(v_ctorIdx_1212_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(lean_object* v_t_1217_, lean_object* v_coequal_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1217_, v_coequal_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg___boxed(lean_object* v_t_1220_, lean_object* v_coequal_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(v_t_1220_, v_coequal_1221_);
lean_dec(v_t_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(lean_object* v_motive_1223_, lean_object* v_t_1224_, lean_object* v_h_1225_, lean_object* v_coequal_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1224_, v_coequal_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___boxed(lean_object* v_motive_1228_, lean_object* v_t_1229_, lean_object* v_h_1230_, lean_object* v_coequal_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(v_motive_1228_, v_t_1229_, v_h_1230_, v_coequal_1231_);
lean_dec(v_t_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(lean_object* v_t_1233_, lean_object* v_preferUnsticky_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1233_, v_preferUnsticky_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg___boxed(lean_object* v_t_1236_, lean_object* v_preferUnsticky_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(v_t_1236_, v_preferUnsticky_1237_);
lean_dec(v_t_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(lean_object* v_motive_1239_, lean_object* v_t_1240_, lean_object* v_h_1241_, lean_object* v_preferUnsticky_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1240_, v_preferUnsticky_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___boxed(lean_object* v_motive_1244_, lean_object* v_t_1245_, lean_object* v_h_1246_, lean_object* v_preferUnsticky_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(v_motive_1244_, v_t_1245_, v_h_1246_, v_preferUnsticky_1247_);
lean_dec(v_t_1245_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(lean_object* v_t_1249_, lean_object* v_preferSticky_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1249_, v_preferSticky_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg___boxed(lean_object* v_t_1252_, lean_object* v_preferSticky_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(v_t_1252_, v_preferSticky_1253_);
lean_dec(v_t_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(lean_object* v_motive_1255_, lean_object* v_t_1256_, lean_object* v_h_1257_, lean_object* v_preferSticky_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1256_, v_preferSticky_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___boxed(lean_object* v_motive_1260_, lean_object* v_t_1261_, lean_object* v_h_1262_, lean_object* v_preferSticky_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(v_motive_1260_, v_t_1261_, v_h_1262_, v_preferSticky_1263_);
lean_dec(v_t_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(lean_object* v_s_1265_, uint8_t v_allowFlattening_1266_){
_start:
{
uint8_t v_kind_1267_; 
v_kind_1267_ = lean_ctor_get_uint8(v_s_1265_, sizeof(void*)*1);
switch(v_kind_1267_)
{
case 0:
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_box(0);
return v___x_1268_;
}
case 1:
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1269_, 0, v_allowFlattening_1266_);
return v___x_1269_;
}
default: 
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_box(1);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky___boxed(lean_object* v_s_1271_, lean_object* v_allowFlattening_1272_){
_start:
{
uint8_t v_allowFlattening_boxed_1273_; lean_object* v_res_1274_; 
v_allowFlattening_boxed_1273_ = lean_unbox(v_allowFlattening_1272_);
v_res_1274_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_s_1271_, v_allowFlattening_boxed_1273_);
lean_dec_ref(v_s_1271_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt(lean_object* v_doc_1275_, lean_object* v_stickyDoc_1276_, lean_object* v_cfg_1277_){
_start:
{
switch(lean_obj_tag(v_cfg_1277_))
{
case 0:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1278_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1276_);
v___x_1279_ = lean_unsigned_to_nat(2u);
v___x_1280_ = lean_mk_empty_array_with_capacity(v___x_1279_);
v___x_1281_ = lean_array_push(v___x_1280_, v___x_1278_);
v___x_1282_ = lean_array_push(v___x_1281_, v_doc_1275_);
v___x_1283_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1282_);
return v___x_1283_;
}
case 1:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1284_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1276_);
v___x_1285_ = lean_unsigned_to_nat(1u);
v___x_1286_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v___x_1284_, v___x_1285_);
v___x_1287_ = lean_unsigned_to_nat(2u);
v___x_1288_ = lean_mk_empty_array_with_capacity(v___x_1287_);
v___x_1289_ = lean_array_push(v___x_1288_, v_doc_1275_);
v___x_1290_ = lean_array_push(v___x_1289_, v___x_1286_);
v___x_1291_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1290_);
return v___x_1291_;
}
default: 
{
uint8_t v_allowFlattening_1292_; 
v_allowFlattening_1292_ = lean_ctor_get_uint8(v_cfg_1277_, 0);
if (v_allowFlattening_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1293_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1276_);
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1275_, v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(2u);
v___x_1297_ = lean_mk_empty_array_with_capacity(v___x_1296_);
v___x_1298_ = lean_array_push(v___x_1297_, v___x_1293_);
v___x_1299_ = lean_array_push(v___x_1298_, v___x_1295_);
v___x_1300_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1299_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1301_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1276_);
lean_inc_ref(v_doc_1275_);
v___x_1302_ = l_Lean_Fmt_TaggedDoc_flattened(v_doc_1275_);
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1275_, v___x_1303_);
v___x_1305_ = lean_unsigned_to_nat(3u);
v___x_1306_ = lean_mk_empty_array_with_capacity(v___x_1305_);
v___x_1307_ = lean_array_push(v___x_1306_, v___x_1301_);
v___x_1308_ = lean_array_push(v___x_1307_, v___x_1302_);
v___x_1309_ = lean_array_push(v___x_1308_, v___x_1304_);
v___x_1310_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1309_);
return v___x_1310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt___boxed(lean_object* v_doc_1311_, lean_object* v_stickyDoc_1312_, lean_object* v_cfg_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1311_, v_stickyDoc_1312_, v_cfg_1313_);
lean_dec(v_cfg_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0(lean_object* v_s_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0));
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_s_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___lam__0(lean_object* v_doc_x3f_1321_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v_doc_x3f_1321_);
lean_ctor_set(v___x_1323_, 2, v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object* v_doc_x3f_1326_, lean_object* v_sepBefore_1327_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_sepBefore_1327_);
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v_doc_x3f_1326_);
lean_ctor_set(v___x_1330_, 2, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object* v_doc_x3f_1331_, lean_object* v_sepAfter_1332_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_box(0);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_sepAfter_1332_);
v___x_1335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v_doc_x3f_1331_);
lean_ctor_set(v___x_1335_, 2, v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(lean_object* v_as_1336_, size_t v_i_1337_, size_t v_stop_1338_, lean_object* v_b_1339_){
_start:
{
lean_object* v___y_1341_; uint8_t v___x_1345_; 
v___x_1345_ = lean_usize_dec_eq(v_i_1337_, v_stop_1338_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v_doc_x3f_1347_; 
v___x_1346_ = lean_array_uget_borrowed(v_as_1336_, v_i_1337_);
v_doc_x3f_1347_ = lean_ctor_get(v___x_1346_, 1);
if (lean_obj_tag(v_doc_x3f_1347_) == 0)
{
v___y_1341_ = v_b_1339_;
goto v___jp_1340_;
}
else
{
lean_object* v_sepBefore_x3f_1348_; lean_object* v_sepAfter_x3f_1349_; lean_object* v_val_1350_; uint8_t v___x_1351_; 
v_sepBefore_x3f_1348_ = lean_ctor_get(v___x_1346_, 0);
v_sepAfter_x3f_1349_ = lean_ctor_get(v___x_1346_, 2);
v_val_1350_ = lean_ctor_get(v_doc_x3f_1347_, 0);
v___x_1351_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_inc(v_sepAfter_x3f_1349_);
lean_inc(v_val_1350_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_val_1350_);
lean_ctor_set(v___x_1352_, 1, v_sepAfter_x3f_1349_);
lean_inc(v_sepBefore_x3f_1348_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_sepBefore_x3f_1348_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = lean_array_push(v_b_1339_, v___x_1353_);
v___y_1341_ = v___x_1354_;
goto v___jp_1340_;
}
else
{
v___y_1341_ = v_b_1339_;
goto v___jp_1340_;
}
}
}
else
{
return v_b_1339_;
}
v___jp_1340_:
{
size_t v___x_1342_; size_t v___x_1343_; 
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_add(v_i_1337_, v___x_1342_);
v_i_1337_ = v___x_1343_;
v_b_1339_ = v___y_1341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0___boxed(lean_object* v_as_1355_, lean_object* v_i_1356_, lean_object* v_stop_1357_, lean_object* v_b_1358_){
_start:
{
size_t v_i_boxed_1359_; size_t v_stop_boxed_1360_; lean_object* v_res_1361_; 
v_i_boxed_1359_ = lean_unbox_usize(v_i_1356_);
lean_dec(v_i_1356_);
v_stop_boxed_1360_ = lean_unbox_usize(v_stop_1357_);
lean_dec(v_stop_1357_);
v_res_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1355_, v_i_boxed_1359_, v_stop_boxed_1360_, v_b_1358_);
lean_dec_ref(v_as_1355_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(lean_object* v_as_1364_, lean_object* v_start_1365_, lean_object* v_stop_1366_){
_start:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0));
v___x_1368_ = lean_nat_dec_lt(v_start_1365_, v_stop_1366_);
if (v___x_1368_ == 0)
{
return v___x_1367_;
}
else
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_array_get_size(v_as_1364_);
v___x_1370_ = lean_nat_dec_le(v_stop_1366_, v___x_1369_);
if (v___x_1370_ == 0)
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_nat_dec_lt(v_start_1365_, v___x_1369_);
if (v___x_1371_ == 0)
{
return v___x_1367_;
}
else
{
size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_usize_of_nat(v_start_1365_);
v___x_1373_ = lean_usize_of_nat(v___x_1369_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1364_, v___x_1372_, v___x_1373_, v___x_1367_);
return v___x_1374_;
}
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_usize_of_nat(v_start_1365_);
v___x_1376_ = lean_usize_of_nat(v_stop_1366_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1364_, v___x_1375_, v___x_1376_, v___x_1367_);
return v___x_1377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___boxed(lean_object* v_as_1378_, lean_object* v_start_1379_, lean_object* v_stop_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_as_1378_, v_start_1379_, v_stop_1380_);
lean_dec(v_stop_1380_);
lean_dec(v_start_1379_);
lean_dec_ref(v_as_1378_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(lean_object* v_cs_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_array_get_size(v_cs_1382_);
v___x_1385_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_cs_1382_, v___x_1383_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs___boxed(lean_object* v_cs_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1386_);
lean_dec_ref(v_cs_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(size_t v_sz_1388_, size_t v_i_1389_, lean_object* v_bs_1390_){
_start:
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_usize_dec_lt(v_i_1389_, v_sz_1388_);
if (v___x_1391_ == 0)
{
return v_bs_1390_;
}
else
{
lean_object* v_v_1392_; lean_object* v_snd_1393_; lean_object* v_fst_1394_; lean_object* v_fst_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1408_; 
v_v_1392_ = lean_array_uget_borrowed(v_bs_1390_, v_i_1389_);
v_snd_1393_ = lean_ctor_get(v_v_1392_, 1);
lean_inc(v_snd_1393_);
v_fst_1394_ = lean_ctor_get(v_v_1392_, 0);
lean_inc(v_fst_1394_);
v_fst_1395_ = lean_ctor_get(v_snd_1393_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_snd_1393_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v_snd_1393_, 1);
lean_dec(v_unused_1409_);
v___x_1397_ = v_snd_1393_;
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_fst_1395_);
lean_dec(v_snd_1393_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v_bs_x27_1400_; lean_object* v___x_1402_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v_bs_x27_1400_ = lean_array_uset(v_bs_1390_, v_i_1389_, v___x_1399_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v_fst_1395_);
lean_ctor_set(v___x_1397_, 0, v_fst_1394_);
v___x_1402_ = v___x_1397_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_fst_1394_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_fst_1395_);
v___x_1402_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_add(v_i_1389_, v___x_1403_);
v___x_1405_ = lean_array_uset(v_bs_x27_1400_, v_i_1389_, v___x_1402_);
v_i_1389_ = v___x_1404_;
v_bs_1390_ = v___x_1405_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0___boxed(lean_object* v_sz_1410_, lean_object* v_i_1411_, lean_object* v_bs_1412_){
_start:
{
size_t v_sz_boxed_1413_; size_t v_i_boxed_1414_; lean_object* v_res_1415_; 
v_sz_boxed_1413_ = lean_unbox_usize(v_sz_1410_);
lean_dec(v_sz_1410_);
v_i_boxed_1414_ = lean_unbox_usize(v_i_1411_);
lean_dec(v_i_1411_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_boxed_1413_, v_i_boxed_1414_, v_bs_1412_);
return v_res_1415_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_box(0);
v___x_1417_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v___x_1416_);
return v___x_1418_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0);
v___x_1420_ = lean_box(0);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
lean_ctor_set(v___x_1421_, 1, v___x_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(lean_object* v_upperBound_1422_, lean_object* v_a_1423_, lean_object* v_b_1424_){
_start:
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_nat_dec_lt(v_a_1423_, v_upperBound_1422_);
if (v___x_1425_ == 0)
{
lean_dec(v_a_1423_);
return v_b_1424_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v_snd_1428_; lean_object* v_snd_1429_; lean_object* v___x_1430_; lean_object* v_a_1432_; 
v___x_1426_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1427_ = lean_array_get_borrowed(v___x_1426_, v_b_1424_, v_a_1423_);
v_snd_1428_ = lean_ctor_get(v___x_1427_, 1);
v_snd_1429_ = lean_ctor_get(v_snd_1428_, 1);
v___x_1430_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1429_) == 1)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = lean_nat_add(v_a_1423_, v___x_1430_);
v___x_1436_ = lean_array_get_size(v_b_1424_);
v___x_1437_ = lean_nat_dec_lt(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_dec(v___x_1435_);
v_a_1432_ = v_b_1424_;
goto v___jp_1431_;
}
else
{
lean_object* v_v_1438_; lean_object* v_snd_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1449_; 
lean_inc_ref(v_snd_1429_);
v_v_1438_ = lean_array_fget(v_b_1424_, v___x_1435_);
v_snd_1439_ = lean_ctor_get(v_v_1438_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_v_1438_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v_v_1438_, 0);
lean_dec(v_unused_1450_);
v___x_1441_ = v_v_1438_;
v_isShared_1442_ = v_isSharedCheck_1449_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_snd_1439_);
lean_dec(v_v_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1449_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v_xs_x27_1444_; lean_object* v___x_1446_; 
v___x_1443_ = lean_box(0);
v_xs_x27_1444_ = lean_array_fset(v_b_1424_, v___x_1435_, v___x_1443_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v_snd_1429_);
v___x_1446_ = v___x_1441_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_snd_1429_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_snd_1439_);
v___x_1446_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_array_fset(v_xs_x27_1444_, v___x_1435_, v___x_1446_);
lean_dec(v___x_1435_);
v_a_1432_ = v___x_1447_;
goto v___jp_1431_;
}
}
}
}
else
{
v_a_1432_ = v_b_1424_;
goto v___jp_1431_;
}
v___jp_1431_:
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_nat_add(v_a_1423_, v___x_1430_);
lean_dec(v_a_1423_);
v_a_1423_ = v___x_1433_;
v_b_1424_ = v_a_1432_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___boxed(lean_object* v_upperBound_1451_, lean_object* v_a_1452_, lean_object* v_b_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1451_, v_a_1452_, v_b_1453_);
lean_dec(v_upperBound_1451_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(lean_object* v_upperBound_1455_, lean_object* v_a_1456_, lean_object* v_b_1457_){
_start:
{
uint8_t v___x_1458_; 
v___x_1458_ = lean_nat_dec_lt(v_a_1456_, v_upperBound_1455_);
if (v___x_1458_ == 0)
{
lean_dec(v_a_1456_);
return v_b_1457_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v_snd_1462_; lean_object* v_snd_1463_; lean_object* v___x_1464_; lean_object* v_a_1466_; 
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1461_ = lean_array_get_borrowed(v___x_1460_, v_b_1457_, v_a_1456_);
v_snd_1462_ = lean_ctor_get(v___x_1461_, 1);
v_snd_1463_ = lean_ctor_get(v_snd_1462_, 1);
v___x_1464_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1463_) == 1)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v_fst_1471_; 
v___x_1469_ = lean_nat_add(v_a_1456_, v___x_1464_);
v___x_1470_ = lean_array_get_borrowed(v___x_1460_, v_b_1457_, v___x_1469_);
lean_dec(v___x_1469_);
v_fst_1471_ = lean_ctor_get(v___x_1470_, 0);
if (lean_obj_tag(v_fst_1471_) == 1)
{
lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1472_ = lean_array_get_size(v_b_1457_);
v___x_1473_ = lean_nat_dec_lt(v_a_1456_, v___x_1472_);
if (v___x_1473_ == 0)
{
v_a_1466_ = v_b_1457_;
goto v___jp_1465_;
}
else
{
lean_object* v_v_1474_; lean_object* v_snd_1475_; lean_object* v_fst_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1495_; 
v_v_1474_ = lean_array_fget(v_b_1457_, v_a_1456_);
v_snd_1475_ = lean_ctor_get(v_v_1474_, 1);
v_fst_1476_ = lean_ctor_get(v_v_1474_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_v_1474_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1478_ = v_v_1474_;
v_isShared_1479_ = v_isSharedCheck_1495_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_snd_1475_);
lean_inc(v_fst_1476_);
lean_dec(v_v_1474_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1495_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_fst_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1493_; 
v_fst_1480_ = lean_ctor_get(v_snd_1475_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_snd_1475_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_snd_1475_, 1);
lean_dec(v_unused_1494_);
v___x_1482_ = v_snd_1475_;
v_isShared_1483_ = v_isSharedCheck_1493_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_fst_1480_);
lean_dec(v_snd_1475_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1493_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v_xs_x27_1485_; lean_object* v___x_1487_; 
v___x_1484_ = lean_box(0);
v_xs_x27_1485_ = lean_array_fset(v_b_1457_, v_a_1456_, v___x_1484_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1459_);
v___x_1487_ = v___x_1482_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_fst_1480_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1459_);
v___x_1487_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 1, v___x_1487_);
v___x_1489_ = v___x_1478_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_fst_1476_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_array_fset(v_xs_x27_1485_, v_a_1456_, v___x_1489_);
v_a_1466_ = v___x_1490_;
goto v___jp_1465_;
}
}
}
}
}
}
else
{
v_a_1466_ = v_b_1457_;
goto v___jp_1465_;
}
}
else
{
v_a_1466_ = v_b_1457_;
goto v___jp_1465_;
}
v___jp_1465_:
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_nat_add(v_a_1456_, v___x_1464_);
lean_dec(v_a_1456_);
v_a_1456_ = v___x_1467_;
v_b_1457_ = v_a_1466_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg___boxed(lean_object* v_upperBound_1496_, lean_object* v_a_1497_, lean_object* v_b_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1496_, v_a_1497_, v_b_1498_);
lean_dec(v_upperBound_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(lean_object* v_upperBound_1500_, lean_object* v_a_1501_, lean_object* v_b_1502_){
_start:
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_nat_dec_lt(v_a_1501_, v_upperBound_1500_);
if (v___x_1503_ == 0)
{
return v_b_1502_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_snd_1507_; lean_object* v_snd_1508_; lean_object* v___x_1509_; lean_object* v_a_1511_; 
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1506_ = lean_array_get_borrowed(v___x_1505_, v_b_1502_, v_a_1501_);
v_snd_1507_ = lean_ctor_get(v___x_1506_, 1);
v_snd_1508_ = lean_ctor_get(v_snd_1507_, 1);
v___x_1509_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1508_) == 1)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_fst_1516_; 
v___x_1514_ = lean_nat_add(v_a_1501_, v___x_1509_);
v___x_1515_ = lean_array_get_borrowed(v___x_1505_, v_b_1502_, v___x_1514_);
lean_dec(v___x_1514_);
v_fst_1516_ = lean_ctor_get(v___x_1515_, 0);
if (lean_obj_tag(v_fst_1516_) == 1)
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = lean_array_get_size(v_b_1502_);
v___x_1518_ = lean_nat_dec_lt(v_a_1501_, v___x_1517_);
if (v___x_1518_ == 0)
{
v_a_1511_ = v_b_1502_;
goto v___jp_1510_;
}
else
{
lean_object* v_v_1519_; lean_object* v_snd_1520_; lean_object* v_fst_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1540_; 
v_v_1519_ = lean_array_fget(v_b_1502_, v_a_1501_);
v_snd_1520_ = lean_ctor_get(v_v_1519_, 1);
v_fst_1521_ = lean_ctor_get(v_v_1519_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_v_1519_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1523_ = v_v_1519_;
v_isShared_1524_ = v_isSharedCheck_1540_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_snd_1520_);
lean_inc(v_fst_1521_);
lean_dec(v_v_1519_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1540_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_fst_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1538_; 
v_fst_1525_ = lean_ctor_get(v_snd_1520_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_snd_1520_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v_snd_1520_, 1);
lean_dec(v_unused_1539_);
v___x_1527_ = v_snd_1520_;
v_isShared_1528_ = v_isSharedCheck_1538_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_fst_1525_);
lean_dec(v_snd_1520_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1538_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v_xs_x27_1530_; lean_object* v___x_1532_; 
v___x_1529_ = lean_box(0);
v_xs_x27_1530_ = lean_array_fset(v_b_1502_, v_a_1501_, v___x_1529_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1504_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_fst_1525_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1504_);
v___x_1532_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 1, v___x_1532_);
v___x_1534_ = v___x_1523_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_fst_1521_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_array_fset(v_xs_x27_1530_, v_a_1501_, v___x_1534_);
v_a_1511_ = v___x_1535_;
goto v___jp_1510_;
}
}
}
}
}
}
else
{
v_a_1511_ = v_b_1502_;
goto v___jp_1510_;
}
}
else
{
v_a_1511_ = v_b_1502_;
goto v___jp_1510_;
}
v___jp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_nat_add(v_a_1501_, v___x_1509_);
v___x_1513_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1500_, v___x_1512_, v_a_1511_);
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg___boxed(lean_object* v_upperBound_1541_, lean_object* v_a_1542_, lean_object* v_b_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1541_, v_a_1542_, v_b_1543_);
lean_dec(v_a_1542_);
lean_dec(v_upperBound_1541_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(lean_object* v_entries_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1560_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1588_ = lean_array_get_size(v_entries_1545_);
v___x_1589_ = lean_nat_dec_lt(v___x_1546_, v___x_1588_);
if (v___x_1589_ == 0)
{
v___y_1560_ = v_entries_1545_;
goto v___jp_1559_;
}
else
{
lean_object* v_v_1590_; lean_object* v_snd_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1602_; 
v_v_1590_ = lean_array_fget(v_entries_1545_, v___x_1546_);
v_snd_1591_ = lean_ctor_get(v_v_1590_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_v_1590_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v_v_1590_, 0);
lean_dec(v_unused_1603_);
v___x_1593_ = v_v_1590_;
v_isShared_1594_ = v_isSharedCheck_1602_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_snd_1591_);
lean_dec(v_v_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1602_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v_xs_x27_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1595_ = lean_box(0);
v_xs_x27_1596_ = lean_array_fset(v_entries_1545_, v___x_1546_, v___x_1595_);
v___x_1597_ = lean_box(0);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1597_);
v___x_1599_ = v___x_1593_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_snd_1591_);
v___x_1599_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_array_fset(v_xs_x27_1596_, v___x_1546_, v___x_1599_);
v___y_1560_ = v___x_1600_;
goto v___jp_1559_;
}
}
}
v___jp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; size_t v_sz_1556_; size_t v___x_1557_; lean_object* v___x_1558_; 
v___x_1550_ = lean_array_get_size(v___y_1549_);
v___x_1551_ = lean_nat_sub(v___x_1550_, v___y_1548_);
v___x_1552_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v___x_1551_, v___x_1546_, v___y_1549_);
lean_dec(v___x_1551_);
v___x_1553_ = lean_array_get_size(v___x_1552_);
v___x_1554_ = lean_nat_sub(v___x_1553_, v___y_1548_);
v___x_1555_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v___x_1554_, v___x_1546_, v___x_1552_);
lean_dec(v___x_1554_);
v_sz_1556_ = lean_array_size(v___x_1555_);
v___x_1557_ = ((size_t)0ULL);
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_1556_, v___x_1557_, v___x_1555_);
return v___x_1558_;
}
v___jp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1561_ = lean_array_get_size(v___y_1560_);
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_sub(v___x_1561_, v___x_1562_);
v___x_1564_ = lean_nat_dec_lt(v___x_1563_, v___x_1561_);
if (v___x_1564_ == 0)
{
lean_dec(v___x_1563_);
v___y_1548_ = v___x_1562_;
v___y_1549_ = v___y_1560_;
goto v___jp_1547_;
}
else
{
lean_object* v_v_1565_; lean_object* v_snd_1566_; lean_object* v_fst_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1587_; 
v_v_1565_ = lean_array_fget(v___y_1560_, v___x_1563_);
v_snd_1566_ = lean_ctor_get(v_v_1565_, 1);
v_fst_1567_ = lean_ctor_get(v_v_1565_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_v_1565_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1569_ = v_v_1565_;
v_isShared_1570_ = v_isSharedCheck_1587_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snd_1566_);
lean_inc(v_fst_1567_);
lean_dec(v_v_1565_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1587_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v_fst_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1585_; 
v_fst_1571_ = lean_ctor_get(v_snd_1566_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_snd_1566_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v_snd_1566_, 1);
lean_dec(v_unused_1586_);
v___x_1573_ = v_snd_1566_;
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_fst_1571_);
lean_dec(v_snd_1566_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v_xs_x27_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1575_ = lean_box(0);
v_xs_x27_1576_ = lean_array_fset(v___y_1560_, v___x_1563_, v___x_1575_);
v___x_1577_ = lean_box(0);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___x_1577_);
v___x_1579_ = v___x_1573_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_fst_1571_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1581_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 1, v___x_1579_);
v___x_1581_ = v___x_1569_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_fst_1567_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_array_fset(v_xs_x27_1576_, v___x_1563_, v___x_1581_);
lean_dec(v___x_1563_);
v___y_1548_ = v___x_1562_;
v___y_1549_ = v___x_1582_;
goto v___jp_1547_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(lean_object* v_upperBound_1604_, lean_object* v_inst_1605_, lean_object* v_R_1606_, lean_object* v_a_1607_, lean_object* v_b_1608_, lean_object* v_c_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1604_, v_a_1607_, v_b_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___boxed(lean_object* v_upperBound_1611_, lean_object* v_inst_1612_, lean_object* v_R_1613_, lean_object* v_a_1614_, lean_object* v_b_1615_, lean_object* v_c_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(v_upperBound_1611_, v_inst_1612_, v_R_1613_, v_a_1614_, v_b_1615_, v_c_1616_);
lean_dec(v_upperBound_1611_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(lean_object* v_upperBound_1618_, lean_object* v_inst_1619_, lean_object* v_R_1620_, lean_object* v_a_1621_, lean_object* v_b_1622_, lean_object* v_c_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1618_, v_a_1621_, v_b_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___boxed(lean_object* v_upperBound_1625_, lean_object* v_inst_1626_, lean_object* v_R_1627_, lean_object* v_a_1628_, lean_object* v_b_1629_, lean_object* v_c_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(v_upperBound_1625_, v_inst_1626_, v_R_1627_, v_a_1628_, v_b_1629_, v_c_1630_);
lean_dec(v_a_1628_);
lean_dec(v_upperBound_1625_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(lean_object* v_upperBound_1632_, lean_object* v_inst_1633_, lean_object* v_R_1634_, lean_object* v_a_1635_, lean_object* v_b_1636_, lean_object* v_c_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1632_, v_a_1635_, v_b_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___boxed(lean_object* v_upperBound_1639_, lean_object* v_inst_1640_, lean_object* v_R_1641_, lean_object* v_a_1642_, lean_object* v_b_1643_, lean_object* v_c_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(v_upperBound_1639_, v_inst_1640_, v_R_1641_, v_a_1642_, v_b_1643_, v_c_1644_);
lean_dec(v_upperBound_1639_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(lean_object* v_as_1646_, size_t v_sz_1647_, size_t v_i_1648_, lean_object* v_b_1649_){
_start:
{
lean_object* v_a_1651_; uint8_t v___x_1655_; 
v___x_1655_ = lean_usize_dec_lt(v_i_1648_, v_sz_1647_);
if (v___x_1655_ == 0)
{
return v_b_1649_;
}
else
{
lean_object* v_a_1656_; lean_object* v_fst_1657_; 
v_a_1656_ = lean_array_uget_borrowed(v_as_1646_, v_i_1648_);
v_fst_1657_ = lean_ctor_get(v_a_1656_, 0);
if (lean_obj_tag(v_fst_1657_) == 1)
{
lean_object* v_val_1658_; lean_object* v_snd_1659_; lean_object* v_s_1660_; lean_object* v_wrap_1661_; lean_object* v___y_1663_; lean_object* v___y_1666_; uint8_t v___x_1677_; 
v_val_1658_ = lean_ctor_get(v_fst_1657_, 0);
v_snd_1659_ = lean_ctor_get(v_a_1656_, 1);
v_s_1660_ = lean_ctor_get(v_val_1658_, 0);
v_wrap_1661_ = lean_ctor_get(v_val_1658_, 1);
v___x_1677_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_s_1660_);
if (v___x_1677_ == 0)
{
uint8_t v___x_1678_; 
v___x_1678_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_snd_1659_);
if (v___x_1678_ == 0)
{
lean_object* v_doc_1679_; lean_object* v_doc_1680_; uint8_t v___x_1681_; 
v_doc_1679_ = lean_ctor_get(v_s_1660_, 0);
v_doc_1680_ = lean_ctor_get(v_snd_1659_, 0);
v___x_1681_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1679_);
if (v___x_1681_ == 0)
{
uint8_t v___x_1682_; 
v___x_1682_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1680_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_inc(v_doc_1680_);
lean_inc(v_doc_1679_);
v___x_1683_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1679_, v_doc_1680_);
v___x_1684_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1683_);
v___y_1666_ = v___x_1684_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1685_; 
lean_inc(v_doc_1679_);
v___x_1685_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1679_);
v___y_1666_ = v___x_1685_;
goto v___jp_1665_;
}
}
else
{
lean_object* v___x_1686_; 
lean_inc(v_doc_1680_);
v___x_1686_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1680_);
v___y_1666_ = v___x_1686_;
goto v___jp_1665_;
}
}
else
{
lean_inc_ref(v_s_1660_);
v___y_1666_ = v_s_1660_;
goto v___jp_1665_;
}
}
else
{
lean_inc(v_snd_1659_);
v___y_1666_ = v_snd_1659_;
goto v___jp_1665_;
}
v___jp_1662_:
{
lean_object* v___x_1664_; 
lean_inc_ref(v_wrap_1661_);
v___x_1664_ = lean_apply_1(v_wrap_1661_, v___y_1663_);
v_a_1651_ = v___x_1664_;
goto v___jp_1650_;
}
v___jp_1665_:
{
uint8_t v___x_1667_; 
v___x_1667_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_1666_);
if (v___x_1667_ == 0)
{
uint8_t v___x_1668_; 
v___x_1668_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_1649_);
if (v___x_1668_ == 0)
{
lean_object* v_doc_1669_; lean_object* v_doc_1670_; uint8_t v___x_1671_; 
v_doc_1669_ = lean_ctor_get(v___y_1666_, 0);
lean_inc(v_doc_1669_);
lean_dec_ref(v___y_1666_);
v_doc_1670_ = lean_ctor_get(v_b_1649_, 0);
lean_inc(v_doc_1670_);
lean_dec_ref(v_b_1649_);
v___x_1671_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1669_);
if (v___x_1671_ == 0)
{
uint8_t v___x_1672_; 
v___x_1672_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1670_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1669_, v_doc_1670_);
v___x_1674_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1673_);
v___y_1663_ = v___x_1674_;
goto v___jp_1662_;
}
else
{
lean_object* v___x_1675_; 
lean_dec(v_doc_1670_);
v___x_1675_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1669_);
v___y_1663_ = v___x_1675_;
goto v___jp_1662_;
}
}
else
{
lean_object* v___x_1676_; 
lean_dec(v_doc_1669_);
v___x_1676_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1670_);
v___y_1663_ = v___x_1676_;
goto v___jp_1662_;
}
}
else
{
lean_dec_ref(v_b_1649_);
v___y_1663_ = v___y_1666_;
goto v___jp_1662_;
}
}
else
{
lean_dec_ref(v___y_1666_);
v___y_1663_ = v_b_1649_;
goto v___jp_1662_;
}
}
}
else
{
lean_object* v_snd_1687_; uint8_t v___x_1688_; 
v_snd_1687_ = lean_ctor_get(v_a_1656_, 1);
v___x_1688_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_snd_1687_);
if (v___x_1688_ == 0)
{
uint8_t v___x_1689_; 
v___x_1689_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_1649_);
if (v___x_1689_ == 0)
{
lean_object* v_doc_1690_; lean_object* v_doc_1691_; uint8_t v___x_1692_; 
v_doc_1690_ = lean_ctor_get(v_snd_1687_, 0);
v_doc_1691_ = lean_ctor_get(v_b_1649_, 0);
lean_inc(v_doc_1691_);
lean_dec_ref(v_b_1649_);
v___x_1692_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1690_);
if (v___x_1692_ == 0)
{
uint8_t v___x_1693_; 
v___x_1693_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1691_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc(v_doc_1690_);
v___x_1694_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1690_, v_doc_1691_);
v___x_1695_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1694_);
v_a_1651_ = v___x_1695_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1696_; 
lean_dec(v_doc_1691_);
lean_inc(v_doc_1690_);
v___x_1696_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1690_);
v_a_1651_ = v___x_1696_;
goto v___jp_1650_;
}
}
else
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1691_);
v_a_1651_ = v___x_1697_;
goto v___jp_1650_;
}
}
else
{
lean_dec_ref(v_b_1649_);
lean_inc(v_snd_1687_);
v_a_1651_ = v_snd_1687_;
goto v___jp_1650_;
}
}
else
{
v_a_1651_ = v_b_1649_;
goto v___jp_1650_;
}
}
}
v___jp_1650_:
{
size_t v___x_1652_; size_t v___x_1653_; 
v___x_1652_ = ((size_t)1ULL);
v___x_1653_ = lean_usize_add(v_i_1648_, v___x_1652_);
v_i_1648_ = v___x_1653_;
v_b_1649_ = v_a_1651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0___boxed(lean_object* v_as_1698_, lean_object* v_sz_1699_, lean_object* v_i_1700_, lean_object* v_b_1701_){
_start:
{
size_t v_sz_boxed_1702_; size_t v_i_boxed_1703_; lean_object* v_res_1704_; 
v_sz_boxed_1702_ = lean_unbox_usize(v_sz_1699_);
lean_dec(v_sz_1699_);
v_i_boxed_1703_ = lean_unbox_usize(v_i_1700_);
lean_dec(v_i_1700_);
v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v_as_1698_, v_sz_boxed_1702_, v_i_boxed_1703_, v_b_1701_);
lean_dec_ref(v_as_1698_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object* v_cs_1705_){
_start:
{
lean_object* v_entries_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_entries_1706_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1705_);
v___x_1707_ = lean_array_get_size(v_entries_1706_);
v___x_1708_ = lean_unsigned_to_nat(0u);
v___x_1709_ = lean_nat_dec_eq(v___x_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_dec_eq(v___x_1707_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v_entries_1712_; lean_object* v_combined_1713_; lean_object* v___x_1714_; size_t v_sz_1715_; size_t v___x_1716_; lean_object* v___x_1717_; 
v_entries_1712_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(v_entries_1706_);
v_combined_1713_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_1714_ = l_Array_reverse___redArg(v_entries_1712_);
v_sz_1715_ = lean_array_size(v___x_1714_);
v___x_1716_ = ((size_t)0ULL);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v___x_1714_, v_sz_1715_, v___x_1716_, v_combined_1713_);
lean_dec_ref(v___x_1714_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; lean_object* v_snd_1719_; lean_object* v_fst_1720_; 
v___x_1718_ = lean_array_fget(v_entries_1706_, v___x_1708_);
lean_dec_ref(v_entries_1706_);
v_snd_1719_ = lean_ctor_get(v___x_1718_, 1);
lean_inc(v_snd_1719_);
lean_dec(v___x_1718_);
v_fst_1720_ = lean_ctor_get(v_snd_1719_, 0);
lean_inc(v_fst_1720_);
lean_dec(v_snd_1719_);
return v_fst_1720_;
}
}
else
{
lean_object* v___x_1721_; 
lean_dec_ref(v_entries_1706_);
v___x_1721_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine___boxed(lean_object* v_cs_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Fmt_TaggedDoc_combine(v_cs_1722_);
lean_dec_ref(v_cs_1722_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object* v_lhs_1724_, lean_object* v_sep_1725_, lean_object* v_rhs_1726_, uint8_t v_allowFlattening_1727_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_nonStickyDoc_1737_; lean_object* v___x_1738_; 
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_lhs_1724_);
lean_inc_ref(v_sep_1725_);
lean_inc_ref(v___x_1728_);
v___x_1729_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1728_, v_sep_1725_);
v___x_1730_ = lean_box(0);
lean_inc_ref(v_rhs_1726_);
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_rhs_1726_);
v___x_1732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
lean_ctor_set(v___x_1732_, 2, v___x_1730_);
v___x_1733_ = lean_unsigned_to_nat(2u);
v___x_1734_ = lean_mk_empty_array_with_capacity(v___x_1733_);
lean_inc_ref(v___x_1734_);
v___x_1735_ = lean_array_push(v___x_1734_, v___x_1729_);
v___x_1736_ = lean_array_push(v___x_1735_, v___x_1732_);
v_nonStickyDoc_1737_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1736_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_1726_);
if (lean_obj_tag(v___x_1738_) == 1)
{
lean_object* v_val_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1764_; 
v_val_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1764_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_val_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1764_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v_wrap_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1762_; 
v_wrap_1743_ = lean_ctor_get(v_sep_1725_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_sep_1725_);
if (v_isSharedCheck_1762_ == 0)
{
lean_object* v_unused_1763_; 
v_unused_1763_ = lean_ctor_get(v_sep_1725_, 0);
lean_dec(v_unused_1763_);
v___x_1745_ = v_sep_1725_;
v_isShared_1746_ = v_isSharedCheck_1762_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_wrap_1743_);
lean_dec(v_sep_1725_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1762_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v_stickyVariant_1747_; lean_object* v___x_1748_; lean_object* v_stickySep_1750_; 
v_stickyVariant_1747_ = lean_ctor_get(v_val_1739_, 0);
v___x_1748_ = l_Lean_Fmt_TaggedDoc_space;
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1748_);
v_stickySep_1750_ = v___x_1745_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_wrap_1743_);
v_stickySep_1750_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1728_, v_stickySep_1750_);
lean_inc_ref(v_stickyVariant_1747_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v_stickyVariant_1747_);
v___x_1753_ = v___x_1741_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_stickyVariant_1747_);
v___x_1753_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v_stickyDoc_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1730_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
lean_ctor_set(v___x_1754_, 2, v___x_1730_);
v___x_1755_ = lean_array_push(v___x_1734_, v___x_1751_);
v___x_1756_ = lean_array_push(v___x_1755_, v___x_1754_);
v_stickyDoc_1757_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1756_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_1739_, v_allowFlattening_1727_);
lean_dec(v_val_1739_);
v___x_1759_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_1737_, v_stickyDoc_1757_, v___x_1758_);
lean_dec(v___x_1758_);
return v___x_1759_;
}
}
}
}
}
else
{
lean_dec(v___x_1738_);
lean_dec_ref(v___x_1734_);
lean_dec_ref_known(v___x_1728_, 1);
lean_dec_ref(v_sep_1725_);
return v_nonStickyDoc_1737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine___boxed(lean_object* v_lhs_1765_, lean_object* v_sep_1766_, lean_object* v_rhs_1767_, lean_object* v_allowFlattening_1768_){
_start:
{
uint8_t v_allowFlattening_boxed_1769_; lean_object* v_res_1770_; 
v_allowFlattening_boxed_1769_ = lean_unbox(v_allowFlattening_1768_);
v_res_1770_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_1765_, v_sep_1766_, v_rhs_1767_, v_allowFlattening_boxed_1769_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object* v_body_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(lean_object* v_f_1773_, size_t v_sz_1774_, size_t v_i_1775_, lean_object* v_bs_1776_){
_start:
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_usize_dec_lt(v_i_1775_, v_sz_1774_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v_f_1773_);
return v_bs_1776_;
}
else
{
lean_object* v_v_1778_; lean_object* v___x_1779_; lean_object* v_bs_x27_1780_; lean_object* v___y_1782_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_v_1778_ = lean_array_uget(v_bs_1776_, v_i_1775_);
v___x_1779_ = lean_unsigned_to_nat(0u);
v_bs_x27_1780_ = lean_array_uset(v_bs_1776_, v_i_1775_, v___x_1779_);
v___x_1787_ = lean_usize_to_nat(v_i_1775_);
v___x_1788_ = lean_unsigned_to_nat(2u);
v___x_1789_ = lean_nat_mod(v___x_1787_, v___x_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_nat_dec_eq(v___x_1789_, v___x_1779_);
lean_dec(v___x_1789_);
if (v___x_1790_ == 0)
{
v___y_1782_ = v_v_1778_;
goto v___jp_1781_;
}
else
{
lean_object* v___x_1791_; 
lean_inc_ref(v_f_1773_);
v___x_1791_ = lean_apply_1(v_f_1773_, v_v_1778_);
v___y_1782_ = v___x_1791_;
goto v___jp_1781_;
}
v___jp_1781_:
{
size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_add(v_i_1775_, v___x_1783_);
v___x_1785_ = lean_array_uset(v_bs_x27_1780_, v_i_1775_, v___y_1782_);
v_i_1775_ = v___x_1784_;
v_bs_1776_ = v___x_1785_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg___boxed(lean_object* v_f_1792_, lean_object* v_sz_1793_, lean_object* v_i_1794_, lean_object* v_bs_1795_){
_start:
{
size_t v_sz_boxed_1796_; size_t v_i_boxed_1797_; lean_object* v_res_1798_; 
v_sz_boxed_1796_ = lean_unbox_usize(v_sz_1793_);
lean_dec(v_sz_1793_);
v_i_boxed_1797_ = lean_unbox_usize(v_i_1794_);
lean_dec(v_i_1794_);
v_res_1798_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1792_, v_sz_boxed_1796_, v_i_boxed_1797_, v_bs_1795_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(lean_object* v_a_1799_, lean_object* v_f_1800_){
_start:
{
size_t v_sz_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v_sz_1801_ = lean_array_size(v_a_1799_);
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1800_, v_sz_1801_, v___x_1802_, v_a_1799_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems(lean_object* v_sep_1804_, lean_object* v_a_1805_, lean_object* v_f_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(v_a_1805_, v_f_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___boxed(lean_object* v_sep_1808_, lean_object* v_a_1809_, lean_object* v_f_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems(v_sep_1808_, v_a_1809_, v_f_1810_);
lean_dec_ref(v_sep_1808_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(lean_object* v_f_1812_, lean_object* v_as_1813_, size_t v_sz_1814_, size_t v_i_1815_, lean_object* v_bs_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1812_, v_sz_1814_, v_i_1815_, v_bs_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___boxed(lean_object* v_f_1818_, lean_object* v_as_1819_, lean_object* v_sz_1820_, lean_object* v_i_1821_, lean_object* v_bs_1822_){
_start:
{
size_t v_sz_boxed_1823_; size_t v_i_boxed_1824_; lean_object* v_res_1825_; 
v_sz_boxed_1823_ = lean_unbox_usize(v_sz_1820_);
lean_dec(v_sz_1820_);
v_i_boxed_1824_ = lean_unbox_usize(v_i_1821_);
lean_dec(v_i_1821_);
v_res_1825_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(v_f_1818_, v_as_1819_, v_sz_boxed_1823_, v_i_boxed_1824_, v_bs_1822_);
lean_dec_ref(v_as_1819_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_pushElem(lean_object* v_sep_1826_, lean_object* v_a_1827_, lean_object* v_elem_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1829_ = lean_array_get_size(v_a_1827_);
v___x_1830_ = lean_unsigned_to_nat(2u);
v___x_1831_ = lean_nat_mod(v___x_1829_, v___x_1830_);
v___x_1832_ = lean_unsigned_to_nat(0u);
v___x_1833_ = lean_nat_dec_eq(v___x_1831_, v___x_1832_);
lean_dec(v___x_1831_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1834_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_1826_);
v___x_1835_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1834_);
v___x_1836_ = lean_mk_empty_array_with_capacity(v___x_1830_);
v___x_1837_ = lean_array_push(v___x_1836_, v___x_1835_);
v___x_1838_ = lean_array_push(v___x_1837_, v_elem_1828_);
v___x_1839_ = l_Array_append___redArg(v_a_1827_, v___x_1838_);
lean_dec_ref(v___x_1838_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; 
lean_dec_ref(v_sep_1826_);
v___x_1840_ = lean_array_push(v_a_1827_, v_elem_1828_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(lean_object* v_a_1841_){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1842_ = lean_array_get_size(v_a_1841_);
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_nat_add(v___x_1842_, v___x_1843_);
v___x_1845_ = lean_nat_shiftr(v___x_1844_, v___x_1843_);
lean_dec(v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg___boxed(lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1846_);
lean_dec_ref(v_a_1846_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems(lean_object* v_sep_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___boxed(lean_object* v_sep_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems(v_sep_1851_, v_a_1852_);
lean_dec_ref(v_a_1852_);
lean_dec_ref(v_sep_1851_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0(lean_object* v_docs_1854_){
_start:
{
lean_inc_ref(v_docs_1854_);
return v_docs_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0___boxed(lean_object* v_docs_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0(v_docs_1855_);
lean_dec_ref(v_docs_1855_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg(){
_start:
{
lean_object* v___f_1859_; 
v___f_1859_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___boxed(lean_object* v___dummy_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg();
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(lean_object* v_sep_1862_){
_start:
{
lean_object* v___f_1863_; 
v___f_1863_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___boxed(lean_object* v_sep_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(v_sep_1864_);
lean_dec_ref(v_sep_1864_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg(){
_start:
{
lean_object* v___f_1867_; 
v___f_1867_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg___boxed(lean_object* v___dummy_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg();
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(lean_object* v_sep_1870_){
_start:
{
lean_object* v___f_1871_; 
v___f_1871_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___boxed(lean_object* v_sep_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(v_sep_1872_);
lean_dec_ref(v_sep_1872_);
return v_res_1873_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default(void){
_start:
{
uint8_t v___x_1874_; 
v___x_1874_ = 0;
return v___x_1874_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited(void){
_start:
{
uint8_t v___x_1875_; 
v___x_1875_ = 0;
return v___x_1875_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(uint8_t v_v_1884_, lean_object* v_x_1885_){
_start:
{
return v_v_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0___boxed(lean_object* v_v_1886_, lean_object* v_x_1887_){
_start:
{
uint8_t v_v_boxed_1888_; uint8_t v_res_1889_; lean_object* v_r_1890_; 
v_v_boxed_1888_ = lean_unbox(v_v_1886_);
v_res_1889_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(v_v_boxed_1888_, v_x_1887_);
lean_dec_ref(v_x_1887_);
v_r_1890_ = lean_box(v_res_1889_);
return v_r_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object* v_doc_1892_, uint8_t v_isBracketed_1893_){
_start:
{
lean_object* v___f_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___f_1894_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0));
v___x_1895_ = 0;
v___x_1896_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1897_ = lean_box(v___x_1895_);
v___x_1898_ = lean_box(v_isBracketed_1893_);
v___x_1899_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1897_, v___x_1896_, v_doc_1892_, v___x_1898_, v___f_1894_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___boxed(lean_object* v_doc_1900_, lean_object* v_isBracketed_1901_){
_start:
{
uint8_t v_isBracketed_boxed_1902_; lean_object* v_res_1903_; 
v_isBracketed_boxed_1902_ = lean_unbox(v_isBracketed_1901_);
v_res_1903_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_1900_, v_isBracketed_boxed_1902_);
return v_res_1903_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object* v_doc_1904_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1906_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1905_, v_doc_1904_);
if (lean_obj_tag(v___x_1906_) == 0)
{
uint8_t v___x_1907_; 
v___x_1907_ = 0;
return v___x_1907_;
}
else
{
uint8_t v___x_1908_; 
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = 1;
return v___x_1908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isSelfDelimited___boxed(lean_object* v_doc_1909_){
_start:
{
uint8_t v_res_1910_; lean_object* v_r_1911_; 
v_res_1910_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1909_);
v_r_1911_ = lean_box(v_res_1910_);
return v_r_1911_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isBracketed(lean_object* v_doc_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1914_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1913_, v_doc_1912_);
if (lean_obj_tag(v___x_1914_) == 0)
{
uint8_t v___x_1915_; 
v___x_1915_ = 0;
return v___x_1915_;
}
else
{
lean_object* v_val_1916_; uint8_t v___x_1917_; 
v_val_1916_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v___x_1914_, 1);
v___x_1917_ = lean_unbox(v_val_1916_);
lean_dec(v_val_1916_);
return v___x_1917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isBracketed___boxed(lean_object* v_doc_1918_){
_start:
{
uint8_t v_res_1919_; lean_object* v_r_1920_; 
v_res_1919_ = l_Lean_Fmt_TaggedDoc_isBracketed(v_doc_1918_);
v_r_1920_ = lean_box(v_res_1919_);
return v_r_1920_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default(void){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_box(0);
return v___x_1921_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback(void){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_box(0);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(lean_object* v_v_1931_, lean_object* v_x_1932_){
_start:
{
return v_v_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0___boxed(lean_object* v_v_1933_, lean_object* v_x_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(v_v_1933_, v_x_1934_);
lean_dec_ref(v_x_1934_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object* v_doc_1937_){
_start:
{
lean_object* v___f_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___f_1938_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0));
v___x_1939_ = lean_box(0);
v___x_1940_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1941_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1939_, v___x_1940_, v_doc_1937_, v___x_1939_, v___f_1938_);
return v___x_1941_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object* v_doc_1942_){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1944_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1943_, v_doc_1942_);
if (lean_obj_tag(v___x_1944_) == 0)
{
uint8_t v___x_1945_; 
v___x_1945_ = 0;
return v___x_1945_;
}
else
{
uint8_t v___x_1946_; 
lean_dec_ref_known(v___x_1944_, 1);
v___x_1946_ = 1;
return v___x_1946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isRawFallback___boxed(lean_object* v_doc_1947_){
_start:
{
uint8_t v_res_1948_; lean_object* v_r_1949_; 
v_res_1948_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1947_);
v_r_1949_ = lean_box(v_res_1948_);
return v_r_1949_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default(void){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = 0;
return v___x_1950_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned(void){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = 0;
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object* v_doc_1960_, uint8_t v_mustBeRespected_1961_){
_start:
{
lean_object* v___f_1962_; uint8_t v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___f_1962_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0));
v___x_1963_ = 0;
v___x_1964_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14_));
v___x_1965_ = lean_box(v___x_1963_);
v___x_1966_ = lean_box(v_mustBeRespected_1961_);
v___x_1967_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1965_, v___x_1964_, v_doc_1960_, v___x_1966_, v___f_1962_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___boxed(lean_object* v_doc_1968_, lean_object* v_mustBeRespected_1969_){
_start:
{
uint8_t v_mustBeRespected_boxed_1970_; lean_object* v_res_1971_; 
v_mustBeRespected_boxed_1970_ = lean_unbox(v_mustBeRespected_1969_);
v_res_1971_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_1968_, v_mustBeRespected_boxed_1970_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(lean_object* v_doc_1972_){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14_));
v___x_1974_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1973_, v_doc_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object* v_doc_1975_){
_start:
{
uint8_t v___x_1976_; 
lean_inc_ref(v_doc_1975_);
v___x_1976_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1975_);
if (v___x_1976_ == 0)
{
uint8_t v___x_1977_; 
v___x_1977_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_doc_1975_);
if (v___x_1977_ == 0)
{
uint8_t v___x_1978_; 
v___x_1978_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1975_);
if (v___x_1978_ == 0)
{
uint8_t v___x_1979_; 
v___x_1979_ = 1;
return v___x_1979_;
}
else
{
return v___x_1976_;
}
}
else
{
lean_dec_ref(v_doc_1975_);
return v___x_1976_;
}
}
else
{
lean_dec_ref(v_doc_1975_);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_needsAppBrackets___boxed(lean_object* v_doc_1980_){
_start:
{
uint8_t v_res_1981_; lean_object* v_r_1982_; 
v_res_1981_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_doc_1980_);
v_r_1982_ = lean_box(v_res_1981_);
return v_r_1982_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default(void){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1983_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented(void){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented(lean_object* v_indentedVariant_1994_, lean_object* v_dedentedVariant_1995_){
_start:
{
lean_object* v___f_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___f_1996_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0));
v___x_1997_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1998_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_1999_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1997_, v___x_1998_, v_indentedVariant_1994_, v_dedentedVariant_1995_, v___f_1996_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoDedented_x3f(lean_object* v_doc_2000_){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_2002_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_2001_, v_doc_2000_);
return v___x_2002_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_multiLineRawTagId = _init_l_Lean_Fmt_multiLineRawTagId();
lean_mark_persistent(l_Lean_Fmt_multiLineRawTagId);
l_Lean_Fmt_firstSyntaxTagId = _init_l_Lean_Fmt_firstSyntaxTagId();
lean_mark_persistent(l_Lean_Fmt_firstSyntaxTagId);
l_Lean_Fmt_TaggedDoc_failure = _init_l_Lean_Fmt_TaggedDoc_failure();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_failure);
l_Lean_Fmt_TaggedDoc_nl = _init_l_Lean_Fmt_TaggedDoc_nl();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_nl);
l_Lean_Fmt_TaggedDoc_break = _init_l_Lean_Fmt_TaggedDoc_break();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_break);
l_Lean_Fmt_TaggedDoc_hardNl = _init_l_Lean_Fmt_TaggedDoc_hardNl();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_hardNl);
l_Lean_Fmt_TaggedDoc_empty = _init_l_Lean_Fmt_TaggedDoc_empty();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_empty);
l_Lean_Fmt_TaggedDoc_space = _init_l_Lean_Fmt_TaggedDoc_space();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_space);
l_Lean_Fmt_TaggedDoc_softSpace = _init_l_Lean_Fmt_TaggedDoc_softSpace();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_softSpace);
l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default();
l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind = _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind();
l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default);
l_Lean_Fmt_TaggedDoc_instInhabitedSticky = _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedSticky);
l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default();
l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited = _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited();
l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default);
l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback = _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback);
l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default();
l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned = _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned();
l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default);
l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented = _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Primitives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Primitives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Primitives(builtin);
}
#ifdef __cplusplus
}
#endif
