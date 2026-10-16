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
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isTagged(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isTagged___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object* v_doc_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_doc_1_);
lean_ctor_set(v___x_3_, 1, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(lean_object* v_freshTagId_4_, uint8_t v_kind_5_, lean_object* v_x_6_){
_start:
{
if (lean_obj_tag(v_x_6_) == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_mk_empty_array_with_capacity(v___x_7_);
v___x_9_ = lean_array_push(v___x_8_, v_freshTagId_4_);
v___x_10_ = lean_box(v_kind_5_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_9_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
v___x_12_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
else
{
lean_object* v_val_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_30_; 
v_val_13_ = lean_ctor_get(v_x_6_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_30_ == 0)
{
v___x_15_ = v_x_6_;
v_isShared_16_ = v_isSharedCheck_30_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_val_13_);
lean_dec(v_x_6_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_30_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v_fst_17_; lean_object* v_snd_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_29_; 
v_fst_17_ = lean_ctor_get(v_val_13_, 0);
v_snd_18_ = lean_ctor_get(v_val_13_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v_val_13_);
if (v_isSharedCheck_29_ == 0)
{
v___x_20_ = v_val_13_;
v_isShared_21_ = v_isSharedCheck_29_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_snd_18_);
lean_inc(v_fst_17_);
lean_dec(v_val_13_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_29_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_22_ = lean_array_push(v_fst_17_, v_freshTagId_4_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 0, v___x_22_);
v___x_24_ = v___x_20_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_22_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_snd_18_);
v___x_24_ = v_reuseFailAlloc_28_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_26_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_24_);
v___x_26_ = v___x_15_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0___boxed(lean_object* v_freshTagId_31_, lean_object* v_kind_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_kind_boxed_34_; lean_object* v_res_35_; 
v_kind_boxed_34_ = lean_unbox(v_kind_32_);
v_res_35_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(v_freshTagId_31_, v_kind_boxed_34_, v_x_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(lean_object* v_freshTagId_36_, uint8_t v_kind_37_, lean_object* v_a_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_val_42_; lean_object* v___x_43_; 
v___x_40_ = lean_box(0);
v___x_41_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(v_freshTagId_36_, v_kind_37_, v___x_40_);
v_val_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_val_42_);
lean_dec(v___x_41_);
v___x_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_43_, 0, v_a_38_);
lean_ctor_set(v___x_43_, 1, v_val_42_);
lean_ctor_set(v___x_43_, 2, v_x_39_);
return v___x_43_;
}
else
{
lean_object* v_key_44_; lean_object* v_value_45_; lean_object* v_tail_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_61_; 
v_key_44_ = lean_ctor_get(v_x_39_, 0);
v_value_45_ = lean_ctor_get(v_x_39_, 1);
v_tail_46_ = lean_ctor_get(v_x_39_, 2);
v_isSharedCheck_61_ = !lean_is_exclusive(v_x_39_);
if (v_isSharedCheck_61_ == 0)
{
v___x_48_ = v_x_39_;
v_isShared_49_ = v_isSharedCheck_61_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_tail_46_);
lean_inc(v_value_45_);
lean_inc(v_key_44_);
lean_dec(v_x_39_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_61_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
uint8_t v___x_50_; 
v___x_50_ = l_Lean_Syntax_instBEqRange_beq(v_key_44_, v_a_38_);
if (v___x_50_ == 0)
{
lean_object* v_tail_51_; lean_object* v___x_53_; 
v_tail_51_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_36_, v_kind_37_, v_a_38_, v_tail_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 2, v_tail_51_);
v___x_53_ = v___x_48_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_key_44_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_value_45_);
lean_ctor_set(v_reuseFailAlloc_54_, 2, v_tail_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_val_57_; lean_object* v___x_59_; 
lean_dec(v_key_44_);
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v_value_45_);
v___x_56_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(v_freshTagId_36_, v_kind_37_, v___x_55_);
v_val_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_val_57_);
lean_dec(v___x_56_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 1, v_val_57_);
lean_ctor_set(v___x_48_, 0, v_a_38_);
v___x_59_ = v___x_48_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_38_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_val_57_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v_tail_46_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___boxed(lean_object* v_freshTagId_62_, lean_object* v_kind_63_, lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_kind_boxed_66_; lean_object* v_res_67_; 
v_kind_boxed_66_ = lean_unbox(v_kind_63_);
v_res_67_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_62_, v_kind_boxed_66_, v_a_64_, v_x_65_);
return v_res_67_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(lean_object* v_a_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
else
{
lean_object* v_key_71_; lean_object* v_tail_72_; uint8_t v___x_73_; 
v_key_71_ = lean_ctor_get(v_x_69_, 0);
v_tail_72_ = lean_ctor_get(v_x_69_, 2);
v___x_73_ = l_Lean_Syntax_instBEqRange_beq(v_key_71_, v_a_68_);
if (v___x_73_ == 0)
{
v_x_69_ = v_tail_72_;
goto _start;
}
else
{
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg___boxed(lean_object* v_a_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_75_, v_x_76_);
lean_dec(v_x_76_);
lean_dec_ref(v_a_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
return v_x_79_;
}
else
{
lean_object* v_key_81_; lean_object* v_value_82_; lean_object* v_tail_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_106_; 
v_key_81_ = lean_ctor_get(v_x_80_, 0);
v_value_82_ = lean_ctor_get(v_x_80_, 1);
v_tail_83_ = lean_ctor_get(v_x_80_, 2);
v_isSharedCheck_106_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_106_ == 0)
{
v___x_85_ = v_x_80_;
v_isShared_86_ = v_isSharedCheck_106_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_tail_83_);
lean_inc(v_value_82_);
lean_inc(v_key_81_);
lean_dec(v_x_80_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_106_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v_fold_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_87_ = lean_array_get_size(v_x_79_);
v___x_88_ = l_Lean_Syntax_instHashableRange_hash(v_key_81_);
v___x_89_ = 32ULL;
v___x_90_ = lean_uint64_shift_right(v___x_88_, v___x_89_);
v_fold_91_ = lean_uint64_xor(v___x_88_, v___x_90_);
v___x_92_ = 16ULL;
v___x_93_ = lean_uint64_shift_right(v_fold_91_, v___x_92_);
v___x_94_ = lean_uint64_xor(v_fold_91_, v___x_93_);
v___x_95_ = lean_uint64_to_usize(v___x_94_);
v___x_96_ = lean_usize_of_nat(v___x_87_);
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_sub(v___x_96_, v___x_97_);
v___x_99_ = lean_usize_land(v___x_95_, v___x_98_);
v___x_100_ = lean_array_uget_borrowed(v_x_79_, v___x_99_);
lean_inc(v___x_100_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 2, v___x_100_);
v___x_102_ = v___x_85_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_key_81_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_value_82_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v___x_100_);
v___x_102_ = v_reuseFailAlloc_105_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; 
v___x_103_ = lean_array_uset(v_x_79_, v___x_99_, v___x_102_);
v_x_79_ = v___x_103_;
v_x_80_ = v_tail_83_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(lean_object* v_i_107_, lean_object* v_source_108_, lean_object* v_target_109_){
_start:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_array_get_size(v_source_108_);
v___x_111_ = lean_nat_dec_lt(v_i_107_, v___x_110_);
if (v___x_111_ == 0)
{
lean_dec_ref(v_source_108_);
lean_dec(v_i_107_);
return v_target_109_;
}
else
{
lean_object* v_es_112_; lean_object* v___x_113_; lean_object* v_source_114_; lean_object* v_target_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_es_112_ = lean_array_fget(v_source_108_, v_i_107_);
v___x_113_ = lean_box(0);
v_source_114_ = lean_array_fset(v_source_108_, v_i_107_, v___x_113_);
v_target_115_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(v_target_109_, v_es_112_);
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_i_107_, v___x_116_);
lean_dec(v_i_107_);
v_i_107_ = v___x_117_;
v_source_108_ = v_source_114_;
v_target_109_ = v_target_115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(lean_object* v_data_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_nbuckets_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_120_ = lean_array_get_size(v_data_119_);
v___x_121_ = lean_unsigned_to_nat(2u);
v_nbuckets_122_ = lean_nat_mul(v___x_120_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_box(0);
v___x_125_ = lean_mk_array(v_nbuckets_122_, v___x_124_);
v___x_126_ = lean_array_propagate_mark(v_data_119_, v___x_125_);
v___x_127_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(v___x_123_, v_data_119_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(lean_object* v_freshTagId_128_, uint8_t v_kind_129_, lean_object* v_m_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_size_132_; lean_object* v_buckets_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_185_; 
v_size_132_ = lean_ctor_get(v_m_130_, 0);
v_buckets_133_ = lean_ctor_get(v_m_130_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_m_130_);
if (v_isSharedCheck_185_ == 0)
{
v___x_135_ = v_m_130_;
v_isShared_136_ = v_isSharedCheck_185_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_buckets_133_);
lean_inc(v_size_132_);
lean_dec(v_m_130_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_185_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v_fold_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v_bkt_150_; uint8_t v___x_151_; 
v___x_137_ = lean_array_get_size(v_buckets_133_);
v___x_138_ = l_Lean_Syntax_instHashableRange_hash(v_a_131_);
v___x_139_ = 32ULL;
v___x_140_ = lean_uint64_shift_right(v___x_138_, v___x_139_);
v_fold_141_ = lean_uint64_xor(v___x_138_, v___x_140_);
v___x_142_ = 16ULL;
v___x_143_ = lean_uint64_shift_right(v_fold_141_, v___x_142_);
v___x_144_ = lean_uint64_xor(v_fold_141_, v___x_143_);
v___x_145_ = lean_uint64_to_usize(v___x_144_);
v___x_146_ = lean_usize_of_nat(v___x_137_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v___x_146_, v___x_147_);
v___x_149_ = lean_usize_land(v___x_145_, v___x_148_);
v_bkt_150_ = lean_array_uget_borrowed(v_buckets_133_, v___x_149_);
v___x_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_131_, v_bkt_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_size_x27_157_; lean_object* v___x_158_; lean_object* v_buckets_x27_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_array_push(v___x_153_, v_freshTagId_128_);
v___x_155_ = lean_box(v_kind_129_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v_size_x27_157_ = lean_nat_add(v_size_132_, v___x_152_);
lean_dec(v_size_132_);
lean_inc(v_bkt_150_);
v___x_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_158_, 0, v_a_131_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v_bkt_150_);
v_buckets_x27_159_ = lean_array_uset(v_buckets_133_, v___x_149_, v___x_158_);
v___x_160_ = lean_unsigned_to_nat(4u);
v___x_161_ = lean_nat_mul(v_size_x27_157_, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(3u);
v___x_163_ = lean_nat_div(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_array_get_size(v_buckets_x27_159_);
v___x_165_ = lean_nat_dec_le(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
if (v___x_165_ == 0)
{
lean_object* v_val_166_; lean_object* v___x_168_; 
v_val_166_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(v_buckets_x27_159_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_val_166_);
lean_ctor_set(v___x_135_, 0, v_size_x27_157_);
v___x_168_ = v___x_135_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_size_x27_157_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_val_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
else
{
lean_object* v___x_171_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_buckets_x27_159_);
lean_ctor_set(v___x_135_, 0, v_size_x27_157_);
v___x_171_ = v___x_135_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_size_x27_157_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_buckets_x27_159_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_object* v___x_173_; lean_object* v_buckets_x27_174_; lean_object* v_bkt_x27_175_; lean_object* v___y_177_; uint8_t v___x_182_; 
lean_inc(v_bkt_150_);
v___x_173_ = lean_box(0);
v_buckets_x27_174_ = lean_array_uset(v_buckets_133_, v___x_149_, v___x_173_);
lean_inc_ref(v_a_131_);
v_bkt_x27_175_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_128_, v_kind_129_, v_a_131_, v_bkt_150_);
v___x_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_131_, v_bkt_x27_175_);
lean_dec_ref(v_a_131_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_sub(v_size_132_, v___x_183_);
lean_dec(v_size_132_);
v___y_177_ = v___x_184_;
goto v___jp_176_;
}
else
{
v___y_177_ = v_size_132_;
goto v___jp_176_;
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_array_uset(v_buckets_x27_174_, v___x_149_, v_bkt_x27_175_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v___x_178_);
lean_ctor_set(v___x_135_, 0, v___y_177_);
v___x_180_ = v___x_135_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___y_177_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0___boxed(lean_object* v_freshTagId_186_, lean_object* v_kind_187_, lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
uint8_t v_kind_boxed_190_; lean_object* v_res_191_; 
v_kind_boxed_190_ = lean_unbox(v_kind_187_);
v_res_191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(v_freshTagId_186_, v_kind_boxed_190_, v_m_188_, v_a_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange(lean_object* v_freshTagId_192_, lean_object* v_tags_193_, lean_object* v_doc_194_, lean_object* v_range_195_, uint8_t v_kind_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_doc_199_; lean_object* v_tags_200_; lean_object* v___x_201_; lean_object* v_freshTagId_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_inc_n(v_freshTagId_192_, 2);
v___x_197_ = l_Lean_Fmt_Doc_tagged___override___redArg(v_freshTagId_192_, v_doc_194_);
v___x_198_ = lean_box(0);
v_doc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_doc_199_, 0, v___x_197_);
lean_ctor_set(v_doc_199_, 1, v___x_198_);
v_tags_200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(v_freshTagId_192_, v_kind_196_, v_tags_193_, v_range_195_);
v___x_201_ = lean_unsigned_to_nat(1u);
v_freshTagId_202_ = lean_nat_add(v_freshTagId_192_, v___x_201_);
lean_dec(v_freshTagId_192_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_tags_200_);
lean_ctor_set(v___x_203_, 1, v_doc_199_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_freshTagId_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange___boxed(lean_object* v_freshTagId_205_, lean_object* v_tags_206_, lean_object* v_doc_207_, lean_object* v_range_208_, lean_object* v_kind_209_){
_start:
{
uint8_t v_kind_boxed_210_; lean_object* v_res_211_; 
v_kind_boxed_210_ = lean_unbox(v_kind_209_);
v_res_211_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_205_, v_tags_206_, v_doc_207_, v_range_208_, v_kind_boxed_210_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(lean_object* v_00_u03b2_212_, lean_object* v_a_213_, lean_object* v_x_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_213_, v_x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___boxed(lean_object* v_00_u03b2_216_, lean_object* v_a_217_, lean_object* v_x_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(v_00_u03b2_216_, v_a_217_, v_x_218_);
lean_dec(v_x_218_);
lean_dec_ref(v_a_217_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1(lean_object* v_00_u03b2_221_, lean_object* v_data_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(v_data_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_224_, lean_object* v_i_225_, lean_object* v_source_226_, lean_object* v_target_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(v_i_225_, v_source_226_, v_target_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(v_x_230_, v_x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object* v_doc_233_, lean_object* v_ref_234_, lean_object* v_a_235_){
_start:
{
uint8_t v___x_236_; lean_object* v___x_237_; 
v___x_236_ = 0;
v___x_237_ = l_Lean_Syntax_getRange_x3f(v_ref_234_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 1)
{
lean_object* v_val_238_; lean_object* v_toBacktrackableState_239_; lean_object* v_shareCommonState_240_; lean_object* v_freshTagId_241_; lean_object* v_missingFormatters_242_; lean_object* v_partialFormatters_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_263_; 
v_val_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v___x_237_, 1);
v_toBacktrackableState_239_ = lean_ctor_get(v_a_235_, 0);
v_shareCommonState_240_ = lean_ctor_get(v_a_235_, 1);
v_freshTagId_241_ = lean_ctor_get(v_a_235_, 2);
v_missingFormatters_242_ = lean_ctor_get(v_a_235_, 3);
v_partialFormatters_243_ = lean_ctor_get(v_a_235_, 4);
v_isSharedCheck_263_ = !lean_is_exclusive(v_a_235_);
if (v_isSharedCheck_263_ == 0)
{
v___x_245_ = v_a_235_;
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_partialFormatters_243_);
lean_inc(v_missingFormatters_242_);
lean_inc(v_freshTagId_241_);
lean_inc(v_shareCommonState_240_);
lean_inc(v_toBacktrackableState_239_);
lean_dec(v_a_235_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v_snd_249_; lean_object* v_fst_250_; lean_object* v_fst_251_; lean_object* v_snd_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v___x_247_ = 2;
v___x_248_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_241_, v_toBacktrackableState_239_, v_doc_233_, v_val_238_, v___x_247_);
v_snd_249_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_snd_249_);
v_fst_250_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_fst_250_);
lean_dec_ref(v___x_248_);
v_fst_251_ = lean_ctor_get(v_snd_249_, 0);
v_snd_252_ = lean_ctor_get(v_snd_249_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_snd_249_);
if (v_isSharedCheck_262_ == 0)
{
v___x_254_ = v_snd_249_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snd_252_);
lean_inc(v_fst_251_);
lean_dec(v_snd_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 2, v_fst_250_);
lean_ctor_set(v___x_245_, 0, v_fst_251_);
v___x_257_ = v___x_245_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_fst_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_shareCommonState_240_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_fst_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_missingFormatters_242_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_partialFormatters_243_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_257_);
lean_ctor_set(v___x_254_, 0, v_snd_252_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_snd_252_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v___x_237_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v_doc_233_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_a_235_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg___boxed(lean_object* v_doc_267_, lean_object* v_ref_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_doc_267_, v_ref_268_, v_a_269_);
lean_dec(v_ref_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText(lean_object* v_doc_271_, lean_object* v_ref_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_doc_271_, v_ref_272_, v_a_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___boxed(lean_object* v_doc_276_, lean_object* v_ref_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Fmt_TaggedDoc_taggedText(v_doc_276_, v_ref_277_, v_a_278_, v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_ref_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object* v_doc_281_, lean_object* v_ref_282_, lean_object* v_a_283_){
_start:
{
uint8_t v___x_284_; lean_object* v___x_285_; 
v___x_284_ = 0;
v___x_285_ = l_Lean_Syntax_getRange_x3f(v_ref_282_, v___x_284_);
if (lean_obj_tag(v___x_285_) == 1)
{
lean_object* v_val_286_; lean_object* v_toBacktrackableState_287_; lean_object* v_shareCommonState_288_; lean_object* v_freshTagId_289_; lean_object* v_missingFormatters_290_; lean_object* v_partialFormatters_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_311_; 
v_val_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v___x_285_, 1);
v_toBacktrackableState_287_ = lean_ctor_get(v_a_283_, 0);
v_shareCommonState_288_ = lean_ctor_get(v_a_283_, 1);
v_freshTagId_289_ = lean_ctor_get(v_a_283_, 2);
v_missingFormatters_290_ = lean_ctor_get(v_a_283_, 3);
v_partialFormatters_291_ = lean_ctor_get(v_a_283_, 4);
v_isSharedCheck_311_ = !lean_is_exclusive(v_a_283_);
if (v_isSharedCheck_311_ == 0)
{
v___x_293_ = v_a_283_;
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_partialFormatters_291_);
lean_inc(v_missingFormatters_290_);
lean_inc(v_freshTagId_289_);
lean_inc(v_shareCommonState_288_);
lean_inc(v_toBacktrackableState_287_);
lean_dec(v_a_283_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v_snd_297_; lean_object* v_fst_298_; lean_object* v_fst_299_; lean_object* v_snd_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v___x_295_ = 1;
v___x_296_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_289_, v_toBacktrackableState_287_, v_doc_281_, v_val_286_, v___x_295_);
v_snd_297_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_snd_297_);
v_fst_298_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_fst_298_);
lean_dec_ref(v___x_296_);
v_fst_299_ = lean_ctor_get(v_snd_297_, 0);
v_snd_300_ = lean_ctor_get(v_snd_297_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_snd_297_);
if (v_isSharedCheck_310_ == 0)
{
v___x_302_ = v_snd_297_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_snd_300_);
lean_inc(v_fst_299_);
lean_dec(v_snd_297_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 2, v_fst_298_);
lean_ctor_set(v___x_293_, 0, v_fst_299_);
v___x_305_ = v___x_293_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_fst_299_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_shareCommonState_288_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_fst_298_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_missingFormatters_290_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_partialFormatters_291_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_305_);
lean_ctor_set(v___x_302_, 0, v_snd_300_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_snd_300_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v___x_285_);
v___x_312_ = lean_box(0);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v_doc_281_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_a_283_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg___boxed(lean_object* v_doc_315_, lean_object* v_ref_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_315_, v_ref_316_, v_a_317_);
lean_dec(v_ref_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode(lean_object* v_doc_319_, lean_object* v_ref_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_319_, v_ref_320_, v_a_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___boxed(lean_object* v_doc_324_, lean_object* v_ref_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Fmt_TaggedDoc_taggedNode(v_doc_324_, v_ref_325_, v_a_326_, v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_ref_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(lean_object* v_doc_329_, lean_object* v_range_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_toBacktrackableState_332_; lean_object* v_shareCommonState_333_; lean_object* v_freshTagId_334_; lean_object* v_missingFormatters_335_; lean_object* v_partialFormatters_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_356_; 
v_toBacktrackableState_332_ = lean_ctor_get(v_a_331_, 0);
v_shareCommonState_333_ = lean_ctor_get(v_a_331_, 1);
v_freshTagId_334_ = lean_ctor_get(v_a_331_, 2);
v_missingFormatters_335_ = lean_ctor_get(v_a_331_, 3);
v_partialFormatters_336_ = lean_ctor_get(v_a_331_, 4);
v_isSharedCheck_356_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_356_ == 0)
{
v___x_338_ = v_a_331_;
v_isShared_339_ = v_isSharedCheck_356_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_partialFormatters_336_);
lean_inc(v_missingFormatters_335_);
lean_inc(v_freshTagId_334_);
lean_inc(v_shareCommonState_333_);
lean_inc(v_toBacktrackableState_332_);
lean_dec(v_a_331_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_356_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v_snd_342_; lean_object* v_fst_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_355_; 
v___x_340_ = 0;
v___x_341_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_334_, v_toBacktrackableState_332_, v_doc_329_, v_range_330_, v___x_340_);
v_snd_342_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_snd_342_);
v_fst_343_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_fst_343_);
lean_dec_ref(v___x_341_);
v_fst_344_ = lean_ctor_get(v_snd_342_, 0);
v_snd_345_ = lean_ctor_get(v_snd_342_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_snd_342_);
if (v_isSharedCheck_355_ == 0)
{
v___x_347_ = v_snd_342_;
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snd_345_);
lean_inc(v_fst_344_);
lean_dec(v_snd_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 2, v_fst_343_);
lean_ctor_set(v___x_338_, 0, v_fst_344_);
v___x_350_ = v___x_338_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_fst_344_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_shareCommonState_333_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_fst_343_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_missingFormatters_335_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_partialFormatters_336_);
v___x_350_ = v_reuseFailAlloc_354_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___x_350_);
lean_ctor_set(v___x_347_, 0, v_snd_345_);
v___x_352_ = v___x_347_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_snd_345_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace(lean_object* v_doc_357_, lean_object* v_range_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(v_doc_357_, v_range_358_, v_a_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___boxed(lean_object* v_doc_362_, lean_object* v_range_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace(v_doc_362_, v_range_363_, v_a_364_, v_a_365_);
lean_dec_ref(v_a_364_);
return v_res_366_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isTagged(lean_object* v_d_367_){
_start:
{
lean_object* v_doc_368_; 
v_doc_368_ = lean_ctor_get(v_d_367_, 0);
if (lean_obj_tag(v_doc_368_) == 3)
{
uint8_t v___x_369_; 
v___x_369_ = 1;
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = 0;
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isTagged___boxed(lean_object* v_d_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Lean_Fmt_TaggedDoc_isTagged(v_d_371_);
lean_dec_ref(v_d_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg(lean_object* v_d_374_, lean_object* v_ref_375_, lean_object* v_a_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = l_Lean_Fmt_TaggedDoc_isTagged(v_d_374_);
if (v___x_377_ == 0)
{
lean_object* v_doc_378_; lean_object* v_metaData_379_; lean_object* v___x_380_; lean_object* v_a_381_; lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_398_; 
v_doc_378_ = lean_ctor_get(v_d_374_, 0);
lean_inc(v_doc_378_);
v_metaData_379_ = lean_ctor_get(v_d_374_, 1);
lean_inc(v_metaData_379_);
lean_dec_ref(v_d_374_);
v___x_380_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_378_, v_ref_375_, v_a_376_);
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_a_382_ = lean_ctor_get(v___x_380_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_398_ == 0)
{
v___x_384_ = v___x_380_;
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_doc_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_396_; 
v_doc_386_ = lean_ctor_get(v_a_381_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_a_381_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v_a_381_, 1);
lean_dec(v_unused_397_);
v___x_388_ = v_a_381_;
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_doc_386_);
lean_dec(v_a_381_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v_metaData_379_);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_doc_386_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_metaData_379_);
v___x_391_ = v_reuseFailAlloc_395_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_391_);
v___x_393_ = v___x_384_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_a_382_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_d_374_);
lean_ctor_set(v___x_399_, 1, v_a_376_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg___boxed(lean_object* v_d_400_, lean_object* v_ref_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_d_400_, v_ref_401_, v_a_402_);
lean_dec(v_ref_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag(lean_object* v_d_404_, lean_object* v_ref_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_d_404_, v_ref_405_, v_a_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___boxed(lean_object* v_d_409_, lean_object* v_ref_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Fmt_TaggedDoc_tag(v_d_409_, v_ref_410_, v_a_411_, v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_ref_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(lean_object* v_inst_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_v_416_; lean_object* v___x_417_; 
v_v_416_ = lean_ctor_get(v_x_415_, 0);
v___x_417_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_v_416_, v_inst_414_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed(lean_object* v_inst_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(v_inst_418_, v_x_419_);
lean_dec_ref(v_x_419_);
lean_dec(v_inst_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(lean_object* v_inst_421_, lean_object* v_d_422_){
_start:
{
lean_object* v_metaData_423_; lean_object* v___f_424_; lean_object* v___x_425_; 
v_metaData_423_ = lean_ctor_get(v_d_422_, 1);
lean_inc(v_metaData_423_);
lean_dec_ref(v_d_422_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_424_, 0, v_inst_421_);
v___x_425_ = l_List_findSome_x3f___redArg(v___f_424_, v_metaData_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f(lean_object* v_00_u03b1_426_, lean_object* v_inst_427_, lean_object* v_d_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v_inst_427_, v_d_428_);
return v___x_429_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_433_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2));
v___x_434_ = lean_unsigned_to_nat(14u);
v___x_435_ = lean_unsigned_to_nat(22u);
v___x_436_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1));
v___x_437_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0));
v___x_438_ = l_mkPanicMessageWithDecl(v___x_437_, v___x_436_, v___x_435_, v___x_434_, v___x_433_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_propagate_441_, lean_object* v_v_442_, lean_object* v_f_443_){
_start:
{
lean_object* v___y_445_; lean_object* v___x_448_; 
v___x_448_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_v_442_, v_inst_440_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3);
v___x_450_ = l_panic___redArg(v_inst_439_, v___x_449_);
v___y_445_ = v___x_450_;
goto v___jp_444_;
}
else
{
lean_object* v_val_451_; 
v_val_451_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v___x_448_, 1);
v___y_445_ = v_val_451_;
goto v___jp_444_;
}
v___jp_444_:
{
lean_object* v_r_446_; lean_object* v___x_447_; 
v_r_446_ = lean_apply_2(v_propagate_441_, v___y_445_, v_f_443_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v_inst_440_);
lean_ctor_set(v___x_447_, 1, v_r_446_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___boxed(lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_propagate_454_, lean_object* v_v_455_, lean_object* v_f_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(v_inst_452_, v_inst_453_, v_propagate_454_, v_v_455_, v_f_456_);
lean_dec(v_v_455_);
lean_dec(v_inst_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(lean_object* v_00_u03b1_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_propagate_461_, lean_object* v_v_462_, lean_object* v_f_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(v_inst_459_, v_inst_460_, v_propagate_461_, v_v_462_, v_f_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed(lean_object* v_00_u03b1_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_propagate_468_, lean_object* v_v_469_, lean_object* v_f_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(v_00_u03b1_465_, v_inst_466_, v_inst_467_, v_propagate_468_, v_v_469_, v_f_470_);
lean_dec(v_v_469_);
lean_dec(v_inst_466_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData___redArg(lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_d_474_, lean_object* v_metaData_475_, lean_object* v_propagate_476_){
_start:
{
lean_object* v_doc_477_; lean_object* v_metaData_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_489_; 
v_doc_477_ = lean_ctor_get(v_d_474_, 0);
v_metaData_478_ = lean_ctor_get(v_d_474_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_d_474_);
if (v_isSharedCheck_489_ == 0)
{
v___x_480_ = v_d_474_;
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_metaData_478_);
lean_inc(v_doc_477_);
lean_dec(v_d_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
lean_inc(v_inst_473_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_inst_473_);
lean_ctor_set(v___x_482_, 1, v_metaData_475_);
v___x_483_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed), 6, 4);
lean_closure_set(v___x_483_, 0, lean_box(0));
lean_closure_set(v___x_483_, 1, v_inst_472_);
lean_closure_set(v___x_483_, 2, v_inst_473_);
lean_closure_set(v___x_483_, 3, v_propagate_476_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_metaData_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_485_);
v___x_487_ = v___x_480_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_doc_477_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData(lean_object* v_00_u03b1_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_d_493_, lean_object* v_metaData_494_, lean_object* v_propagate_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v_inst_491_, v_inst_492_, v_d_493_, v_metaData_494_, v_propagate_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(lean_object* v_f_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
if (lean_obj_tag(v_a_498_) == 0)
{
lean_object* v___x_500_; 
lean_dec_ref(v_f_497_);
v___x_500_ = l_List_reverse___redArg(v_a_499_);
return v___x_500_;
}
else
{
lean_object* v_head_501_; lean_object* v_tail_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_520_; 
v_head_501_ = lean_ctor_get(v_a_498_, 0);
v_tail_502_ = lean_ctor_get(v_a_498_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_a_498_);
if (v_isSharedCheck_520_ == 0)
{
v___x_504_ = v_a_498_;
v_isShared_505_ = v_isSharedCheck_520_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_tail_502_);
lean_inc(v_head_501_);
lean_dec(v_a_498_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_520_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_v_506_; lean_object* v_propagate_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_519_; 
v_v_506_ = lean_ctor_get(v_head_501_, 0);
v_propagate_507_ = lean_ctor_get(v_head_501_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_head_501_);
if (v_isSharedCheck_519_ == 0)
{
v___x_509_ = v_head_501_;
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_propagate_507_);
lean_inc(v_v_506_);
lean_dec(v_head_501_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
lean_inc(v_propagate_507_);
lean_inc_ref(v_f_497_);
v___x_511_ = lean_apply_2(v_propagate_507_, v_v_506_, v_f_497_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_propagate_507_);
v___x_513_ = v_reuseFailAlloc_518_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v_a_499_);
lean_ctor_set(v___x_504_, 0, v___x_513_);
v___x_515_ = v___x_504_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_a_499_);
v___x_515_ = v_reuseFailAlloc_517_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v_a_498_ = v_tail_502_;
v_a_499_ = v___x_515_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateMetaData(lean_object* v_d_521_, lean_object* v_f_522_){
_start:
{
lean_object* v_doc_523_; lean_object* v_metaData_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_534_; 
v_doc_523_ = lean_ctor_get(v_d_521_, 0);
v_metaData_524_ = lean_ctor_get(v_d_521_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_d_521_);
if (v_isSharedCheck_534_ == 0)
{
v___x_526_ = v_d_521_;
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_metaData_524_);
lean_inc(v_doc_523_);
lean_dec(v_d_521_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
lean_inc_ref(v_f_522_);
v___x_528_ = lean_apply_1(v_f_522_, v_doc_523_);
v___x_529_ = lean_box(0);
v___x_530_ = l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(v_f_522_, v_metaData_524_, v___x_529_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___x_530_);
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_532_ = v___x_526_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(size_t v_sz_535_, size_t v_i_536_, lean_object* v_bs_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_lt(v_i_536_, v_sz_535_);
if (v___x_538_ == 0)
{
return v_bs_537_;
}
else
{
lean_object* v_v_539_; lean_object* v_doc_540_; lean_object* v___x_541_; lean_object* v_bs_x27_542_; size_t v___x_543_; size_t v___x_544_; lean_object* v___x_545_; 
v_v_539_ = lean_array_uget_borrowed(v_bs_537_, v_i_536_);
v_doc_540_ = lean_ctor_get(v_v_539_, 0);
lean_inc(v_doc_540_);
v___x_541_ = lean_unsigned_to_nat(0u);
v_bs_x27_542_ = lean_array_uset(v_bs_537_, v_i_536_, v___x_541_);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_add(v_i_536_, v___x_543_);
v___x_545_ = lean_array_uset(v_bs_x27_542_, v_i_536_, v_doc_540_);
v_i_536_ = v___x_544_;
v_bs_537_ = v___x_545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0___boxed(lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_bs_549_){
_start:
{
size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_sz_boxed_550_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_551_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_boxed_550_, v_i_boxed_551_, v_bs_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(lean_object* v_ds_553_, lean_object* v_f_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_array_get_size(v_ds_553_);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
size_t v_sz_558_; size_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_sz_558_ = lean_array_size(v_ds_553_);
v___x_559_ = ((size_t)0ULL);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_558_, v___x_559_, v_ds_553_);
v___x_561_ = lean_apply_1(v_f_554_, v___x_560_);
v___x_562_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_561_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec_ref(v_f_554_);
v___x_563_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_array_get(v___x_563_, v_ds_553_, v___x_564_);
lean_dec_ref(v_ds_553_);
return v___x_565_;
}
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_failure___closed__0(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(0);
v___x_567_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_failure(void){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_failure___closed__0, &l_Lean_Fmt_TaggedDoc_failure___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_failure___closed__0);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_newline(lean_object* v_flattened_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = l_Lean_Fmt_Doc_newline___override___redArg(v_flattened_569_);
v___x_571_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl___closed__0(void){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Fmt_Doc_nl___redArg();
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_nl___closed__0, &l_Lean_Fmt_TaggedDoc_nl___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_nl___closed__0);
v___x_574_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_nl___closed__1, &l_Lean_Fmt_TaggedDoc_nl___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_nl___closed__1);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break___closed__0(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Fmt_Doc_break___redArg();
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break___closed__1(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_break___closed__0, &l_Lean_Fmt_TaggedDoc_break___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_break___closed__0);
v___x_578_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_break___closed__1, &l_Lean_Fmt_TaggedDoc_break___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_break___closed__1);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__0(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__1(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_hardNl___closed__0, &l_Lean_Fmt_TaggedDoc_hardNl___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__0);
v___x_582_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl(void){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_hardNl___closed__1, &l_Lean_Fmt_TaggedDoc_hardNl___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__1);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object* v_s_584_, lean_object* v_ref_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_584_);
v___x_588_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_587_, v_ref_585_, v_a_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg___boxed(lean_object* v_s_589_, lean_object* v_ref_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Fmt_TaggedDoc_text___redArg(v_s_589_, v_ref_590_, v_a_591_);
lean_dec(v_ref_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text(lean_object* v_s_593_, lean_object* v_ref_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Fmt_TaggedDoc_text___redArg(v_s_593_, v_ref_594_, v_a_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___boxed(lean_object* v_s_598_, lean_object* v_ref_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Fmt_TaggedDoc_text(v_s_598_, v_ref_599_, v_a_600_, v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_ref_599_);
return v_res_602_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty___closed__0(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Fmt_Doc_empty___redArg();
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty___closed__1(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_empty___closed__0, &l_Lean_Fmt_TaggedDoc_empty___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_empty___closed__0);
v___x_605_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty(void){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_empty___closed__1, &l_Lean_Fmt_TaggedDoc_empty___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_empty___closed__1);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space___closed__1(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_space___closed__0));
v___x_609_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space___closed__2(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_space___closed__1, &l_Lean_Fmt_TaggedDoc_space___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_space___closed__1);
v___x_611_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space(void){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_space___closed__2, &l_Lean_Fmt_TaggedDoc_space___closed__2_once, _init_l_Lean_Fmt_TaggedDoc_space___closed__2);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object* v_d_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_nested___closed__0));
v___x_616_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_614_, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object* v_d_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_hardNested___closed__0));
v___x_620_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_618_, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_doublyNested(lean_object* v_d_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = l_Lean_Fmt_TaggedDoc_nested(v_d_621_);
v___x_623_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object* v_d_624_){
_start:
{
lean_object* v_doc_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_doc_625_ = lean_ctor_get(v_d_624_, 0);
lean_inc(v_doc_625_);
lean_dec_ref(v_d_624_);
v___x_626_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_625_);
v___x_627_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object* v_d_629_){
_start:
{
lean_object* v___f_630_; lean_object* v___x_631_; 
v___f_630_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_unflattenable___closed__0));
v___x_631_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_629_, v___f_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object* v_d_633_){
_start:
{
lean_object* v___f_634_; lean_object* v___x_635_; 
v___f_634_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_flattened___closed__0));
v___x_635_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_633_, v___f_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object* v_d_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0));
v___x_639_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_637_, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0(uint8_t v_onlyNonCumulative_640_, lean_object* v_d_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_640_, v_d_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed(lean_object* v_onlyNonCumulative_643_, lean_object* v_d_644_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_645_; lean_object* v_res_646_; 
v_onlyNonCumulative_boxed_645_ = lean_unbox(v_onlyNonCumulative_643_);
v_res_646_ = l_Lean_Fmt_TaggedDoc_unindented___lam__0(v_onlyNonCumulative_boxed_645_, v_d_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object* v_d_647_, uint8_t v_onlyNonCumulative_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___x_651_; 
v___x_649_ = lean_box(v_onlyNonCumulative_648_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed), 2, 1);
lean_closure_set(v___f_650_, 0, v___x_649_);
v___x_651_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_647_, v___f_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___boxed(lean_object* v_d_652_, lean_object* v_onlyNonCumulative_653_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_654_; lean_object* v_res_655_; 
v_onlyNonCumulative_boxed_654_ = lean_unbox(v_onlyNonCumulative_653_);
v_res_655_ = l_Lean_Fmt_TaggedDoc_unindented(v_d_652_, v_onlyNonCumulative_boxed_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_final(lean_object* v_d_657_){
_start:
{
lean_object* v___f_658_; lean_object* v___x_659_; 
v___f_658_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_final___closed__0));
v___x_659_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_657_, v___f_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_initial(lean_object* v_d_661_){
_start:
{
lean_object* v___f_662_; lean_object* v___x_663_; 
v___f_662_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_initial___closed__0));
v___x_663_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_661_, v___f_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_free(lean_object* v_d_665_){
_start:
{
lean_object* v___f_666_; lean_object* v___x_667_; 
v___f_666_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_free___closed__0));
v___x_667_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_665_, v___f_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded___lam__0(lean_object* v_p_668_, lean_object* v_d_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_668_, v_d_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object* v_p_671_, lean_object* v_d_672_){
_start:
{
lean_object* v___f_673_; lean_object* v___x_674_; 
v___f_673_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_guarded___lam__0), 2, 1);
lean_closure_set(v___f_673_, 0, v_p_671_);
v___x_674_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_672_, v___f_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0(lean_object* v_amount_675_, lean_object* v_d_676_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = l_Lean_Fmt_DefaultCost_ofFailureFallbackPenalty___redArg(v_amount_675_);
v___x_678_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_677_, v_d_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(lean_object* v_d_679_, lean_object* v_amount_680_){
_start:
{
lean_object* v___f_681_; lean_object* v___x_682_; 
v___f_681_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_681_, 0, v_amount_680_);
v___x_682_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_679_, v___f_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0(lean_object* v_amount_683_, lean_object* v_d_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = l_Lean_Fmt_DefaultCost_ofOverflowFallbackPenalty___redArg(v_amount_683_);
v___x_686_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_685_, v_d_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(lean_object* v_d_687_, lean_object* v_amount_688_){
_start:
{
lean_object* v___f_689_; lean_object* v___x_690_; 
v___f_689_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_689_, 0, v_amount_688_);
v___x_690_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_687_, v___f_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0(lean_object* v_amount_691_, lean_object* v_d_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(v_amount_691_);
v___x_694_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_693_, v_d_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(lean_object* v_d_695_, lean_object* v_amount_696_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_697_, 0, v_amount_696_);
v___x_698_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_695_, v___f_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_either(lean_object* v_a_699_, lean_object* v_b_700_){
_start:
{
lean_object* v_doc_701_; lean_object* v_doc_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_doc_701_ = lean_ctor_get(v_a_699_, 0);
lean_inc(v_doc_701_);
lean_dec_ref(v_a_699_);
v_doc_702_ = lean_ctor_get(v_b_700_, 0);
lean_inc(v_doc_702_);
lean_dec_ref(v_b_700_);
v___x_703_ = l_Lean_Fmt_Doc_either___override___redArg(v_doc_701_, v_doc_702_);
v___x_704_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object* v_ds_706_){
_start:
{
lean_object* v___f_707_; lean_object* v___x_708_; 
v___f_707_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_oneOf___closed__0));
v___x_708_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_706_, v___f_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnFailure(lean_object* v_d_709_, lean_object* v_fallback_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(v_fallback_710_, v___x_711_);
v___x_713_ = lean_unsigned_to_nat(2u);
v___x_714_ = lean_mk_empty_array_with_capacity(v___x_713_);
v___x_715_ = lean_array_push(v___x_714_, v_d_709_);
v___x_716_ = lean_array_push(v___x_715_, v___x_712_);
v___x_717_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(lean_object* v_d_718_, lean_object* v_fallback_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_fallback_719_, v___x_720_);
v___x_722_ = lean_unsigned_to_nat(2u);
v___x_723_ = lean_mk_empty_array_with_capacity(v___x_722_);
v___x_724_ = lean_array_push(v___x_723_, v_d_718_);
v___x_725_ = lean_array_push(v___x_724_, v___x_721_);
v___x_726_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnHeight(lean_object* v_d_727_, lean_object* v_fallback_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v_fallback_728_, v___x_729_);
v___x_731_ = lean_unsigned_to_nat(2u);
v___x_732_ = lean_mk_empty_array_with_capacity(v___x_731_);
v___x_733_ = lean_array_push(v___x_732_, v_d_727_);
v___x_734_ = lean_array_push(v___x_733_, v___x_730_);
v___x_735_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__0(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_736_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_737_ = l_Lean_Fmt_TaggedDoc_space;
v___x_738_ = lean_unsigned_to_nat(2u);
v___x_739_ = lean_mk_empty_array_with_capacity(v___x_738_);
v___x_740_ = lean_array_push(v___x_739_, v___x_737_);
v___x_741_ = lean_array_push(v___x_740_, v___x_736_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__1(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_softSpace___closed__0, &l_Lean_Fmt_TaggedDoc_softSpace___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__0);
v___x_743_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace(void){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_softSpace___closed__1, &l_Lean_Fmt_TaggedDoc_softSpace___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__1);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_append(lean_object* v_a_745_, lean_object* v_b_746_){
_start:
{
lean_object* v_doc_747_; lean_object* v_doc_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_doc_747_ = lean_ctor_get(v_a_745_, 0);
lean_inc(v_doc_747_);
lean_dec_ref(v_a_745_);
v_doc_748_ = lean_ctor_get(v_b_746_, 0);
lean_inc(v_doc_748_);
lean_dec_ref(v_b_746_);
v___x_749_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_747_, v_doc_748_);
v___x_750_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object* v_ds_752_){
_start:
{
lean_object* v___f_753_; lean_object* v___x_754_; 
v___f_753_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_join___closed__0));
v___x_754_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_752_, v___f_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing___lam__0(lean_object* v_sep_755_, lean_object* v_x_756_){
_start:
{
lean_object* v_doc_757_; lean_object* v___x_758_; 
v_doc_757_ = lean_ctor_get(v_sep_755_, 0);
lean_inc(v_doc_757_);
lean_dec_ref(v_sep_755_);
v___x_758_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_doc_757_, v_x_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing(lean_object* v_sep_759_, lean_object* v_ds_760_){
_start:
{
lean_object* v___f_761_; lean_object* v___x_762_; 
v___f_761_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_joinUsing___lam__0), 2, 1);
lean_closure_set(v___f_761_, 0, v_sep_759_);
v___x_762_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_760_, v___f_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith___lam__0(lean_object* v_sep_763_, lean_object* v_i_764_){
_start:
{
lean_object* v___x_765_; lean_object* v_flat_766_; lean_object* v_broken_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_776_; 
v___x_765_ = lean_apply_1(v_sep_763_, v_i_764_);
v_flat_766_ = lean_ctor_get(v___x_765_, 0);
v_broken_767_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_776_ == 0)
{
v___x_769_ = v___x_765_;
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_broken_767_);
lean_inc(v_flat_766_);
lean_dec(v___x_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_doc_771_; lean_object* v_doc_772_; lean_object* v___x_774_; 
v_doc_771_ = lean_ctor_get(v_flat_766_, 0);
lean_inc(v_doc_771_);
lean_dec(v_flat_766_);
v_doc_772_ = lean_ctor_get(v_broken_767_, 0);
lean_inc(v_doc_772_);
lean_dec(v_broken_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_doc_772_);
lean_ctor_set(v___x_769_, 0, v_doc_771_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_doc_771_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_doc_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith___lam__1(lean_object* v___f_777_, lean_object* v_x_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Fmt_Doc_fillWith___redArg(v_x_778_, v___f_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith___lam__1___boxed(lean_object* v___f_780_, lean_object* v_x_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Fmt_TaggedDoc_fillWith___lam__1(v___f_780_, v_x_781_);
lean_dec_ref(v_x_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWith(lean_object* v_ds_783_, lean_object* v_sep_784_){
_start:
{
lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___x_787_; 
v___f_785_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWith___lam__0), 2, 1);
lean_closure_set(v___f_785_, 0, v_sep_784_);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWith___lam__1___boxed), 2, 1);
lean_closure_set(v___f_786_, 0, v___f_785_);
v___x_787_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_783_, v___f_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object* v_ds_789_){
_start:
{
lean_object* v___f_790_; lean_object* v___x_791_; 
v___f_790_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fill___closed__0));
v___x_791_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_789_, v___f_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0(lean_object* v_wrap_792_, lean_object* v_d_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_doc_796_; 
v___x_794_ = l_Lean_Fmt_TaggedDoc_untagged(v_d_793_);
v___x_795_ = lean_apply_1(v_wrap_792_, v___x_794_);
v_doc_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_doc_796_);
lean_dec_ref(v___x_795_);
return v_doc_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1(lean_object* v___f_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_x_798_, v___f_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping(lean_object* v_ds_800_, lean_object* v_wrap_801_){
_start:
{
lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___x_804_; 
v___f_802_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_802_, 0, v_wrap_801_);
v___f_803_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1), 2, 1);
lean_closure_set(v___f_803_, 0, v___f_802_);
v___x_804_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_800_, v___f_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace(lean_object* v_ds_806_){
_start:
{
lean_object* v___f_807_; lean_object* v___x_808_; 
v___f_807_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0));
v___x_808_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_806_, v___f_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1(lean_object* v___f_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_x_810_, v___f_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(lean_object* v_ds_812_, lean_object* v_wrap_813_){
_start:
{
lean_object* v___f_814_; lean_object* v___f_815_; lean_object* v___x_816_; 
v___f_814_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_814_, 0, v_wrap_813_);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1), 2, 1);
lean_closure_set(v___f_815_, 0, v___f_814_);
v___x_816_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_812_, v___f_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object* v_as_817_, size_t v_i_818_, size_t v_stop_819_, lean_object* v_b_820_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = lean_usize_dec_eq(v_i_818_, v_stop_819_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; size_t v___x_824_; size_t v___x_825_; 
v___x_822_ = lean_array_uget_borrowed(v_as_817_, v_i_818_);
v___x_823_ = l_Array_append___redArg(v_b_820_, v___x_822_);
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_add(v_i_818_, v___x_824_);
v_i_818_ = v___x_825_;
v_b_820_ = v___x_823_;
goto _start;
}
else
{
return v_b_820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1___boxed(lean_object* v_as_827_, lean_object* v_i_828_, lean_object* v_stop_829_, lean_object* v_b_830_){
_start:
{
size_t v_i_boxed_831_; size_t v_stop_boxed_832_; lean_object* v_res_833_; 
v_i_boxed_831_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_stop_boxed_832_ = lean_unbox_usize(v_stop_829_);
lean_dec(v_stop_829_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(v_as_827_, v_i_boxed_831_, v_stop_boxed_832_, v_b_830_);
lean_dec_ref(v_as_827_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(size_t v_sz_834_, size_t v_i_835_, lean_object* v_bs_836_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = lean_usize_dec_lt(v_i_835_, v_sz_834_);
if (v___x_837_ == 0)
{
return v_bs_836_;
}
else
{
lean_object* v_v_838_; lean_object* v___x_839_; lean_object* v_bs_x27_840_; size_t v_sz_841_; size_t v___x_842_; lean_object* v___x_843_; size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
v_v_838_ = lean_array_uget(v_bs_836_, v_i_835_);
v___x_839_ = lean_unsigned_to_nat(0u);
v_bs_x27_840_ = lean_array_uset(v_bs_836_, v_i_835_, v___x_839_);
v_sz_841_ = lean_array_size(v_v_838_);
v___x_842_ = ((size_t)0ULL);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_841_, v___x_842_, v_v_838_);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_add(v_i_835_, v___x_844_);
v___x_846_ = lean_array_uset(v_bs_x27_840_, v_i_835_, v___x_843_);
v_i_835_ = v___x_845_;
v_bs_836_ = v___x_846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object* v_sz_848_, lean_object* v_i_849_, lean_object* v_bs_850_){
_start:
{
size_t v_sz_boxed_851_; size_t v_i_boxed_852_; lean_object* v_res_853_; 
v_sz_boxed_851_ = lean_unbox_usize(v_sz_848_);
lean_dec(v_sz_848_);
v_i_boxed_852_ = lean_unbox_usize(v_i_849_);
lean_dec(v_i_849_);
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(v_sz_boxed_851_, v_i_boxed_852_, v_bs_850_);
return v_res_853_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(lean_object* v_dss_858_){
_start:
{
lean_object* v___x_859_; lean_object* v___y_861_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_859_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1));
v___x_875_ = lean_array_get_size(v_dss_858_);
v___x_876_ = lean_nat_dec_lt(v___x_873_, v___x_875_);
if (v___x_876_ == 0)
{
v___y_861_ = v___x_874_;
goto v___jp_860_;
}
else
{
size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; 
v___x_877_ = ((size_t)0ULL);
v___x_878_ = lean_usize_of_nat(v___x_875_);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(v_dss_858_, v___x_877_, v___x_878_, v___x_874_);
v___y_861_ = v___x_879_;
goto v___jp_860_;
}
v___jp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_862_ = lean_array_get_size(v___y_861_);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_dec_eq(v___x_862_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; size_t v_sz_866_; size_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec_ref(v___y_861_);
v___x_865_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0, &l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0);
v_sz_866_ = lean_array_size(v_dss_858_);
v___x_867_ = ((size_t)0ULL);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(v_sz_866_, v___x_867_, v_dss_858_);
v___x_869_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v___x_865_, v___x_868_);
lean_dec_ref(v___x_868_);
v___x_870_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_869_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v_dss_858_);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_array_get(v___x_859_, v___y_861_, v___x_871_);
lean_dec_ref(v___y_861_);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0(size_t v_sz_880_, size_t v_i_881_, lean_object* v_bs_882_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = lean_usize_dec_lt(v_i_881_, v_sz_880_);
if (v___x_883_ == 0)
{
return v_bs_882_;
}
else
{
lean_object* v_v_884_; lean_object* v_v_885_; uint8_t v_allowFill_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_900_; 
v_v_884_ = lean_array_uget(v_bs_882_, v_i_881_);
v_v_885_ = lean_ctor_get(v_v_884_, 0);
v_allowFill_886_ = lean_ctor_get_uint8(v_v_884_, sizeof(void*)*1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_v_884_);
if (v_isSharedCheck_900_ == 0)
{
v___x_888_ = v_v_884_;
v_isShared_889_ = v_isSharedCheck_900_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_v_885_);
lean_dec(v_v_884_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_900_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v_doc_890_; lean_object* v___x_891_; lean_object* v_bs_x27_892_; lean_object* v___x_894_; 
v_doc_890_ = lean_ctor_get(v_v_885_, 0);
lean_inc(v_doc_890_);
lean_dec(v_v_885_);
v___x_891_ = lean_unsigned_to_nat(0u);
v_bs_x27_892_ = lean_array_uset(v_bs_882_, v_i_881_, v___x_891_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_doc_890_);
v___x_894_ = v___x_888_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_doc_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_899_, sizeof(void*)*1, v_allowFill_886_);
v___x_894_ = v_reuseFailAlloc_899_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_add(v_i_881_, v___x_895_);
v___x_897_ = lean_array_uset(v_bs_x27_892_, v_i_881_, v___x_894_);
v_i_881_ = v___x_896_;
v_bs_882_ = v___x_897_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0___boxed(lean_object* v_sz_901_, lean_object* v_i_902_, lean_object* v_bs_903_){
_start:
{
size_t v_sz_boxed_904_; size_t v_i_boxed_905_; lean_object* v_res_906_; 
v_sz_boxed_904_ = lean_unbox_usize(v_sz_901_);
lean_dec(v_sz_901_);
v_i_boxed_905_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0(v_sz_boxed_904_, v_i_boxed_905_, v_bs_903_);
return v_res_906_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_908_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object* v_ds_909_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_910_ = lean_array_get_size(v_ds_909_);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_dec_eq(v___x_910_, v___x_911_);
if (v___x_912_ == 0)
{
size_t v_sz_913_; size_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_sz_913_ = lean_array_size(v_ds_909_);
v___x_914_ = ((size_t)0ULL);
v___x_915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0(v_sz_913_, v___x_914_, v_ds_909_);
v___x_916_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v___x_915_);
v___x_917_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_916_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v_v_921_; 
v___x_918_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0);
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = lean_array_get(v___x_918_, v_ds_909_, v___x_919_);
lean_dec_ref(v_ds_909_);
v_v_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_v_921_);
lean_dec(v___x_920_);
return v_v_921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object* v_ds_922_, lean_object* v_wrap_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_924_ = lean_array_get_size(v_ds_922_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_dec_eq(v___x_924_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___f_927_; size_t v_sz_928_; size_t v___x_929_; lean_object* v_ds_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_927_, 0, v_wrap_923_);
v_sz_928_ = lean_array_size(v_ds_922_);
v___x_929_ = ((size_t)0ULL);
v_ds_930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsingSpace_spec__0(v_sz_928_, v___x_929_, v_ds_922_);
v___x_931_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_930_, v___f_927_);
v___x_932_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_931_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_v_936_; 
lean_dec_ref(v_wrap_923_);
v___x_933_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace___closed__0);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_array_get(v___x_933_, v_ds_922_, v___x_934_);
lean_dec_ref(v_ds_922_);
v_v_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_v_936_);
lean_dec(v___x_935_);
return v_v_936_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object* v_d_937_){
_start:
{
lean_object* v_doc_938_; uint8_t v___x_939_; 
v_doc_938_ = lean_ctor_get(v_d_937_, 0);
v___x_939_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object* v_d_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_d_940_);
lean_dec_ref(v_d_940_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(lean_object* v_d_943_){
_start:
{
lean_object* v_doc_944_; uint8_t v___x_945_; 
v_doc_944_ = lean_ctor_get(v_d_943_, 0);
v___x_945_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_doc_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty___boxed(lean_object* v_d_946_){
_start:
{
uint8_t v_res_947_; lean_object* v_r_948_; 
v_res_947_ = l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(v_d_946_);
lean_dec_ref(v_d_946_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isCompoundAtomic(lean_object* v_d_949_){
_start:
{
lean_object* v_doc_950_; uint8_t v___x_951_; 
v_doc_950_ = lean_ctor_get(v_d_949_, 0);
v___x_951_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_doc_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isCompoundAtomic___boxed(lean_object* v_d_952_){
_start:
{
uint8_t v_res_953_; lean_object* v_r_954_; 
v_res_953_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_d_952_);
lean_dec_ref(v_d_952_);
v_r_954_ = lean_box(v_res_953_);
return v_r_954_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object* v_d_955_){
_start:
{
lean_object* v_doc_956_; uint8_t v___x_957_; 
v_doc_956_ = lean_ctor_get(v_d_955_, 0);
v___x_957_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_doc_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAtomic___boxed(lean_object* v_d_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_d_958_);
lean_dec_ref(v_d_958_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instAppend___lam__0(lean_object* v_a_961_, lean_object* v_b_962_){
_start:
{
uint8_t v___x_963_; 
v___x_963_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_961_);
if (v___x_963_ == 0)
{
uint8_t v___x_964_; 
v___x_964_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_962_);
if (v___x_964_ == 0)
{
lean_object* v_doc_965_; lean_object* v_doc_966_; uint8_t v___x_967_; 
v_doc_965_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_doc_965_);
lean_dec_ref(v_a_961_);
v_doc_966_ = lean_ctor_get(v_b_962_, 0);
lean_inc(v_doc_966_);
lean_dec_ref(v_b_962_);
v___x_967_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_965_);
if (v___x_967_ == 0)
{
uint8_t v___x_968_; 
v___x_968_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_966_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_965_, v_doc_966_);
v___x_970_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_969_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; 
lean_dec(v_doc_966_);
v___x_971_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_965_);
return v___x_971_;
}
}
else
{
lean_object* v___x_972_; 
lean_dec(v_doc_965_);
v___x_972_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_966_);
return v___x_972_;
}
}
else
{
lean_dec_ref(v_b_962_);
return v_a_961_;
}
}
else
{
lean_dec_ref(v_a_961_);
return v_b_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___impl(uint8_t v_x_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_box(v_x_975_);
v___x_977_ = lean_obj_tag_nat(v___x_976_);
lean_dec(v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___impl___boxed(lean_object* v_x_978_){
_start:
{
uint8_t v_x_4__boxed_979_; lean_object* v_res_980_; 
v_x_4__boxed_979_ = lean_unbox(v_x_978_);
v_res_980_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___impl(v_x_4__boxed_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(lean_object* v_k_981_){
_start:
{
lean_inc(v_k_981_);
return v_k_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg___boxed(lean_object* v_k_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(v_k_982_);
lean_dec(v_k_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(lean_object* v_motive_984_, lean_object* v_ctorIdx_985_, uint8_t v_t_986_, lean_object* v_h_987_, lean_object* v_k_988_){
_start:
{
lean_inc(v_k_988_);
return v_k_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___boxed(lean_object* v_motive_989_, lean_object* v_ctorIdx_990_, lean_object* v_t_991_, lean_object* v_h_992_, lean_object* v_k_993_){
_start:
{
uint8_t v_t_boxed_994_; lean_object* v_res_995_; 
v_t_boxed_994_ = lean_unbox(v_t_991_);
v_res_995_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(v_motive_989_, v_ctorIdx_990_, v_t_boxed_994_, v_h_992_, v_k_993_);
lean_dec(v_k_993_);
lean_dec(v_ctorIdx_990_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(lean_object* v_coequal_996_){
_start:
{
lean_inc(v_coequal_996_);
return v_coequal_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg___boxed(lean_object* v_coequal_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(v_coequal_997_);
lean_dec(v_coequal_997_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(lean_object* v_motive_999_, uint8_t v_t_1000_, lean_object* v_h_1001_, lean_object* v_coequal_1002_){
_start:
{
lean_inc(v_coequal_1002_);
return v_coequal_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___boxed(lean_object* v_motive_1003_, lean_object* v_t_1004_, lean_object* v_h_1005_, lean_object* v_coequal_1006_){
_start:
{
uint8_t v_t_boxed_1007_; lean_object* v_res_1008_; 
v_t_boxed_1007_ = lean_unbox(v_t_1004_);
v_res_1008_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(v_motive_1003_, v_t_boxed_1007_, v_h_1005_, v_coequal_1006_);
lean_dec(v_coequal_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(lean_object* v_preferSticky_1009_){
_start:
{
lean_inc(v_preferSticky_1009_);
return v_preferSticky_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg___boxed(lean_object* v_preferSticky_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(v_preferSticky_1010_);
lean_dec(v_preferSticky_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(lean_object* v_motive_1012_, uint8_t v_t_1013_, lean_object* v_h_1014_, lean_object* v_preferSticky_1015_){
_start:
{
lean_inc(v_preferSticky_1015_);
return v_preferSticky_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___boxed(lean_object* v_motive_1016_, lean_object* v_t_1017_, lean_object* v_h_1018_, lean_object* v_preferSticky_1019_){
_start:
{
uint8_t v_t_boxed_1020_; lean_object* v_res_1021_; 
v_t_boxed_1020_ = lean_unbox(v_t_1017_);
v_res_1021_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(v_motive_1016_, v_t_boxed_1020_, v_h_1018_, v_preferSticky_1019_);
lean_dec(v_preferSticky_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(lean_object* v_preferUnsticky_1022_){
_start:
{
lean_inc(v_preferUnsticky_1022_);
return v_preferUnsticky_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg___boxed(lean_object* v_preferUnsticky_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(v_preferUnsticky_1023_);
lean_dec(v_preferUnsticky_1023_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(lean_object* v_motive_1025_, uint8_t v_t_1026_, lean_object* v_h_1027_, lean_object* v_preferUnsticky_1028_){
_start:
{
lean_inc(v_preferUnsticky_1028_);
return v_preferUnsticky_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___boxed(lean_object* v_motive_1029_, lean_object* v_t_1030_, lean_object* v_h_1031_, lean_object* v_preferUnsticky_1032_){
_start:
{
uint8_t v_t_boxed_1033_; lean_object* v_res_1034_; 
v_t_boxed_1033_ = lean_unbox(v_t_1030_);
v_res_1034_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(v_motive_1029_, v_t_boxed_1033_, v_h_1031_, v_preferUnsticky_1032_);
lean_dec(v_preferUnsticky_1032_);
return v_res_1034_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default(void){
_start:
{
uint8_t v___x_1035_; 
v___x_1035_ = 0;
return v___x_1035_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind(void){
_start:
{
uint8_t v___x_1036_; 
v___x_1036_ = 0;
return v___x_1036_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(uint8_t v_x_1037_, uint8_t v_y_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1039_ = lean_box(v_x_1037_);
v___x_1040_ = lean_obj_tag_nat(v___x_1039_);
lean_dec(v___x_1039_);
v___x_1041_ = lean_box(v_y_1038_);
v___x_1042_ = lean_obj_tag_nat(v___x_1041_);
lean_dec(v___x_1041_);
v___x_1043_ = lean_nat_dec_eq(v___x_1040_, v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq___boxed(lean_object* v_x_1044_, lean_object* v_y_1045_){
_start:
{
uint8_t v_x_24__boxed_1046_; uint8_t v_y_25__boxed_1047_; uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_x_24__boxed_1046_ = lean_unbox(v_x_1044_);
v_y_25__boxed_1047_ = lean_unbox(v_y_1045_);
v_res_1048_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_x_24__boxed_1046_, v_y_25__boxed_1047_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0(void){
_start:
{
uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = 0;
v___x_1053_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1054_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*1, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default(void){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0, &l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky(void){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___lam__0(lean_object* v_v_1068_, lean_object* v_f_1069_){
_start:
{
lean_object* v_stickyVariant_1070_; uint8_t v_kind_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1079_; 
v_stickyVariant_1070_ = lean_ctor_get(v_v_1068_, 0);
v_kind_1071_ = lean_ctor_get_uint8(v_v_1068_, sizeof(void*)*1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_v_1068_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1073_ = v_v_1068_;
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_stickyVariant_1070_);
lean_dec(v_v_1068_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_stickyVariant_1070_, v_f_1069_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1075_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
lean_ctor_set_uint8(v_reuseFailAlloc_1078_, sizeof(void*)*1, v_kind_1071_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object* v_nonStickyVariant_1081_, lean_object* v_stickyVariant_1082_, uint8_t v_kind_1083_){
_start:
{
lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___f_1084_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_sticky___closed__0));
v___x_1085_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_1086_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_1087_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1087_, 0, v_stickyVariant_1082_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1, v_kind_1083_);
v___x_1088_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1085_, v___x_1086_, v_nonStickyVariant_1081_, v___x_1087_, v___f_1084_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___boxed(lean_object* v_nonStickyVariant_1089_, lean_object* v_stickyVariant_1090_, lean_object* v_kind_1091_){
_start:
{
uint8_t v_kind_boxed_1092_; lean_object* v_res_1093_; 
v_kind_boxed_1092_ = lean_unbox(v_kind_1091_);
v_res_1093_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_1089_, v_stickyVariant_1090_, v_kind_boxed_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object* v_doc_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_1096_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1095_, v_doc_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(lean_object* v_doc_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_doc_1097_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_box(0);
return v___x_1099_;
}
else
{
lean_object* v_val_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1109_; 
v_val_1100_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1102_ = v___x_1098_;
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_val_1100_);
lean_dec(v___x_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
uint8_t v_kind_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v_kind_1104_ = lean_ctor_get_uint8(v_val_1100_, sizeof(void*)*1);
lean_dec(v_val_1100_);
v___x_1105_ = lean_box(v_kind_1104_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object* v_inner_1110_, lean_object* v_f_1111_, lean_object* v_kind_x3f_1112_){
_start:
{
lean_object* v_nonStickyOuter_1113_; lean_object* v___x_1114_; 
lean_inc_ref(v_f_1111_);
lean_inc_ref(v_inner_1110_);
v_nonStickyOuter_1113_ = lean_apply_1(v_f_1111_, v_inner_1110_);
v___x_1114_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_inner_1110_);
if (lean_obj_tag(v___x_1114_) == 1)
{
lean_object* v_val_1115_; lean_object* v_stickyVariant_1116_; uint8_t v_kind_1117_; lean_object* v_stickyOuter_1118_; 
v_val_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_val_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v_stickyVariant_1116_ = lean_ctor_get(v_val_1115_, 0);
lean_inc_ref(v_stickyVariant_1116_);
v_kind_1117_ = lean_ctor_get_uint8(v_val_1115_, sizeof(void*)*1);
lean_dec(v_val_1115_);
v_stickyOuter_1118_ = lean_apply_1(v_f_1111_, v_stickyVariant_1116_);
if (lean_obj_tag(v_kind_x3f_1112_) == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1113_, v_stickyOuter_1118_, v_kind_1117_);
return v___x_1119_;
}
else
{
lean_object* v_val_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; 
v_val_1120_ = lean_ctor_get(v_kind_x3f_1112_, 0);
v___x_1121_ = lean_unbox(v_val_1120_);
v___x_1122_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1113_, v_stickyOuter_1118_, v___x_1121_);
return v___x_1122_;
}
}
else
{
lean_dec(v___x_1114_);
lean_dec_ref(v_f_1111_);
return v_nonStickyOuter_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness___boxed(lean_object* v_inner_1123_, lean_object* v_f_1124_, lean_object* v_kind_x3f_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_inner_1123_, v_f_1124_, v_kind_x3f_1125_);
lean_dec(v_kind_x3f_1125_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___impl(lean_object* v_x_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_obj_tag_nat(v_x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___impl___boxed(lean_object* v_x_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___impl(v_x_1129_);
lean_dec(v_x_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(lean_object* v_t_1131_, lean_object* v_k_1132_){
_start:
{
if (lean_obj_tag(v_t_1131_) == 2)
{
uint8_t v_allowFlattening_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_allowFlattening_1133_ = lean_ctor_get_uint8(v_t_1131_, 0);
v___x_1134_ = lean_box(v_allowFlattening_1133_);
v___x_1135_ = lean_apply_1(v_k_1132_, v___x_1134_);
return v___x_1135_;
}
else
{
return v_k_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg___boxed(lean_object* v_t_1136_, lean_object* v_k_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1136_, v_k_1137_);
lean_dec(v_t_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(lean_object* v_motive_1139_, lean_object* v_ctorIdx_1140_, lean_object* v_t_1141_, lean_object* v_h_1142_, lean_object* v_k_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1141_, v_k_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___boxed(lean_object* v_motive_1145_, lean_object* v_ctorIdx_1146_, lean_object* v_t_1147_, lean_object* v_h_1148_, lean_object* v_k_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(v_motive_1145_, v_ctorIdx_1146_, v_t_1147_, v_h_1148_, v_k_1149_);
lean_dec(v_t_1147_);
lean_dec(v_ctorIdx_1146_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(lean_object* v_t_1151_, lean_object* v_coequal_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1151_, v_coequal_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg___boxed(lean_object* v_t_1154_, lean_object* v_coequal_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(v_t_1154_, v_coequal_1155_);
lean_dec(v_t_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(lean_object* v_motive_1157_, lean_object* v_t_1158_, lean_object* v_h_1159_, lean_object* v_coequal_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1158_, v_coequal_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___boxed(lean_object* v_motive_1162_, lean_object* v_t_1163_, lean_object* v_h_1164_, lean_object* v_coequal_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(v_motive_1162_, v_t_1163_, v_h_1164_, v_coequal_1165_);
lean_dec(v_t_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(lean_object* v_t_1167_, lean_object* v_preferUnsticky_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1167_, v_preferUnsticky_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg___boxed(lean_object* v_t_1170_, lean_object* v_preferUnsticky_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(v_t_1170_, v_preferUnsticky_1171_);
lean_dec(v_t_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(lean_object* v_motive_1173_, lean_object* v_t_1174_, lean_object* v_h_1175_, lean_object* v_preferUnsticky_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1174_, v_preferUnsticky_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___boxed(lean_object* v_motive_1178_, lean_object* v_t_1179_, lean_object* v_h_1180_, lean_object* v_preferUnsticky_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(v_motive_1178_, v_t_1179_, v_h_1180_, v_preferUnsticky_1181_);
lean_dec(v_t_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(lean_object* v_t_1183_, lean_object* v_preferSticky_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1183_, v_preferSticky_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg___boxed(lean_object* v_t_1186_, lean_object* v_preferSticky_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(v_t_1186_, v_preferSticky_1187_);
lean_dec(v_t_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(lean_object* v_motive_1189_, lean_object* v_t_1190_, lean_object* v_h_1191_, lean_object* v_preferSticky_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1190_, v_preferSticky_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___boxed(lean_object* v_motive_1194_, lean_object* v_t_1195_, lean_object* v_h_1196_, lean_object* v_preferSticky_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(v_motive_1194_, v_t_1195_, v_h_1196_, v_preferSticky_1197_);
lean_dec(v_t_1195_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(lean_object* v_s_1199_, uint8_t v_allowFlattening_1200_){
_start:
{
uint8_t v_kind_1201_; 
v_kind_1201_ = lean_ctor_get_uint8(v_s_1199_, sizeof(void*)*1);
switch(v_kind_1201_)
{
case 0:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_box(0);
return v___x_1202_;
}
case 1:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1203_, 0, v_allowFlattening_1200_);
return v___x_1203_;
}
default: 
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(1);
return v___x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky___boxed(lean_object* v_s_1205_, lean_object* v_allowFlattening_1206_){
_start:
{
uint8_t v_allowFlattening_boxed_1207_; lean_object* v_res_1208_; 
v_allowFlattening_boxed_1207_ = lean_unbox(v_allowFlattening_1206_);
v_res_1208_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_s_1205_, v_allowFlattening_boxed_1207_);
lean_dec_ref(v_s_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt(lean_object* v_doc_1209_, lean_object* v_stickyDoc_1210_, lean_object* v_cfg_1211_){
_start:
{
switch(lean_obj_tag(v_cfg_1211_))
{
case 0:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1210_);
v___x_1213_ = lean_unsigned_to_nat(2u);
v___x_1214_ = lean_mk_empty_array_with_capacity(v___x_1213_);
v___x_1215_ = lean_array_push(v___x_1214_, v___x_1212_);
v___x_1216_ = lean_array_push(v___x_1215_, v_doc_1209_);
v___x_1217_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1216_);
return v___x_1217_;
}
case 1:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1218_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1210_);
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v___x_1218_, v___x_1219_);
v___x_1221_ = lean_unsigned_to_nat(2u);
v___x_1222_ = lean_mk_empty_array_with_capacity(v___x_1221_);
v___x_1223_ = lean_array_push(v___x_1222_, v_doc_1209_);
v___x_1224_ = lean_array_push(v___x_1223_, v___x_1220_);
v___x_1225_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1224_);
return v___x_1225_;
}
default: 
{
uint8_t v_allowFlattening_1226_; 
v_allowFlattening_1226_ = lean_ctor_get_uint8(v_cfg_1211_, 0);
if (v_allowFlattening_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1227_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1210_);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1209_, v___x_1228_);
v___x_1230_ = lean_unsigned_to_nat(2u);
v___x_1231_ = lean_mk_empty_array_with_capacity(v___x_1230_);
v___x_1232_ = lean_array_push(v___x_1231_, v___x_1227_);
v___x_1233_ = lean_array_push(v___x_1232_, v___x_1229_);
v___x_1234_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1233_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1235_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1210_);
lean_inc_ref(v_doc_1209_);
v___x_1236_ = l_Lean_Fmt_TaggedDoc_flattened(v_doc_1209_);
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1209_, v___x_1237_);
v___x_1239_ = lean_unsigned_to_nat(3u);
v___x_1240_ = lean_mk_empty_array_with_capacity(v___x_1239_);
v___x_1241_ = lean_array_push(v___x_1240_, v___x_1235_);
v___x_1242_ = lean_array_push(v___x_1241_, v___x_1236_);
v___x_1243_ = lean_array_push(v___x_1242_, v___x_1238_);
v___x_1244_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1243_);
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt___boxed(lean_object* v_doc_1245_, lean_object* v_stickyDoc_1246_, lean_object* v_cfg_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1245_, v_stickyDoc_1246_, v_cfg_1247_);
lean_dec(v_cfg_1247_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0(lean_object* v_s_1250_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0));
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_s_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___lam__0(lean_object* v_doc_x3f_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_box(0);
v___x_1257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v_doc_x3f_1255_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object* v_doc_x3f_1260_, lean_object* v_sepBefore_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_sepBefore_1261_);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v_doc_x3f_1260_);
lean_ctor_set(v___x_1264_, 2, v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object* v_doc_x3f_1265_, lean_object* v_sepAfter_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_sepAfter_1266_);
v___x_1269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v_doc_x3f_1265_);
lean_ctor_set(v___x_1269_, 2, v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(lean_object* v_as_1270_, size_t v_i_1271_, size_t v_stop_1272_, lean_object* v_b_1273_){
_start:
{
lean_object* v___y_1275_; uint8_t v___x_1279_; 
v___x_1279_ = lean_usize_dec_eq(v_i_1271_, v_stop_1272_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v_doc_x3f_1281_; 
v___x_1280_ = lean_array_uget_borrowed(v_as_1270_, v_i_1271_);
v_doc_x3f_1281_ = lean_ctor_get(v___x_1280_, 1);
if (lean_obj_tag(v_doc_x3f_1281_) == 0)
{
v___y_1275_ = v_b_1273_;
goto v___jp_1274_;
}
else
{
lean_object* v_sepBefore_x3f_1282_; lean_object* v_sepAfter_x3f_1283_; lean_object* v_val_1284_; uint8_t v___x_1285_; 
v_sepBefore_x3f_1282_ = lean_ctor_get(v___x_1280_, 0);
v_sepAfter_x3f_1283_ = lean_ctor_get(v___x_1280_, 2);
v_val_1284_ = lean_ctor_get(v_doc_x3f_1281_, 0);
v___x_1285_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_inc(v_sepAfter_x3f_1283_);
lean_inc(v_val_1284_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_val_1284_);
lean_ctor_set(v___x_1286_, 1, v_sepAfter_x3f_1283_);
lean_inc(v_sepBefore_x3f_1282_);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v_sepBefore_x3f_1282_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_array_push(v_b_1273_, v___x_1287_);
v___y_1275_ = v___x_1288_;
goto v___jp_1274_;
}
else
{
v___y_1275_ = v_b_1273_;
goto v___jp_1274_;
}
}
}
else
{
return v_b_1273_;
}
v___jp_1274_:
{
size_t v___x_1276_; size_t v___x_1277_; 
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_i_1271_, v___x_1276_);
v_i_1271_ = v___x_1277_;
v_b_1273_ = v___y_1275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0___boxed(lean_object* v_as_1289_, lean_object* v_i_1290_, lean_object* v_stop_1291_, lean_object* v_b_1292_){
_start:
{
size_t v_i_boxed_1293_; size_t v_stop_boxed_1294_; lean_object* v_res_1295_; 
v_i_boxed_1293_ = lean_unbox_usize(v_i_1290_);
lean_dec(v_i_1290_);
v_stop_boxed_1294_ = lean_unbox_usize(v_stop_1291_);
lean_dec(v_stop_1291_);
v_res_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1289_, v_i_boxed_1293_, v_stop_boxed_1294_, v_b_1292_);
lean_dec_ref(v_as_1289_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(lean_object* v_as_1298_, lean_object* v_start_1299_, lean_object* v_stop_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0));
v___x_1302_ = lean_nat_dec_lt(v_start_1299_, v_stop_1300_);
if (v___x_1302_ == 0)
{
return v___x_1301_;
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_array_get_size(v_as_1298_);
v___x_1304_ = lean_nat_dec_le(v_stop_1300_, v___x_1303_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_nat_dec_lt(v_start_1299_, v___x_1303_);
if (v___x_1305_ == 0)
{
return v___x_1301_;
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_usize_of_nat(v_start_1299_);
v___x_1307_ = lean_usize_of_nat(v___x_1303_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1298_, v___x_1306_, v___x_1307_, v___x_1301_);
return v___x_1308_;
}
}
else
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_usize_of_nat(v_start_1299_);
v___x_1310_ = lean_usize_of_nat(v_stop_1300_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1298_, v___x_1309_, v___x_1310_, v___x_1301_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___boxed(lean_object* v_as_1312_, lean_object* v_start_1313_, lean_object* v_stop_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_as_1312_, v_start_1313_, v_stop_1314_);
lean_dec(v_stop_1314_);
lean_dec(v_start_1313_);
lean_dec_ref(v_as_1312_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(lean_object* v_cs_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_array_get_size(v_cs_1316_);
v___x_1319_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_cs_1316_, v___x_1317_, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs___boxed(lean_object* v_cs_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1320_);
lean_dec_ref(v_cs_1320_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(size_t v_sz_1322_, size_t v_i_1323_, lean_object* v_bs_1324_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_usize_dec_lt(v_i_1323_, v_sz_1322_);
if (v___x_1325_ == 0)
{
return v_bs_1324_;
}
else
{
lean_object* v_v_1326_; lean_object* v_snd_1327_; lean_object* v_fst_1328_; lean_object* v_fst_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1342_; 
v_v_1326_ = lean_array_uget_borrowed(v_bs_1324_, v_i_1323_);
v_snd_1327_ = lean_ctor_get(v_v_1326_, 1);
lean_inc(v_snd_1327_);
v_fst_1328_ = lean_ctor_get(v_v_1326_, 0);
lean_inc(v_fst_1328_);
v_fst_1329_ = lean_ctor_get(v_snd_1327_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_snd_1327_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v_snd_1327_, 1);
lean_dec(v_unused_1343_);
v___x_1331_ = v_snd_1327_;
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_fst_1329_);
lean_dec(v_snd_1327_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v_bs_x27_1334_; lean_object* v___x_1336_; 
v___x_1333_ = lean_unsigned_to_nat(0u);
v_bs_x27_1334_ = lean_array_uset(v_bs_1324_, v_i_1323_, v___x_1333_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v_fst_1329_);
lean_ctor_set(v___x_1331_, 0, v_fst_1328_);
v___x_1336_ = v___x_1331_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_fst_1328_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_fst_1329_);
v___x_1336_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1323_, v___x_1337_);
v___x_1339_ = lean_array_uset(v_bs_x27_1334_, v_i_1323_, v___x_1336_);
v_i_1323_ = v___x_1338_;
v_bs_1324_ = v___x_1339_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0___boxed(lean_object* v_sz_1344_, lean_object* v_i_1345_, lean_object* v_bs_1346_){
_start:
{
size_t v_sz_boxed_1347_; size_t v_i_boxed_1348_; lean_object* v_res_1349_; 
v_sz_boxed_1347_ = lean_unbox_usize(v_sz_1344_);
lean_dec(v_sz_1344_);
v_i_boxed_1348_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_boxed_1347_, v_i_boxed_1348_, v_bs_1346_);
return v_res_1349_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0);
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v___x_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(lean_object* v_upperBound_1356_, lean_object* v_a_1357_, lean_object* v_b_1358_){
_start:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_nat_dec_lt(v_a_1357_, v_upperBound_1356_);
if (v___x_1359_ == 0)
{
lean_dec(v_a_1357_);
return v_b_1358_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_snd_1362_; lean_object* v_snd_1363_; lean_object* v___x_1364_; lean_object* v_a_1366_; 
v___x_1360_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1361_ = lean_array_get_borrowed(v___x_1360_, v_b_1358_, v_a_1357_);
v_snd_1362_ = lean_ctor_get(v___x_1361_, 1);
v_snd_1363_ = lean_ctor_get(v_snd_1362_, 1);
v___x_1364_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1363_) == 1)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = lean_nat_add(v_a_1357_, v___x_1364_);
v___x_1370_ = lean_array_get_size(v_b_1358_);
v___x_1371_ = lean_nat_dec_lt(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_dec(v___x_1369_);
v_a_1366_ = v_b_1358_;
goto v___jp_1365_;
}
else
{
lean_object* v_v_1372_; lean_object* v_snd_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1383_; 
lean_inc_ref(v_snd_1363_);
v_v_1372_ = lean_array_fget(v_b_1358_, v___x_1369_);
v_snd_1373_ = lean_ctor_get(v_v_1372_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_v_1372_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; 
v_unused_1384_ = lean_ctor_get(v_v_1372_, 0);
lean_dec(v_unused_1384_);
v___x_1375_ = v_v_1372_;
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_snd_1373_);
lean_dec(v_v_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v_xs_x27_1378_; lean_object* v___x_1380_; 
v___x_1377_ = lean_box(0);
v_xs_x27_1378_ = lean_array_fset(v_b_1358_, v___x_1369_, v___x_1377_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_snd_1363_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_snd_1363_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_snd_1373_);
v___x_1380_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_array_fset(v_xs_x27_1378_, v___x_1369_, v___x_1380_);
lean_dec(v___x_1369_);
v_a_1366_ = v___x_1381_;
goto v___jp_1365_;
}
}
}
}
else
{
v_a_1366_ = v_b_1358_;
goto v___jp_1365_;
}
v___jp_1365_:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_nat_add(v_a_1357_, v___x_1364_);
lean_dec(v_a_1357_);
v_a_1357_ = v___x_1367_;
v_b_1358_ = v_a_1366_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___boxed(lean_object* v_upperBound_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1385_, v_a_1386_, v_b_1387_);
lean_dec(v_upperBound_1385_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(lean_object* v_upperBound_1389_, lean_object* v_a_1390_, lean_object* v_b_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_nat_dec_lt(v_a_1390_, v_upperBound_1389_);
if (v___x_1392_ == 0)
{
lean_dec(v_a_1390_);
return v_b_1391_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_snd_1396_; lean_object* v_snd_1397_; lean_object* v___x_1398_; lean_object* v_a_1400_; 
v___x_1393_ = lean_box(0);
v___x_1394_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1395_ = lean_array_get_borrowed(v___x_1394_, v_b_1391_, v_a_1390_);
v_snd_1396_ = lean_ctor_get(v___x_1395_, 1);
v_snd_1397_ = lean_ctor_get(v_snd_1396_, 1);
v___x_1398_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1397_) == 1)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v_fst_1405_; 
v___x_1403_ = lean_nat_add(v_a_1390_, v___x_1398_);
v___x_1404_ = lean_array_get_borrowed(v___x_1394_, v_b_1391_, v___x_1403_);
lean_dec(v___x_1403_);
v_fst_1405_ = lean_ctor_get(v___x_1404_, 0);
if (lean_obj_tag(v_fst_1405_) == 1)
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1406_ = lean_array_get_size(v_b_1391_);
v___x_1407_ = lean_nat_dec_lt(v_a_1390_, v___x_1406_);
if (v___x_1407_ == 0)
{
v_a_1400_ = v_b_1391_;
goto v___jp_1399_;
}
else
{
lean_object* v_v_1408_; lean_object* v_snd_1409_; lean_object* v_fst_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1429_; 
v_v_1408_ = lean_array_fget(v_b_1391_, v_a_1390_);
v_snd_1409_ = lean_ctor_get(v_v_1408_, 1);
v_fst_1410_ = lean_ctor_get(v_v_1408_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_v_1408_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1412_ = v_v_1408_;
v_isShared_1413_ = v_isSharedCheck_1429_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snd_1409_);
lean_inc(v_fst_1410_);
lean_dec(v_v_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1429_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_fst_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1427_; 
v_fst_1414_ = lean_ctor_get(v_snd_1409_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_snd_1409_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v_snd_1409_, 1);
lean_dec(v_unused_1428_);
v___x_1416_ = v_snd_1409_;
v_isShared_1417_ = v_isSharedCheck_1427_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_fst_1414_);
lean_dec(v_snd_1409_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1427_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v_xs_x27_1419_; lean_object* v___x_1421_; 
v___x_1418_ = lean_box(0);
v_xs_x27_1419_ = lean_array_fset(v_b_1391_, v_a_1390_, v___x_1418_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 1, v___x_1393_);
v___x_1421_ = v___x_1416_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_fst_1414_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1393_);
v___x_1421_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v___x_1421_);
v___x_1423_ = v___x_1412_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_fst_1410_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_array_fset(v_xs_x27_1419_, v_a_1390_, v___x_1423_);
v_a_1400_ = v___x_1424_;
goto v___jp_1399_;
}
}
}
}
}
}
else
{
v_a_1400_ = v_b_1391_;
goto v___jp_1399_;
}
}
else
{
v_a_1400_ = v_b_1391_;
goto v___jp_1399_;
}
v___jp_1399_:
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_nat_add(v_a_1390_, v___x_1398_);
lean_dec(v_a_1390_);
v_a_1390_ = v___x_1401_;
v_b_1391_ = v_a_1400_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg___boxed(lean_object* v_upperBound_1430_, lean_object* v_a_1431_, lean_object* v_b_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1430_, v_a_1431_, v_b_1432_);
lean_dec(v_upperBound_1430_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(lean_object* v_upperBound_1434_, lean_object* v_a_1435_, lean_object* v_b_1436_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_lt(v_a_1435_, v_upperBound_1434_);
if (v___x_1437_ == 0)
{
return v_b_1436_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_snd_1441_; lean_object* v_snd_1442_; lean_object* v___x_1443_; lean_object* v_a_1445_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1440_ = lean_array_get_borrowed(v___x_1439_, v_b_1436_, v_a_1435_);
v_snd_1441_ = lean_ctor_get(v___x_1440_, 1);
v_snd_1442_ = lean_ctor_get(v_snd_1441_, 1);
v___x_1443_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1442_) == 1)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_fst_1450_; 
v___x_1448_ = lean_nat_add(v_a_1435_, v___x_1443_);
v___x_1449_ = lean_array_get_borrowed(v___x_1439_, v_b_1436_, v___x_1448_);
lean_dec(v___x_1448_);
v_fst_1450_ = lean_ctor_get(v___x_1449_, 0);
if (lean_obj_tag(v_fst_1450_) == 1)
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = lean_array_get_size(v_b_1436_);
v___x_1452_ = lean_nat_dec_lt(v_a_1435_, v___x_1451_);
if (v___x_1452_ == 0)
{
v_a_1445_ = v_b_1436_;
goto v___jp_1444_;
}
else
{
lean_object* v_v_1453_; lean_object* v_snd_1454_; lean_object* v_fst_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1474_; 
v_v_1453_ = lean_array_fget(v_b_1436_, v_a_1435_);
v_snd_1454_ = lean_ctor_get(v_v_1453_, 1);
v_fst_1455_ = lean_ctor_get(v_v_1453_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_v_1453_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1457_ = v_v_1453_;
v_isShared_1458_ = v_isSharedCheck_1474_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_snd_1454_);
lean_inc(v_fst_1455_);
lean_dec(v_v_1453_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1474_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_fst_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1472_; 
v_fst_1459_ = lean_ctor_get(v_snd_1454_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_snd_1454_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_snd_1454_, 1);
lean_dec(v_unused_1473_);
v___x_1461_ = v_snd_1454_;
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_fst_1459_);
lean_dec(v_snd_1454_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v_xs_x27_1464_; lean_object* v___x_1466_; 
v___x_1463_ = lean_box(0);
v_xs_x27_1464_ = lean_array_fset(v_b_1436_, v_a_1435_, v___x_1463_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 1, v___x_1438_);
v___x_1466_ = v___x_1461_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_fst_1459_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v___x_1438_);
v___x_1466_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1468_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v___x_1466_);
v___x_1468_ = v___x_1457_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_fst_1455_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_array_fset(v_xs_x27_1464_, v_a_1435_, v___x_1468_);
v_a_1445_ = v___x_1469_;
goto v___jp_1444_;
}
}
}
}
}
}
else
{
v_a_1445_ = v_b_1436_;
goto v___jp_1444_;
}
}
else
{
v_a_1445_ = v_b_1436_;
goto v___jp_1444_;
}
v___jp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_nat_add(v_a_1435_, v___x_1443_);
v___x_1447_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1434_, v___x_1446_, v_a_1445_);
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg___boxed(lean_object* v_upperBound_1475_, lean_object* v_a_1476_, lean_object* v_b_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1475_, v_a_1476_, v_b_1477_);
lean_dec(v_a_1476_);
lean_dec(v_upperBound_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(lean_object* v_entries_1479_){
_start:
{
lean_object* v___x_1480_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1494_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1522_ = lean_array_get_size(v_entries_1479_);
v___x_1523_ = lean_nat_dec_lt(v___x_1480_, v___x_1522_);
if (v___x_1523_ == 0)
{
v___y_1494_ = v_entries_1479_;
goto v___jp_1493_;
}
else
{
lean_object* v_v_1524_; lean_object* v_snd_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1536_; 
v_v_1524_ = lean_array_fget(v_entries_1479_, v___x_1480_);
v_snd_1525_ = lean_ctor_get(v_v_1524_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_v_1524_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_v_1524_, 0);
lean_dec(v_unused_1537_);
v___x_1527_ = v_v_1524_;
v_isShared_1528_ = v_isSharedCheck_1536_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_snd_1525_);
lean_dec(v_v_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1536_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v_xs_x27_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1529_ = lean_box(0);
v_xs_x27_1530_ = lean_array_fset(v_entries_1479_, v___x_1480_, v___x_1529_);
v___x_1531_ = lean_box(0);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1531_);
v___x_1533_ = v___x_1527_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_snd_1525_);
v___x_1533_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_array_fset(v_xs_x27_1530_, v___x_1480_, v___x_1533_);
v___y_1494_ = v___x_1534_;
goto v___jp_1493_;
}
}
}
v___jp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; size_t v_sz_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v___x_1484_ = lean_array_get_size(v___y_1483_);
v___x_1485_ = lean_nat_sub(v___x_1484_, v___y_1482_);
v___x_1486_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v___x_1485_, v___x_1480_, v___y_1483_);
lean_dec(v___x_1485_);
v___x_1487_ = lean_array_get_size(v___x_1486_);
v___x_1488_ = lean_nat_sub(v___x_1487_, v___y_1482_);
v___x_1489_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v___x_1488_, v___x_1480_, v___x_1486_);
lean_dec(v___x_1488_);
v_sz_1490_ = lean_array_size(v___x_1489_);
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_1490_, v___x_1491_, v___x_1489_);
return v___x_1492_;
}
v___jp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1495_ = lean_array_get_size(v___y_1494_);
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_sub(v___x_1495_, v___x_1496_);
v___x_1498_ = lean_nat_dec_lt(v___x_1497_, v___x_1495_);
if (v___x_1498_ == 0)
{
lean_dec(v___x_1497_);
v___y_1482_ = v___x_1496_;
v___y_1483_ = v___y_1494_;
goto v___jp_1481_;
}
else
{
lean_object* v_v_1499_; lean_object* v_snd_1500_; lean_object* v_fst_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1521_; 
v_v_1499_ = lean_array_fget(v___y_1494_, v___x_1497_);
v_snd_1500_ = lean_ctor_get(v_v_1499_, 1);
v_fst_1501_ = lean_ctor_get(v_v_1499_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_v_1499_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1503_ = v_v_1499_;
v_isShared_1504_ = v_isSharedCheck_1521_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snd_1500_);
lean_inc(v_fst_1501_);
lean_dec(v_v_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1521_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_fst_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1519_; 
v_fst_1505_ = lean_ctor_get(v_snd_1500_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_snd_1500_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_snd_1500_, 1);
lean_dec(v_unused_1520_);
v___x_1507_ = v_snd_1500_;
v_isShared_1508_ = v_isSharedCheck_1519_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_fst_1505_);
lean_dec(v_snd_1500_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1519_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v_xs_x27_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1509_ = lean_box(0);
v_xs_x27_1510_ = lean_array_fset(v___y_1494_, v___x_1497_, v___x_1509_);
v___x_1511_ = lean_box(0);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___x_1511_);
v___x_1513_ = v___x_1507_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_fst_1505_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1513_);
v___x_1515_ = v___x_1503_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_fst_1501_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_array_fset(v_xs_x27_1510_, v___x_1497_, v___x_1515_);
lean_dec(v___x_1497_);
v___y_1482_ = v___x_1496_;
v___y_1483_ = v___x_1516_;
goto v___jp_1481_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(lean_object* v_upperBound_1538_, lean_object* v_inst_1539_, lean_object* v_R_1540_, lean_object* v_a_1541_, lean_object* v_b_1542_, lean_object* v_c_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1538_, v_a_1541_, v_b_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___boxed(lean_object* v_upperBound_1545_, lean_object* v_inst_1546_, lean_object* v_R_1547_, lean_object* v_a_1548_, lean_object* v_b_1549_, lean_object* v_c_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(v_upperBound_1545_, v_inst_1546_, v_R_1547_, v_a_1548_, v_b_1549_, v_c_1550_);
lean_dec(v_upperBound_1545_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(lean_object* v_upperBound_1552_, lean_object* v_inst_1553_, lean_object* v_R_1554_, lean_object* v_a_1555_, lean_object* v_b_1556_, lean_object* v_c_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1552_, v_a_1555_, v_b_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___boxed(lean_object* v_upperBound_1559_, lean_object* v_inst_1560_, lean_object* v_R_1561_, lean_object* v_a_1562_, lean_object* v_b_1563_, lean_object* v_c_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(v_upperBound_1559_, v_inst_1560_, v_R_1561_, v_a_1562_, v_b_1563_, v_c_1564_);
lean_dec(v_a_1562_);
lean_dec(v_upperBound_1559_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(lean_object* v_upperBound_1566_, lean_object* v_inst_1567_, lean_object* v_R_1568_, lean_object* v_a_1569_, lean_object* v_b_1570_, lean_object* v_c_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1566_, v_a_1569_, v_b_1570_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___boxed(lean_object* v_upperBound_1573_, lean_object* v_inst_1574_, lean_object* v_R_1575_, lean_object* v_a_1576_, lean_object* v_b_1577_, lean_object* v_c_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(v_upperBound_1573_, v_inst_1574_, v_R_1575_, v_a_1576_, v_b_1577_, v_c_1578_);
lean_dec(v_upperBound_1573_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(lean_object* v_as_1580_, size_t v_sz_1581_, size_t v_i_1582_, lean_object* v_b_1583_){
_start:
{
lean_object* v_a_1585_; uint8_t v___x_1589_; 
v___x_1589_ = lean_usize_dec_lt(v_i_1582_, v_sz_1581_);
if (v___x_1589_ == 0)
{
return v_b_1583_;
}
else
{
lean_object* v_a_1590_; lean_object* v_fst_1591_; 
v_a_1590_ = lean_array_uget_borrowed(v_as_1580_, v_i_1582_);
v_fst_1591_ = lean_ctor_get(v_a_1590_, 0);
if (lean_obj_tag(v_fst_1591_) == 1)
{
lean_object* v_val_1592_; lean_object* v_snd_1593_; lean_object* v_s_1594_; lean_object* v_wrap_1595_; lean_object* v___y_1597_; lean_object* v___y_1600_; uint8_t v___x_1611_; 
v_val_1592_ = lean_ctor_get(v_fst_1591_, 0);
v_snd_1593_ = lean_ctor_get(v_a_1590_, 1);
v_s_1594_ = lean_ctor_get(v_val_1592_, 0);
v_wrap_1595_ = lean_ctor_get(v_val_1592_, 1);
v___x_1611_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_s_1594_);
if (v___x_1611_ == 0)
{
uint8_t v___x_1612_; 
v___x_1612_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_snd_1593_);
if (v___x_1612_ == 0)
{
lean_object* v_doc_1613_; lean_object* v_doc_1614_; uint8_t v___x_1615_; 
v_doc_1613_ = lean_ctor_get(v_s_1594_, 0);
v_doc_1614_ = lean_ctor_get(v_snd_1593_, 0);
v___x_1615_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1613_);
if (v___x_1615_ == 0)
{
uint8_t v___x_1616_; 
v___x_1616_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1614_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_inc(v_doc_1614_);
lean_inc(v_doc_1613_);
v___x_1617_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1613_, v_doc_1614_);
v___x_1618_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1617_);
v___y_1600_ = v___x_1618_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1619_; 
lean_inc(v_doc_1613_);
v___x_1619_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1613_);
v___y_1600_ = v___x_1619_;
goto v___jp_1599_;
}
}
else
{
lean_object* v___x_1620_; 
lean_inc(v_doc_1614_);
v___x_1620_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1614_);
v___y_1600_ = v___x_1620_;
goto v___jp_1599_;
}
}
else
{
lean_inc_ref(v_s_1594_);
v___y_1600_ = v_s_1594_;
goto v___jp_1599_;
}
}
else
{
lean_inc(v_snd_1593_);
v___y_1600_ = v_snd_1593_;
goto v___jp_1599_;
}
v___jp_1596_:
{
lean_object* v___x_1598_; 
lean_inc_ref(v_wrap_1595_);
v___x_1598_ = lean_apply_1(v_wrap_1595_, v___y_1597_);
v_a_1585_ = v___x_1598_;
goto v___jp_1584_;
}
v___jp_1599_:
{
uint8_t v___x_1601_; 
v___x_1601_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_1600_);
if (v___x_1601_ == 0)
{
uint8_t v___x_1602_; 
v___x_1602_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_1583_);
if (v___x_1602_ == 0)
{
lean_object* v_doc_1603_; lean_object* v_doc_1604_; uint8_t v___x_1605_; 
v_doc_1603_ = lean_ctor_get(v___y_1600_, 0);
lean_inc(v_doc_1603_);
lean_dec_ref(v___y_1600_);
v_doc_1604_ = lean_ctor_get(v_b_1583_, 0);
lean_inc(v_doc_1604_);
lean_dec_ref(v_b_1583_);
v___x_1605_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1603_);
if (v___x_1605_ == 0)
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1604_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1603_, v_doc_1604_);
v___x_1608_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1607_);
v___y_1597_ = v___x_1608_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1609_; 
lean_dec(v_doc_1604_);
v___x_1609_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1603_);
v___y_1597_ = v___x_1609_;
goto v___jp_1596_;
}
}
else
{
lean_object* v___x_1610_; 
lean_dec(v_doc_1603_);
v___x_1610_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1604_);
v___y_1597_ = v___x_1610_;
goto v___jp_1596_;
}
}
else
{
lean_dec_ref(v_b_1583_);
v___y_1597_ = v___y_1600_;
goto v___jp_1596_;
}
}
else
{
lean_dec_ref(v___y_1600_);
v___y_1597_ = v_b_1583_;
goto v___jp_1596_;
}
}
}
else
{
lean_object* v_snd_1621_; uint8_t v___x_1622_; 
v_snd_1621_ = lean_ctor_get(v_a_1590_, 1);
v___x_1622_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_snd_1621_);
if (v___x_1622_ == 0)
{
uint8_t v___x_1623_; 
v___x_1623_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_1583_);
if (v___x_1623_ == 0)
{
lean_object* v_doc_1624_; lean_object* v_doc_1625_; uint8_t v___x_1626_; 
v_doc_1624_ = lean_ctor_get(v_snd_1621_, 0);
v_doc_1625_ = lean_ctor_get(v_b_1583_, 0);
lean_inc(v_doc_1625_);
lean_dec_ref(v_b_1583_);
v___x_1626_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1624_);
if (v___x_1626_ == 0)
{
uint8_t v___x_1627_; 
v___x_1627_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1625_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_inc(v_doc_1624_);
v___x_1628_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1624_, v_doc_1625_);
v___x_1629_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1628_);
v_a_1585_ = v___x_1629_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1630_; 
lean_dec(v_doc_1625_);
lean_inc(v_doc_1624_);
v___x_1630_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1624_);
v_a_1585_ = v___x_1630_;
goto v___jp_1584_;
}
}
else
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1625_);
v_a_1585_ = v___x_1631_;
goto v___jp_1584_;
}
}
else
{
lean_dec_ref(v_b_1583_);
lean_inc(v_snd_1621_);
v_a_1585_ = v_snd_1621_;
goto v___jp_1584_;
}
}
else
{
v_a_1585_ = v_b_1583_;
goto v___jp_1584_;
}
}
}
v___jp_1584_:
{
size_t v___x_1586_; size_t v___x_1587_; 
v___x_1586_ = ((size_t)1ULL);
v___x_1587_ = lean_usize_add(v_i_1582_, v___x_1586_);
v_i_1582_ = v___x_1587_;
v_b_1583_ = v_a_1585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0___boxed(lean_object* v_as_1632_, lean_object* v_sz_1633_, lean_object* v_i_1634_, lean_object* v_b_1635_){
_start:
{
size_t v_sz_boxed_1636_; size_t v_i_boxed_1637_; lean_object* v_res_1638_; 
v_sz_boxed_1636_ = lean_unbox_usize(v_sz_1633_);
lean_dec(v_sz_1633_);
v_i_boxed_1637_ = lean_unbox_usize(v_i_1634_);
lean_dec(v_i_1634_);
v_res_1638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v_as_1632_, v_sz_boxed_1636_, v_i_boxed_1637_, v_b_1635_);
lean_dec_ref(v_as_1632_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object* v_cs_1639_){
_start:
{
lean_object* v_entries_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_entries_1640_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1639_);
v___x_1641_ = lean_array_get_size(v_entries_1640_);
v___x_1642_ = lean_unsigned_to_nat(0u);
v___x_1643_ = lean_nat_dec_eq(v___x_1641_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_dec_eq(v___x_1641_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v_entries_1646_; lean_object* v_combined_1647_; lean_object* v___x_1648_; size_t v_sz_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v_entries_1646_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(v_entries_1640_);
v_combined_1647_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_1648_ = l_Array_reverse___redArg(v_entries_1646_);
v_sz_1649_ = lean_array_size(v___x_1648_);
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v___x_1648_, v_sz_1649_, v___x_1650_, v_combined_1647_);
lean_dec_ref(v___x_1648_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; lean_object* v_snd_1653_; lean_object* v_fst_1654_; 
v___x_1652_ = lean_array_fget(v_entries_1640_, v___x_1642_);
lean_dec_ref(v_entries_1640_);
v_snd_1653_ = lean_ctor_get(v___x_1652_, 1);
lean_inc(v_snd_1653_);
lean_dec(v___x_1652_);
v_fst_1654_ = lean_ctor_get(v_snd_1653_, 0);
lean_inc(v_fst_1654_);
lean_dec(v_snd_1653_);
return v_fst_1654_;
}
}
else
{
lean_object* v___x_1655_; 
lean_dec_ref(v_entries_1640_);
v___x_1655_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine___boxed(lean_object* v_cs_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Fmt_TaggedDoc_combine(v_cs_1656_);
lean_dec_ref(v_cs_1656_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object* v_lhs_1658_, lean_object* v_sep_1659_, lean_object* v_rhs_1660_, uint8_t v_allowFlattening_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v_nonStickyDoc_1671_; lean_object* v___x_1672_; 
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_lhs_1658_);
lean_inc_ref(v_sep_1659_);
lean_inc_ref(v___x_1662_);
v___x_1663_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1662_, v_sep_1659_);
v___x_1664_ = lean_box(0);
lean_inc_ref(v_rhs_1660_);
v___x_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_rhs_1660_);
v___x_1666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
lean_ctor_set(v___x_1666_, 2, v___x_1664_);
v___x_1667_ = lean_unsigned_to_nat(2u);
v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1667_);
lean_inc_ref(v___x_1668_);
v___x_1669_ = lean_array_push(v___x_1668_, v___x_1663_);
v___x_1670_ = lean_array_push(v___x_1669_, v___x_1666_);
v_nonStickyDoc_1671_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1670_);
lean_dec_ref(v___x_1670_);
v___x_1672_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_1660_);
if (lean_obj_tag(v___x_1672_) == 1)
{
lean_object* v_val_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1698_; 
v_val_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1698_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_val_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1698_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_wrap_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1696_; 
v_wrap_1677_ = lean_ctor_get(v_sep_1659_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_sep_1659_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v_sep_1659_, 0);
lean_dec(v_unused_1697_);
v___x_1679_ = v_sep_1659_;
v_isShared_1680_ = v_isSharedCheck_1696_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_wrap_1677_);
lean_dec(v_sep_1659_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1696_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v_stickyVariant_1681_; lean_object* v___x_1682_; lean_object* v_stickySep_1684_; 
v_stickyVariant_1681_ = lean_ctor_get(v_val_1673_, 0);
v___x_1682_ = l_Lean_Fmt_TaggedDoc_space;
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___x_1682_);
v_stickySep_1684_ = v___x_1679_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_wrap_1677_);
v_stickySep_1684_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1662_, v_stickySep_1684_);
lean_inc_ref(v_stickyVariant_1681_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v_stickyVariant_1681_);
v___x_1687_ = v___x_1675_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_stickyVariant_1681_);
v___x_1687_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v_stickyDoc_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1664_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
lean_ctor_set(v___x_1688_, 2, v___x_1664_);
v___x_1689_ = lean_array_push(v___x_1668_, v___x_1685_);
v___x_1690_ = lean_array_push(v___x_1689_, v___x_1688_);
v_stickyDoc_1691_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1690_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_1673_, v_allowFlattening_1661_);
lean_dec(v_val_1673_);
v___x_1693_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_1671_, v_stickyDoc_1691_, v___x_1692_);
lean_dec(v___x_1692_);
return v___x_1693_;
}
}
}
}
}
else
{
lean_dec(v___x_1672_);
lean_dec_ref(v___x_1668_);
lean_dec_ref_known(v___x_1662_, 1);
lean_dec_ref(v_sep_1659_);
return v_nonStickyDoc_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine___boxed(lean_object* v_lhs_1699_, lean_object* v_sep_1700_, lean_object* v_rhs_1701_, lean_object* v_allowFlattening_1702_){
_start:
{
uint8_t v_allowFlattening_boxed_1703_; lean_object* v_res_1704_; 
v_allowFlattening_boxed_1703_ = lean_unbox(v_allowFlattening_1702_);
v_res_1704_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_1699_, v_sep_1700_, v_rhs_1701_, v_allowFlattening_boxed_1703_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object* v_body_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(lean_object* v_f_1707_, size_t v_sz_1708_, size_t v_i_1709_, lean_object* v_bs_1710_){
_start:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_usize_dec_lt(v_i_1709_, v_sz_1708_);
if (v___x_1711_ == 0)
{
lean_dec_ref(v_f_1707_);
return v_bs_1710_;
}
else
{
lean_object* v_v_1712_; lean_object* v___x_1713_; lean_object* v_bs_x27_1714_; lean_object* v___y_1716_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v_v_1712_ = lean_array_uget(v_bs_1710_, v_i_1709_);
v___x_1713_ = lean_unsigned_to_nat(0u);
v_bs_x27_1714_ = lean_array_uset(v_bs_1710_, v_i_1709_, v___x_1713_);
v___x_1721_ = lean_usize_to_nat(v_i_1709_);
v___x_1722_ = lean_unsigned_to_nat(2u);
v___x_1723_ = lean_nat_mod(v___x_1721_, v___x_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_nat_dec_eq(v___x_1723_, v___x_1713_);
lean_dec(v___x_1723_);
if (v___x_1724_ == 0)
{
v___y_1716_ = v_v_1712_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1725_; 
lean_inc_ref(v_f_1707_);
v___x_1725_ = lean_apply_1(v_f_1707_, v_v_1712_);
v___y_1716_ = v___x_1725_;
goto v___jp_1715_;
}
v___jp_1715_:
{
size_t v___x_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_add(v_i_1709_, v___x_1717_);
v___x_1719_ = lean_array_uset(v_bs_x27_1714_, v_i_1709_, v___y_1716_);
v_i_1709_ = v___x_1718_;
v_bs_1710_ = v___x_1719_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg___boxed(lean_object* v_f_1726_, lean_object* v_sz_1727_, lean_object* v_i_1728_, lean_object* v_bs_1729_){
_start:
{
size_t v_sz_boxed_1730_; size_t v_i_boxed_1731_; lean_object* v_res_1732_; 
v_sz_boxed_1730_ = lean_unbox_usize(v_sz_1727_);
lean_dec(v_sz_1727_);
v_i_boxed_1731_ = lean_unbox_usize(v_i_1728_);
lean_dec(v_i_1728_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1726_, v_sz_boxed_1730_, v_i_boxed_1731_, v_bs_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(lean_object* v_a_1733_, lean_object* v_f_1734_){
_start:
{
size_t v_sz_1735_; size_t v___x_1736_; lean_object* v___x_1737_; 
v_sz_1735_ = lean_array_size(v_a_1733_);
v___x_1736_ = ((size_t)0ULL);
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1734_, v_sz_1735_, v___x_1736_, v_a_1733_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems(lean_object* v_sep_1738_, lean_object* v_a_1739_, lean_object* v_f_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(v_a_1739_, v_f_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___boxed(lean_object* v_sep_1742_, lean_object* v_a_1743_, lean_object* v_f_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems(v_sep_1742_, v_a_1743_, v_f_1744_);
lean_dec_ref(v_sep_1742_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(lean_object* v_f_1746_, lean_object* v_as_1747_, size_t v_sz_1748_, size_t v_i_1749_, lean_object* v_bs_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1746_, v_sz_1748_, v_i_1749_, v_bs_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___boxed(lean_object* v_f_1752_, lean_object* v_as_1753_, lean_object* v_sz_1754_, lean_object* v_i_1755_, lean_object* v_bs_1756_){
_start:
{
size_t v_sz_boxed_1757_; size_t v_i_boxed_1758_; lean_object* v_res_1759_; 
v_sz_boxed_1757_ = lean_unbox_usize(v_sz_1754_);
lean_dec(v_sz_1754_);
v_i_boxed_1758_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(v_f_1752_, v_as_1753_, v_sz_boxed_1757_, v_i_boxed_1758_, v_bs_1756_);
lean_dec_ref(v_as_1753_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_pushElem(lean_object* v_sep_1760_, lean_object* v_a_1761_, lean_object* v_elem_1762_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1763_ = lean_array_get_size(v_a_1761_);
v___x_1764_ = lean_unsigned_to_nat(2u);
v___x_1765_ = lean_nat_mod(v___x_1763_, v___x_1764_);
v___x_1766_ = lean_unsigned_to_nat(0u);
v___x_1767_ = lean_nat_dec_eq(v___x_1765_, v___x_1766_);
lean_dec(v___x_1765_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1768_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_1760_);
v___x_1769_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1768_);
v___x_1770_ = lean_mk_empty_array_with_capacity(v___x_1764_);
v___x_1771_ = lean_array_push(v___x_1770_, v___x_1769_);
v___x_1772_ = lean_array_push(v___x_1771_, v_elem_1762_);
v___x_1773_ = l_Array_append___redArg(v_a_1761_, v___x_1772_);
lean_dec_ref(v___x_1772_);
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; 
lean_dec_ref(v_sep_1760_);
v___x_1774_ = lean_array_push(v_a_1761_, v_elem_1762_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_array_get_size(v_a_1775_);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_add(v___x_1776_, v___x_1777_);
v___x_1779_ = lean_nat_shiftr(v___x_1778_, v___x_1777_);
lean_dec(v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg___boxed(lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1780_);
lean_dec_ref(v_a_1780_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems(lean_object* v_sep_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___boxed(lean_object* v_sep_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems(v_sep_1785_, v_a_1786_);
lean_dec_ref(v_a_1786_);
lean_dec_ref(v_sep_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0(lean_object* v_docs_1788_){
_start:
{
lean_inc_ref(v_docs_1788_);
return v_docs_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0___boxed(lean_object* v_docs_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0(v_docs_1789_);
lean_dec_ref(v_docs_1789_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg(){
_start:
{
lean_object* v___f_1793_; 
v___f_1793_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___boxed(lean_object* v___dummy_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg();
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(lean_object* v_sep_1796_){
_start:
{
lean_object* v___f_1797_; 
v___f_1797_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___boxed(lean_object* v_sep_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(v_sep_1798_);
lean_dec_ref(v_sep_1798_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg(){
_start:
{
lean_object* v___f_1801_; 
v___f_1801_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg___boxed(lean_object* v___dummy_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg();
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(lean_object* v_sep_1804_){
_start:
{
lean_object* v___f_1805_; 
v___f_1805_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___boxed(lean_object* v_sep_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(v_sep_1806_);
lean_dec_ref(v_sep_1806_);
return v_res_1807_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default(void){
_start:
{
uint8_t v___x_1808_; 
v___x_1808_ = 0;
return v___x_1808_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited(void){
_start:
{
uint8_t v___x_1809_; 
v___x_1809_ = 0;
return v___x_1809_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(uint8_t v_v_1818_, lean_object* v_x_1819_){
_start:
{
return v_v_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0___boxed(lean_object* v_v_1820_, lean_object* v_x_1821_){
_start:
{
uint8_t v_v_boxed_1822_; uint8_t v_res_1823_; lean_object* v_r_1824_; 
v_v_boxed_1822_ = lean_unbox(v_v_1820_);
v_res_1823_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(v_v_boxed_1822_, v_x_1821_);
lean_dec_ref(v_x_1821_);
v_r_1824_ = lean_box(v_res_1823_);
return v_r_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object* v_doc_1826_, uint8_t v_isBracketed_1827_){
_start:
{
lean_object* v___f_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___f_1828_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0));
v___x_1829_ = 0;
v___x_1830_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1831_ = lean_box(v___x_1829_);
v___x_1832_ = lean_box(v_isBracketed_1827_);
v___x_1833_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1831_, v___x_1830_, v_doc_1826_, v___x_1832_, v___f_1828_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___boxed(lean_object* v_doc_1834_, lean_object* v_isBracketed_1835_){
_start:
{
uint8_t v_isBracketed_boxed_1836_; lean_object* v_res_1837_; 
v_isBracketed_boxed_1836_ = lean_unbox(v_isBracketed_1835_);
v_res_1837_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_1834_, v_isBracketed_boxed_1836_);
return v_res_1837_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object* v_doc_1838_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1840_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1839_, v_doc_1838_);
if (lean_obj_tag(v___x_1840_) == 0)
{
uint8_t v___x_1841_; 
v___x_1841_ = 0;
return v___x_1841_;
}
else
{
uint8_t v___x_1842_; 
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = 1;
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isSelfDelimited___boxed(lean_object* v_doc_1843_){
_start:
{
uint8_t v_res_1844_; lean_object* v_r_1845_; 
v_res_1844_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1843_);
v_r_1845_ = lean_box(v_res_1844_);
return v_r_1845_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isBracketed(lean_object* v_doc_1846_){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1848_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1847_, v_doc_1846_);
if (lean_obj_tag(v___x_1848_) == 0)
{
uint8_t v___x_1849_; 
v___x_1849_ = 0;
return v___x_1849_;
}
else
{
lean_object* v_val_1850_; uint8_t v___x_1851_; 
v_val_1850_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_val_1850_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1851_ = lean_unbox(v_val_1850_);
lean_dec(v_val_1850_);
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isBracketed___boxed(lean_object* v_doc_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l_Lean_Fmt_TaggedDoc_isBracketed(v_doc_1852_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default(void){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_box(0);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback(void){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_box(0);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(lean_object* v_v_1865_, lean_object* v_x_1866_){
_start:
{
return v_v_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0___boxed(lean_object* v_v_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(v_v_1867_, v_x_1868_);
lean_dec_ref(v_x_1868_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object* v_doc_1871_){
_start:
{
lean_object* v___f_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___f_1872_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0));
v___x_1873_ = lean_box(0);
v___x_1874_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1875_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1873_, v___x_1874_, v_doc_1871_, v___x_1873_, v___f_1872_);
return v___x_1875_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object* v_doc_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1878_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1877_, v_doc_1876_);
if (lean_obj_tag(v___x_1878_) == 0)
{
uint8_t v___x_1879_; 
v___x_1879_ = 0;
return v___x_1879_;
}
else
{
uint8_t v___x_1880_; 
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = 1;
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isRawFallback___boxed(lean_object* v_doc_1881_){
_start:
{
uint8_t v_res_1882_; lean_object* v_r_1883_; 
v_res_1882_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1881_);
v_r_1883_ = lean_box(v_res_1882_);
return v_r_1883_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default(void){
_start:
{
uint8_t v___x_1884_; 
v___x_1884_ = 0;
return v___x_1884_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned(void){
_start:
{
uint8_t v___x_1885_; 
v___x_1885_ = 0;
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object* v_doc_1894_, uint8_t v_mustBeRespected_1895_){
_start:
{
lean_object* v___f_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___f_1896_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0));
v___x_1897_ = 0;
v___x_1898_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14_));
v___x_1899_ = lean_box(v___x_1897_);
v___x_1900_ = lean_box(v_mustBeRespected_1895_);
v___x_1901_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1899_, v___x_1898_, v_doc_1894_, v___x_1900_, v___f_1896_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___boxed(lean_object* v_doc_1902_, lean_object* v_mustBeRespected_1903_){
_start:
{
uint8_t v_mustBeRespected_boxed_1904_; lean_object* v_res_1905_; 
v_mustBeRespected_boxed_1904_ = lean_unbox(v_mustBeRespected_1903_);
v_res_1905_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_1902_, v_mustBeRespected_boxed_1904_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoAligned_x3f(lean_object* v_doc_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_14_));
v___x_1908_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1907_, v_doc_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object* v_doc_1909_){
_start:
{
uint8_t v___x_1910_; 
lean_inc_ref(v_doc_1909_);
v___x_1910_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1909_);
if (v___x_1910_ == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_doc_1909_);
if (v___x_1911_ == 0)
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1909_);
if (v___x_1912_ == 0)
{
uint8_t v___x_1913_; 
v___x_1913_ = 1;
return v___x_1913_;
}
else
{
return v___x_1910_;
}
}
else
{
lean_dec_ref(v_doc_1909_);
return v___x_1910_;
}
}
else
{
lean_dec_ref(v_doc_1909_);
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_needsAppBrackets___boxed(lean_object* v_doc_1914_){
_start:
{
uint8_t v_res_1915_; lean_object* v_r_1916_; 
v_res_1915_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_doc_1914_);
v_r_1916_ = lean_box(v_res_1915_);
return v_r_1916_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default(void){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1917_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented(void){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented(lean_object* v_indentedVariant_1928_, lean_object* v_dedentedVariant_1929_){
_start:
{
lean_object* v___f_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___f_1930_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0));
v___x_1931_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1932_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_1933_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1931_, v___x_1932_, v_indentedVariant_1928_, v_dedentedVariant_1929_, v___f_1930_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoDedented_x3f(lean_object* v_doc_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_1936_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1935_, v_doc_1934_);
return v___x_1936_;
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
