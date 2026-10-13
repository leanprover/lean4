// Lean compiler output
// Module: Lake.Toml.Elab.Expression
// Imports: public import Lake.Toml.Elab.Value meta import all Lake.Toml.Grammar
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_findIdx_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty___redArg();
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_Toml_RBDict_appendArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_elabSimpleKey(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Toml_elabVal(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_instInhabitedKeyTy_default;
LEAN_EXPORT uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "table"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "array"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "dotted"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix___boxed(lean_object*);
static const lean_array_object l_Lake_Toml_instInhabitedElabState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_instInhabitedElabState_default___closed__0 = (const lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__0_value;
static const lean_ctor_object l_Lake_Toml_instInhabitedElabState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__0_value)}};
static const lean_object* l_Lake_Toml_instInhabitedElabState_default___closed__1 = (const lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instInhabitedElabState_default = (const lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState = (const lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__1_value;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cannot redefine "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " key `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Toml"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpleKey"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 51, 117, 190, 121, 223, 170, 220)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "keyval"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 46, 78, 232, 161, 211, 209, 25)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ill-formed key-value pair syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "key"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 24, 166, 18, 184, 133, 165, 53)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ill-formed key syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7;
static const lean_array_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(internal) bad array key `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdTable"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 45, 156, 80, 41, 178, 181, 196)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed table syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "arrayTable"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 220, 56, 86, 146, 203, 81, 19)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "ill-formed array table syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed expression syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0 = (const lean_object*)&l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_elabToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "toml"};
static const lean_object* l_Lake_Toml_elabToml___closed__0 = (const lean_object*)&l_Lake_Toml_elabToml___closed__0_value;
static const lean_ctor_object l_Lake_Toml_elabToml___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_elabToml___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabToml___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_elabToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabToml___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_elabToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 110, 132, 157, 201, 185, 149, 61)}};
static const lean_object* l_Lake_Toml_elabToml___closed__1 = (const lean_object*)&l_Lake_Toml_elabToml___closed__1_value;
static const lean_string_object l_Lake_Toml_elabToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ill-formed TOML syntax"};
static const lean_object* l_Lake_Toml_elabToml___closed__2 = (const lean_object*)&l_Lake_Toml_elabToml___closed__2_value;
static lean_once_cell_t l_Lake_Toml_elabToml___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_elabToml___closed__3;
static const lean_ctor_object l_Lake_Toml_elabToml___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_elabToml___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabToml___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_elabToml___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabToml___closed__4_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value),LEAN_SCALAR_PTR_LITERAL(169, 19, 11, 35, 86, 242, 57, 11)}};
static const lean_object* l_Lake_Toml_elabToml___closed__4 = (const lean_object*)&l_Lake_Toml_elabToml___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(lean_object* v_value_22_){
_start:
{
lean_inc(v_value_22_);
return v_value_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg___boxed(lean_object* v_value_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(v_value_23_);
lean_dec(v_value_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_value_28_){
_start:
{
lean_inc(v_value_28_);
return v_value_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_value_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_value_32_);
lean_dec(v_value_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(lean_object* v_stdTable_35_){
_start:
{
lean_inc(v_stdTable_35_);
return v_stdTable_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg___boxed(lean_object* v_stdTable_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(v_stdTable_36_);
lean_dec(v_stdTable_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_stdTable_41_){
_start:
{
lean_inc(v_stdTable_41_);
return v_stdTable_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_stdTable_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_stdTable_45_);
lean_dec(v_stdTable_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(lean_object* v_array_48_){
_start:
{
lean_inc(v_array_48_);
return v_array_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg___boxed(lean_object* v_array_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(v_array_49_);
lean_dec(v_array_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_array_54_){
_start:
{
lean_inc(v_array_54_);
return v_array_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_array_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_array_58_);
lean_dec(v_array_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(lean_object* v_dottedPrefix_61_){
_start:
{
lean_inc(v_dottedPrefix_61_);
return v_dottedPrefix_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg___boxed(lean_object* v_dottedPrefix_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(v_dottedPrefix_62_);
lean_dec(v_dottedPrefix_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_dottedPrefix_67_){
_start:
{
lean_inc(v_dottedPrefix_67_);
return v_dottedPrefix_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_dottedPrefix_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_dottedPrefix_71_);
lean_dec(v_dottedPrefix_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(lean_object* v_headerPrefix_74_){
_start:
{
lean_inc(v_headerPrefix_74_);
return v_headerPrefix_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg___boxed(lean_object* v_headerPrefix_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(v_headerPrefix_75_);
lean_dec(v_headerPrefix_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_headerPrefix_80_){
_start:
{
lean_inc(v_headerPrefix_80_);
return v_headerPrefix_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_headerPrefix_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_headerPrefix_84_);
lean_dec(v_headerPrefix_84_);
return v_res_86_;
}
}
static uint8_t _init_l_Lake_Toml_instInhabitedKeyTy_default(void){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
}
static uint8_t _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy(void){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(uint8_t v_ty_94_){
_start:
{
switch(v_ty_94_)
{
case 0:
{
lean_object* v___x_95_; 
v___x_95_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0));
return v___x_95_;
}
case 1:
{
lean_object* v___x_96_; 
v___x_96_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1));
return v___x_96_;
}
case 2:
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2));
return v___x_97_;
}
case 3:
{
lean_object* v___x_98_; 
v___x_98_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3));
return v___x_98_;
}
default: 
{
lean_object* v___x_99_; 
v___x_99_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4));
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed(lean_object* v_ty_100_){
_start:
{
uint8_t v_ty_boxed_101_; lean_object* v_res_102_; 
v_ty_boxed_101_ = lean_unbox(v_ty_100_);
v_res_102_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v_ty_boxed_101_);
return v_res_102_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(uint8_t v_ty_105_){
_start:
{
switch(v_ty_105_)
{
case 1:
{
uint8_t v___x_106_; 
v___x_106_ = 1;
return v___x_106_;
}
case 4:
{
uint8_t v___x_107_; 
v___x_107_ = 1;
return v___x_107_;
}
case 3:
{
uint8_t v___x_108_; 
v___x_108_ = 1;
return v___x_108_;
}
default: 
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix___boxed(lean_object* v_ty_110_){
_start:
{
uint8_t v_ty_boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v_ty_boxed_111_ = lean_unbox(v_ty_110_);
v_res_112_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(v_ty_boxed_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
lean_ctor_set(v___x_127_, 3, v___x_126_);
lean_ctor_set(v___x_127_, 4, v___x_125_);
lean_ctor_set(v___x_127_, 5, v___x_125_);
lean_ctor_set(v___x_127_, 6, v___x_125_);
lean_ctor_set(v___x_127_, 7, v___x_125_);
lean_ctor_set(v___x_127_, 8, v___x_125_);
lean_ctor_set(v___x_127_, 9, v___x_125_);
lean_ctor_set(v___x_127_, 10, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(32u);
v___x_129_ = lean_mk_empty_array_with_capacity(v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_131_ = ((size_t)5ULL);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_unsigned_to_nat(32u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3);
v___x_136_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_132_);
lean_ctor_set(v___x_136_, 3, v___x_132_);
lean_ctor_set_usize(v___x_136_, 4, v___x_131_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = lean_box(1);
v___x_138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4);
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_137_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(lean_object* v_msgData_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; lean_object* v_toCold_146_; lean_object* v_env_147_; lean_object* v_options_148_; uint8_t v___x_149_; lean_object* v_env_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_145_ = lean_st_ref_get(v___y_143_);
v_toCold_146_ = lean_ctor_get(v___y_142_, 0);
v_env_147_ = lean_ctor_get(v___x_145_, 0);
lean_inc_ref(v_env_147_);
lean_dec(v___x_145_);
v_options_148_ = lean_ctor_get(v_toCold_146_, 2);
v___x_149_ = 0;
v_env_150_ = l_Lean_Environment_setRecordingDeps(v_env_147_, v___x_149_);
v___x_151_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2);
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_148_);
v___x_153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_153_, 0, v_env_150_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_152_);
lean_ctor_set(v___x_153_, 3, v_options_148_);
v___x_154_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_msgData_141_);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msgData_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(lean_object* v_msg_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_ref_165_; lean_object* v___x_166_; lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_ref_165_ = lean_ctor_get(v___y_162_, 2);
v___x_166_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_161_, v___y_162_, v___y_163_);
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
lean_inc(v_ref_165_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_ref_165_);
lean_ctor_set(v___x_171_, 1, v_a_167_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 1);
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg___boxed(lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(lean_object* v_ref_181_, lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_toCold_187_; lean_object* v_currRecDepth_188_; lean_object* v_ref_189_; uint16_t v_optionFlags_190_; uint8_t v_suppressElabErrors_191_; uint8_t v_isRecordingDeps_192_; lean_object* v_ref_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_toCold_187_ = lean_ctor_get(v___y_184_, 0);
v_currRecDepth_188_ = lean_ctor_get(v___y_184_, 1);
v_ref_189_ = lean_ctor_get(v___y_184_, 2);
v_optionFlags_190_ = lean_ctor_get_uint16(v___y_184_, sizeof(void*)*3);
v_suppressElabErrors_191_ = lean_ctor_get_uint8(v___y_184_, sizeof(void*)*3 + 2);
v_isRecordingDeps_192_ = lean_ctor_get_uint8(v___y_184_, sizeof(void*)*3 + 3);
v_ref_193_ = l_Lean_replaceRef(v_ref_181_, v_ref_189_);
lean_inc(v_currRecDepth_188_);
lean_inc_ref(v_toCold_187_);
v___x_194_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_194_, 0, v_toCold_187_);
lean_ctor_set(v___x_194_, 1, v_currRecDepth_188_);
lean_ctor_set(v___x_194_, 2, v_ref_193_);
lean_ctor_set_uint16(v___x_194_, sizeof(void*)*3, v_optionFlags_190_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*3 + 2, v_suppressElabErrors_191_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*3 + 3, v_isRecordingDeps_192_);
v___x_195_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_182_, v___x_194_, v___y_185_);
lean_dec_ref_known(v___x_194_, 3);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object* v_ref_196_, lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_196_, v_msg_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v_ref_196_);
return v_res_202_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object* v_as_212_, size_t v_i_213_, size_t v_stop_214_, lean_object* v_b_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_fst_221_; lean_object* v_snd_222_; uint8_t v___x_226_; 
v___x_226_ = lean_usize_dec_eq(v_i_213_, v_stop_214_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_array_uget_borrowed(v_as_212_, v_i_213_);
lean_inc(v___x_227_);
v___x_228_ = l_Lake_Toml_elabSimpleKey(v___x_227_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v_keyTys_230_; lean_object* v_arrKeyTys_231_; lean_object* v_arrParents_232_; lean_object* v_currArrKey_233_; lean_object* v_currKey_234_; lean_object* v_items_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v_keyTys_230_ = lean_ctor_get(v___y_216_, 0);
v_arrKeyTys_231_ = lean_ctor_get(v___y_216_, 1);
v_arrParents_232_ = lean_ctor_get(v___y_216_, 2);
v_currArrKey_233_ = lean_ctor_get(v___y_216_, 3);
v_currKey_234_ = lean_ctor_get(v___y_216_, 4);
v_items_235_ = lean_ctor_get(v___y_216_, 5);
v___x_236_ = l_Lean_Name_str___override(v_b_215_, v_a_229_);
v___x_237_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_230_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 1)
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_268_; 
v_val_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_268_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_268_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_268_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
uint8_t v___x_242_; 
v___x_242_ = lean_unbox(v_val_238_);
if (v___x_242_ == 3)
{
lean_del_object(v___x_240_);
lean_dec(v_val_238_);
v_fst_221_ = v___x_236_;
v_snd_222_ = v___y_216_;
goto v___jp_220_;
}
else
{
lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_243_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_244_ = lean_unbox(v_val_238_);
lean_dec(v_val_238_);
v___x_245_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_244_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 3);
lean_ctor_set(v___x_240_, 0, v___x_245_);
v___x_247_ = v___x_240_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_267_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_248_ = l_Lean_MessageData_ofFormat(v___x_247_);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_243_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_inc(v___x_236_);
v___x_252_ = l_Lean_MessageData_ofName(v___x_236_);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_227_, v___x_255_, v___y_216_, v___y_217_, v___y_218_);
lean_dec_ref(v___y_216_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v_snd_258_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_256_, 1);
v_snd_258_ = lean_ctor_get(v_a_257_, 1);
lean_inc(v_snd_258_);
lean_dec(v_a_257_);
v_fst_221_ = v___x_236_;
v_snd_222_ = v_snd_258_;
goto v___jp_220_;
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v___x_236_);
v_a_259_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_256_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_256_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_278_; 
lean_inc_ref(v_items_235_);
lean_inc(v_currKey_234_);
lean_inc(v_currArrKey_233_);
lean_inc(v_arrParents_232_);
lean_inc(v_arrKeyTys_231_);
lean_inc(v_keyTys_230_);
lean_dec(v___x_237_);
v_isSharedCheck_278_ = !lean_is_exclusive(v___y_216_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; lean_object* v_unused_280_; lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; 
v_unused_279_ = lean_ctor_get(v___y_216_, 5);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v___y_216_, 4);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v___y_216_, 3);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v___y_216_, 2);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v___y_216_, 1);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v___y_216_, 0);
lean_dec(v_unused_284_);
v___x_270_ = v___y_216_;
v_isShared_271_ = v_isSharedCheck_278_;
goto v_resetjp_269_;
}
else
{
lean_dec(v___y_216_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_278_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_272_ = 3;
v___x_273_ = lean_box(v___x_272_);
lean_inc(v___x_236_);
v___x_274_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_236_, v___x_273_, v_keyTys_230_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_274_);
v___x_276_ = v___x_270_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_arrKeyTys_231_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_arrParents_232_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_currArrKey_233_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_currKey_234_);
lean_ctor_set(v_reuseFailAlloc_277_, 5, v_items_235_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
v_fst_221_ = v___x_236_;
v_snd_222_ = v___x_276_;
goto v___jp_220_;
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v___y_216_);
lean_dec(v_b_215_);
v_a_285_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_228_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_228_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_b_215_);
lean_ctor_set(v___x_293_, 1, v___y_216_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
v___jp_220_:
{
size_t v___x_223_; size_t v___x_224_; 
v___x_223_ = ((size_t)1ULL);
v___x_224_ = lean_usize_add(v_i_213_, v___x_223_);
v_i_213_ = v___x_224_;
v_b_215_ = v_fst_221_;
v___y_216_ = v_snd_222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object* v_as_295_, lean_object* v_i_296_, lean_object* v_stop_297_, lean_object* v_b_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
size_t v_i_boxed_303_; size_t v_stop_boxed_304_; lean_object* v_res_305_; 
v_i_boxed_303_ = lean_unbox_usize(v_i_296_);
lean_dec(v_i_296_);
v_stop_boxed_304_ = lean_unbox_usize(v_stop_297_);
lean_dec(v_stop_297_);
v_res_305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_295_, v_i_boxed_303_, v_stop_boxed_304_, v_b_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec_ref(v_as_295_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object* v_ks_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_currKey_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_currKey_311_ = lean_ctor_get(v_a_307_, 4);
lean_inc(v_currKey_311_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_array_get_size(v_ks_306_);
v___x_314_ = lean_nat_dec_lt(v___x_312_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v_currKey_311_);
lean_ctor_set(v___x_315_, 1, v_a_307_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
else
{
uint8_t v___x_317_; 
v___x_317_ = lean_nat_dec_le(v___x_313_, v___x_313_);
if (v___x_317_ == 0)
{
if (v___x_314_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v_currKey_311_);
lean_ctor_set(v___x_318_, 1, v_a_307_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
else
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_320_ = ((size_t)0ULL);
v___x_321_ = lean_usize_of_nat(v___x_313_);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_306_, v___x_320_, v___x_321_, v_currKey_311_, v_a_307_, v_a_308_, v_a_309_);
return v___x_322_;
}
}
else
{
size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v___x_323_ = ((size_t)0ULL);
v___x_324_ = lean_usize_of_nat(v___x_313_);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_306_, v___x_323_, v___x_324_, v_currKey_311_, v_a_307_, v_a_308_, v_a_309_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object* v_ks_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_326_, v_a_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec_ref(v_ks_326_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_332_, lean_object* v_ref_333_, lean_object* v_msg_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_333_, v_msg_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_340_, lean_object* v_ref_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_340_, v_ref_341_, v_msg_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v_ref_341_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_349_, v___y_351_, v___y_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_355_, lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_355_, v_msg_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_362_, lean_object* v_as_363_, size_t v_i_364_, size_t v_stop_365_, lean_object* v_b_366_){
_start:
{
lean_object* v___y_368_; uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_eq(v_i_364_, v_stop_365_);
if (v___x_372_ == 0)
{
lean_object* v_fst_373_; uint8_t v___x_374_; 
v_fst_373_ = lean_ctor_get(v_b_366_, 0);
v___x_374_ = lean_unbox(v_fst_373_);
if (v___x_374_ == 0)
{
lean_object* v_snd_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_383_; 
v_snd_375_ = lean_ctor_get(v_b_366_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_b_366_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_b_366_, 0);
lean_dec(v_unused_384_);
v___x_377_ = v_b_366_;
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_snd_375_);
lean_dec(v_b_366_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_box(v___x_362_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_snd_375_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
v___y_368_ = v___x_381_;
goto v___jp_367_;
}
}
}
else
{
lean_object* v_snd_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_395_; 
v_snd_385_ = lean_ctor_get(v_b_366_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_b_366_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v_b_366_, 0);
lean_dec(v_unused_396_);
v___x_387_ = v_b_366_;
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snd_385_);
lean_dec(v_b_366_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_389_ = lean_array_uget_borrowed(v_as_363_, v_i_364_);
lean_inc(v___x_389_);
v___x_390_ = lean_array_push(v_snd_385_, v___x_389_);
v___x_391_ = lean_box(v___x_372_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v___x_390_);
lean_ctor_set(v___x_387_, 0, v___x_391_);
v___x_393_ = v___x_387_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___x_390_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
v___y_368_ = v___x_393_;
goto v___jp_367_;
}
}
}
}
else
{
return v_b_366_;
}
v___jp_367_:
{
size_t v___x_369_; size_t v___x_370_; 
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_364_, v___x_369_);
v_i_364_ = v___x_370_;
v_b_366_ = v___y_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_397_, lean_object* v_as_398_, lean_object* v_i_399_, lean_object* v_stop_400_, lean_object* v_b_401_){
_start:
{
uint8_t v___x_2936__boxed_402_; size_t v_i_boxed_403_; size_t v_stop_boxed_404_; lean_object* v_res_405_; 
v___x_2936__boxed_402_ = lean_unbox(v___x_397_);
v_i_boxed_403_ = lean_unbox_usize(v_i_399_);
lean_dec(v_i_399_);
v_stop_boxed_404_ = lean_unbox_usize(v_stop_400_);
lean_dec(v_stop_400_);
v_res_405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2936__boxed_402_, v_as_398_, v_i_boxed_403_, v_stop_boxed_404_, v_b_401_);
lean_dec_ref(v_as_398_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_413_, size_t v_i_414_, lean_object* v_bs_415_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = lean_usize_dec_lt(v_i_414_, v_sz_413_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v_bs_415_);
return v___x_417_;
}
else
{
lean_object* v_v_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_v_418_ = lean_array_uget(v_bs_415_, v_i_414_);
v___x_419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_418_);
v___x_420_ = l_Lean_Syntax_isOfKind(v_v_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_dec(v_v_418_);
lean_dec_ref(v_bs_415_);
v___x_421_ = lean_box(0);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v_bs_x27_423_; size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v_bs_x27_423_ = lean_array_uset(v_bs_415_, v_i_414_, v___x_422_);
v___x_424_ = ((size_t)1ULL);
v___x_425_ = lean_usize_add(v_i_414_, v___x_424_);
v___x_426_ = lean_array_uset(v_bs_x27_423_, v_i_414_, v_v_418_);
v_i_414_ = v___x_425_;
v_bs_415_ = v___x_426_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_428_, lean_object* v_i_429_, lean_object* v_bs_430_){
_start:
{
size_t v_sz_boxed_431_; size_t v_i_boxed_432_; lean_object* v_res_433_; 
v_sz_boxed_431_ = lean_unbox_usize(v_sz_428_);
lean_dec(v_sz_428_);
v_i_boxed_432_ = lean_unbox_usize(v_i_429_);
lean_dec(v_i_429_);
v_res_433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_431_, v_i_boxed_432_, v_bs_430_);
return v_res_433_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_441_ = l_Lean_stringToMessageData(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_452_);
v___x_458_ = l_Lean_Syntax_isOfKind(v_kv_452_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_460_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_452_, v___x_459_, v_a_453_, v_a_454_, v_a_455_);
lean_dec_ref(v_a_453_);
lean_dec(v_kv_452_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = l_Lean_Syntax_getArg(v_kv_452_, v___x_461_);
v___x_463_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_462_);
v___x_464_ = l_Lean_Syntax_isOfKind(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v_kv_452_);
v___x_465_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_466_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_462_, v___x_465_, v_a_453_, v_a_454_, v_a_455_);
lean_dec_ref(v_a_453_);
lean_dec(v___x_462_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; lean_object* v_v_468_; lean_object* v___y_470_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_467_ = lean_unsigned_to_nat(2u);
v_v_468_ = l_Lean_Syntax_getArg(v_kv_452_, v___x_467_);
lean_dec(v_kv_452_);
v___x_576_ = l_Lean_Syntax_getArg(v___x_462_, v___x_461_);
v___x_577_ = l_Lean_Syntax_getArgs(v___x_576_);
lean_dec(v___x_576_);
v___x_578_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_579_ = lean_array_get_size(v___x_577_);
v___x_580_ = lean_nat_dec_lt(v___x_461_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec_ref(v___x_577_);
v___y_470_ = v___x_578_;
goto v___jp_469_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; size_t v___x_583_; size_t v___x_584_; lean_object* v___x_585_; lean_object* v_snd_586_; 
v___x_581_ = lean_box(v___x_580_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_578_);
v___x_583_ = ((size_t)0ULL);
v___x_584_ = lean_usize_of_nat(v___x_579_);
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_464_, v___x_577_, v___x_583_, v___x_584_, v___x_582_);
lean_dec_ref(v___x_577_);
v_snd_586_ = lean_ctor_get(v___x_585_, 1);
lean_inc(v_snd_586_);
lean_dec_ref(v___x_585_);
v___y_470_ = v_snd_586_;
goto v___jp_469_;
}
v___jp_469_:
{
size_t v_sz_471_; size_t v___x_472_; lean_object* v___x_473_; 
v_sz_471_ = lean_array_size(v___y_470_);
v___x_472_ = ((size_t)0ULL);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_471_, v___x_472_, v___y_470_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v_v_468_);
v___x_474_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_475_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_462_, v___x_474_, v_a_453_, v_a_454_, v_a_455_);
lean_dec_ref(v_a_453_);
lean_dec(v___x_462_);
return v___x_475_;
}
else
{
lean_object* v_val_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v_tailKeyStx_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_val_476_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v___x_473_, 1);
v___x_477_ = lean_box(0);
v___x_478_ = lean_array_get_size(v_val_476_);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_sub(v___x_478_, v___x_479_);
v_tailKeyStx_481_ = lean_array_get(v___x_477_, v_val_476_, v___x_480_);
lean_dec(v___x_480_);
v___x_482_ = lean_array_pop(v_val_476_);
v___x_483_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_482_, v_a_453_, v_a_454_, v_a_455_);
lean_dec_ref(v___x_482_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_567_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v_fst_485_ = lean_ctor_get(v_a_484_, 0);
v_snd_486_ = lean_ctor_get(v_a_484_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_a_484_);
if (v_isSharedCheck_567_ == 0)
{
v___x_488_ = v_a_484_;
v_isShared_489_ = v_isSharedCheck_567_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snd_486_);
lean_inc(v_fst_485_);
lean_dec(v_a_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_567_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; 
lean_inc(v_tailKeyStx_481_);
v___x_490_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_481_, v_a_454_, v_a_455_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v_keyTys_492_; lean_object* v_arrKeyTys_493_; lean_object* v_arrParents_494_; lean_object* v_currArrKey_495_; lean_object* v_currKey_496_; lean_object* v_items_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v_keyTys_492_ = lean_ctor_get(v_snd_486_, 0);
v_arrKeyTys_493_ = lean_ctor_get(v_snd_486_, 1);
v_arrParents_494_ = lean_ctor_get(v_snd_486_, 2);
v_currArrKey_495_ = lean_ctor_get(v_snd_486_, 3);
v_currKey_496_ = lean_ctor_get(v_snd_486_, 4);
v_items_497_ = lean_ctor_get(v_snd_486_, 5);
v___x_498_ = l_Lean_Name_str___override(v_fst_485_, v_a_491_);
v___x_499_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_492_, v___x_498_);
if (lean_obj_tag(v___x_499_) == 1)
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_519_; 
lean_del_object(v___x_488_);
lean_dec(v_v_468_);
lean_dec(v___x_462_);
v_val_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_519_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_519_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_519_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_505_ = lean_unbox(v_val_500_);
lean_dec(v_val_500_);
v___x_506_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_505_);
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 3);
lean_ctor_set(v___x_502_, 0, v___x_506_);
v___x_508_ = v___x_502_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_518_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_509_ = l_Lean_MessageData_ofFormat(v___x_508_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_504_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = l_Lean_MessageData_ofName(v___x_498_);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_481_, v___x_516_, v_snd_486_, v_a_454_, v_a_455_);
lean_dec(v_snd_486_);
lean_dec(v_tailKeyStx_481_);
return v___x_517_;
}
}
}
else
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_552_; 
lean_inc_ref(v_items_497_);
lean_inc(v_currKey_496_);
lean_inc(v_currArrKey_495_);
lean_inc(v_arrParents_494_);
lean_inc(v_arrKeyTys_493_);
lean_inc(v_keyTys_492_);
lean_dec(v___x_499_);
lean_dec(v_tailKeyStx_481_);
v_isSharedCheck_552_ = !lean_is_exclusive(v_snd_486_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; lean_object* v_unused_554_; lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; 
v_unused_553_ = lean_ctor_get(v_snd_486_, 5);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v_snd_486_, 4);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_snd_486_, 3);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_snd_486_, 2);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_snd_486_, 1);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_snd_486_, 0);
lean_dec(v_unused_558_);
v___x_521_ = v_snd_486_;
v_isShared_522_ = v_isSharedCheck_552_;
goto v_resetjp_520_;
}
else
{
lean_dec(v_snd_486_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_552_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lake_Toml_elabVal(v_v_468_, v_a_454_, v_a_455_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_543_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_543_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_543_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_543_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_528_ = lean_box(0);
v___x_529_ = 0;
v___x_530_ = lean_box(v___x_529_);
lean_inc(v___x_498_);
v___x_531_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_498_, v___x_530_, v_keyTys_492_);
v___x_532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_532_, 0, v___x_462_);
lean_ctor_set(v___x_532_, 1, v___x_498_);
lean_ctor_set(v___x_532_, 2, v_a_524_);
v___x_533_ = lean_array_push(v_items_497_, v___x_532_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 5, v___x_533_);
lean_ctor_set(v___x_521_, 0, v___x_531_);
v___x_535_ = v___x_521_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_arrKeyTys_493_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_arrParents_494_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_currArrKey_495_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_currKey_496_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v___x_533_);
v___x_535_ = v_reuseFailAlloc_542_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_535_);
lean_ctor_set(v___x_488_, 0, v___x_528_);
v___x_537_ = v___x_488_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_535_);
v___x_537_ = v_reuseFailAlloc_541_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_539_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_537_);
v___x_539_ = v___x_526_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_del_object(v___x_521_);
lean_dec(v___x_498_);
lean_dec_ref(v_items_497_);
lean_dec(v_currKey_496_);
lean_dec(v_currArrKey_495_);
lean_dec(v_arrParents_494_);
lean_dec(v_arrKeyTys_493_);
lean_dec(v_keyTys_492_);
lean_del_object(v___x_488_);
lean_dec(v___x_462_);
v_a_544_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_523_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_523_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_del_object(v___x_488_);
lean_dec(v_snd_486_);
lean_dec(v_fst_485_);
lean_dec(v_tailKeyStx_481_);
lean_dec(v_v_468_);
lean_dec(v___x_462_);
v_a_559_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_490_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_490_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec(v_tailKeyStx_481_);
lean_dec(v_v_468_);
lean_dec(v___x_462_);
v_a_568_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_483_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_483_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_592_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_595_ = l_Lean_stringToMessageData(v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_596_, size_t v_i_597_, size_t v_stop_598_, lean_object* v_b_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_fst_605_; lean_object* v_snd_606_; uint8_t v___x_610_; 
v___x_610_ = lean_usize_dec_eq(v_i_597_, v_stop_598_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_array_uget_borrowed(v_as_596_, v_i_597_);
lean_inc(v___x_611_);
v___x_612_ = l_Lake_Toml_elabSimpleKey(v___x_611_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v_keyTys_614_; lean_object* v_arrKeyTys_615_; lean_object* v_arrParents_616_; lean_object* v_currArrKey_617_; lean_object* v_currKey_618_; lean_object* v_items_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v_keyTys_614_ = lean_ctor_get(v___y_600_, 0);
v_arrKeyTys_615_ = lean_ctor_get(v___y_600_, 1);
v_arrParents_616_ = lean_ctor_get(v___y_600_, 2);
v_currArrKey_617_ = lean_ctor_get(v___y_600_, 3);
v_currKey_618_ = lean_ctor_get(v___y_600_, 4);
v_items_619_ = lean_ctor_get(v___y_600_, 5);
v___x_620_ = l_Lean_Name_str___override(v_b_599_, v_a_613_);
v___x_621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_614_, v___x_620_);
if (lean_obj_tag(v___x_621_) == 1)
{
lean_object* v_val_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_683_; 
v_val_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_683_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_683_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_val_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_683_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
uint8_t v___x_626_; 
v___x_626_ = lean_unbox(v_val_622_);
switch(v___x_626_)
{
case 2:
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_651_; 
lean_inc_ref(v_items_619_);
lean_inc(v_currKey_618_);
lean_inc(v_arrParents_616_);
lean_inc(v_arrKeyTys_615_);
lean_del_object(v___x_624_);
lean_dec(v_val_622_);
v_isSharedCheck_651_ = !lean_is_exclusive(v___y_600_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; lean_object* v_unused_657_; 
v_unused_652_ = lean_ctor_get(v___y_600_, 5);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v___y_600_, 4);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v___y_600_, 3);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v___y_600_, 2);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v___y_600_, 1);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v___y_600_, 0);
lean_dec(v_unused_657_);
v___x_628_ = v___y_600_;
v_isShared_629_ = v_isSharedCheck_651_;
goto v_resetjp_627_;
}
else
{
lean_dec(v___y_600_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_651_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_615_, v___x_620_);
if (lean_obj_tag(v___x_630_) == 1)
{
lean_object* v_val_631_; lean_object* v___x_633_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
lean_inc(v___x_620_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 3, v___x_620_);
lean_ctor_set(v___x_628_, 0, v_val_631_);
v___x_633_ = v___x_628_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_val_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_arrKeyTys_615_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_arrParents_616_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v_currKey_618_);
lean_ctor_set(v_reuseFailAlloc_634_, 5, v_items_619_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
v_fst_605_ = v___x_620_;
v_snd_606_ = v___x_633_;
goto v___jp_604_;
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v___x_630_);
lean_del_object(v___x_628_);
lean_dec_ref(v_items_619_);
lean_dec(v_currKey_618_);
lean_dec(v_arrParents_616_);
lean_dec(v_arrKeyTys_615_);
v___x_635_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_620_);
v___x_636_ = l_Lean_MessageData_ofName(v___x_620_);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_639_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v_snd_642_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v_snd_642_ = lean_ctor_get(v_a_641_, 1);
lean_inc(v_snd_642_);
lean_dec(v_a_641_);
v_fst_605_ = v___x_620_;
v_snd_606_ = v_snd_642_;
goto v___jp_604_;
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v___x_620_);
v_a_643_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_640_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_640_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
case 1:
{
lean_del_object(v___x_624_);
lean_dec(v_val_622_);
v_fst_605_ = v___x_620_;
v_snd_606_ = v___y_600_;
goto v___jp_604_;
}
case 4:
{
lean_del_object(v___x_624_);
lean_dec(v_val_622_);
v_fst_605_ = v___x_620_;
v_snd_606_ = v___y_600_;
goto v___jp_604_;
}
case 3:
{
lean_del_object(v___x_624_);
lean_dec(v_val_622_);
v_fst_605_ = v___x_620_;
v_snd_606_ = v___y_600_;
goto v___jp_604_;
}
default: 
{
lean_object* v___x_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_659_ = lean_unbox(v_val_622_);
lean_dec(v_val_622_);
v___x_660_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_659_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 3);
lean_ctor_set(v___x_624_, 0, v___x_660_);
v___x_662_ = v___x_624_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_682_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_663_ = l_Lean_MessageData_ofFormat(v___x_662_);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_658_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_inc(v___x_620_);
v___x_667_ = l_Lean_MessageData_ofName(v___x_620_);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_611_, v___x_670_, v___y_600_, v___y_601_, v___y_602_);
lean_dec_ref(v___y_600_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v_snd_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v_snd_673_ = lean_ctor_get(v_a_672_, 1);
lean_inc(v_snd_673_);
lean_dec(v_a_672_);
v_fst_605_ = v___x_620_;
v_snd_606_ = v_snd_673_;
goto v___jp_604_;
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v___x_620_);
v_a_674_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_671_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_671_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_693_; 
lean_inc_ref(v_items_619_);
lean_inc(v_currKey_618_);
lean_inc(v_currArrKey_617_);
lean_inc(v_arrParents_616_);
lean_inc(v_arrKeyTys_615_);
lean_inc(v_keyTys_614_);
lean_dec(v___x_621_);
v_isSharedCheck_693_ = !lean_is_exclusive(v___y_600_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; 
v_unused_694_ = lean_ctor_get(v___y_600_, 5);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v___y_600_, 4);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v___y_600_, 3);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v___y_600_, 2);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v___y_600_, 1);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v___y_600_, 0);
lean_dec(v_unused_699_);
v___x_685_ = v___y_600_;
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
else
{
lean_dec(v___y_600_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_687_ = 4;
v___x_688_ = lean_box(v___x_687_);
lean_inc(v___x_620_);
v___x_689_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_620_, v___x_688_, v_keyTys_614_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_689_);
v___x_691_ = v___x_685_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_arrKeyTys_615_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_arrParents_616_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_currArrKey_617_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_currKey_618_);
lean_ctor_set(v_reuseFailAlloc_692_, 5, v_items_619_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_fst_605_ = v___x_620_;
v_snd_606_ = v___x_691_;
goto v___jp_604_;
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v___y_600_);
lean_dec(v_b_599_);
v_a_700_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_612_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_612_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_b_599_);
lean_ctor_set(v___x_708_, 1, v___y_600_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
v___jp_604_:
{
size_t v___x_607_; size_t v___x_608_; 
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_add(v_i_597_, v___x_607_);
v_i_597_ = v___x_608_;
v_b_599_ = v_fst_605_;
v___y_600_ = v_snd_606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_710_, lean_object* v_i_711_, lean_object* v_stop_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
size_t v_i_boxed_718_; size_t v_stop_boxed_719_; lean_object* v_res_720_; 
v_i_boxed_718_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_stop_boxed_719_ = lean_unbox_usize(v_stop_712_);
lean_dec(v_stop_712_);
v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_710_, v_i_boxed_718_, v_stop_boxed_719_, v_b_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec_ref(v_as_710_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_721_, lean_object* v_k_722_){
_start:
{
if (lean_obj_tag(v_t_721_) == 0)
{
lean_object* v_k_723_; lean_object* v_v_724_; lean_object* v_l_725_; lean_object* v_r_726_; uint8_t v___x_727_; 
v_k_723_ = lean_ctor_get(v_t_721_, 1);
v_v_724_ = lean_ctor_get(v_t_721_, 2);
v_l_725_ = lean_ctor_get(v_t_721_, 3);
v_r_726_ = lean_ctor_get(v_t_721_, 4);
v___x_727_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_722_, v_k_723_);
switch(v___x_727_)
{
case 0:
{
v_t_721_ = v_l_725_;
goto _start;
}
case 1:
{
lean_object* v___x_729_; 
lean_inc(v_v_724_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v_v_724_);
return v___x_729_;
}
default: 
{
v_t_721_ = v_r_726_;
goto _start;
}
}
}
else
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(0);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_732_, lean_object* v_k_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_732_, v_k_733_);
lean_dec(v_k_733_);
lean_dec(v_t_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_keyTys_740_; lean_object* v_arrKeyTys_741_; lean_object* v_arrParents_742_; lean_object* v_currArrKey_743_; lean_object* v_currKey_744_; lean_object* v_items_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_773_; 
v_keyTys_740_ = lean_ctor_get(v_a_736_, 0);
v_arrKeyTys_741_ = lean_ctor_get(v_a_736_, 1);
v_arrParents_742_ = lean_ctor_get(v_a_736_, 2);
v_currArrKey_743_ = lean_ctor_get(v_a_736_, 3);
v_currKey_744_ = lean_ctor_get(v_a_736_, 4);
v_items_745_ = lean_ctor_get(v_a_736_, 5);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_736_);
if (v_isSharedCheck_773_ == 0)
{
v___x_747_ = v_a_736_;
v_isShared_748_ = v_isSharedCheck_773_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_items_745_);
lean_inc(v_currKey_744_);
lean_inc(v_currArrKey_743_);
lean_inc(v_arrParents_742_);
lean_inc(v_arrKeyTys_741_);
lean_inc(v_keyTys_740_);
lean_dec(v_a_736_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_773_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_arrKeyTys_749_; lean_object* v___x_750_; lean_object* v___y_752_; lean_object* v___x_770_; 
v_arrKeyTys_749_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_743_, v_keyTys_740_, v_arrKeyTys_741_);
v___x_750_ = lean_box(0);
v___x_770_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_749_, v___x_750_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_box(1);
v___y_752_ = v___x_771_;
goto v___jp_751_;
}
else
{
lean_object* v_val_772_; 
v_val_772_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v___x_770_, 1);
v___y_752_ = v_val_772_;
goto v___jp_751_;
}
v___jp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 3, v___x_750_);
lean_ctor_set(v___x_747_, 1, v_arrKeyTys_749_);
lean_ctor_set(v___x_747_, 0, v___y_752_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___y_752_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_arrKeyTys_749_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_arrParents_742_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_currKey_744_);
lean_ctor_set(v_reuseFailAlloc_769_, 5, v_items_745_);
v___x_754_ = v_reuseFailAlloc_769_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_array_get_size(v_ks_735_);
v___x_757_ = lean_nat_dec_lt(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_750_);
lean_ctor_set(v___x_758_, 1, v___x_754_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
else
{
uint8_t v___x_760_; 
v___x_760_ = lean_nat_dec_le(v___x_756_, v___x_756_);
if (v___x_760_ == 0)
{
if (v___x_757_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_750_);
lean_ctor_set(v___x_761_, 1, v___x_754_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
else
{
size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_of_nat(v___x_756_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_735_, v___x_763_, v___x_764_, v___x_750_, v___x_754_, v_a_737_, v_a_738_);
return v___x_765_;
}
}
else
{
size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_of_nat(v___x_756_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_735_, v___x_766_, v___x_767_, v___x_750_, v___x_754_, v_a_737_, v_a_738_);
return v___x_768_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_ks_774_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_780_, lean_object* v_t_781_, lean_object* v_k_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_781_, v_k_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_784_, lean_object* v_t_785_, lean_object* v_k_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_784_, v_t_785_, v_k_786_);
lean_dec(v_k_786_);
lean_dec(v_t_785_);
return v_res_787_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0(void){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_788_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___y_803_; lean_object* v_keyTys_804_; lean_object* v_arrKeyTys_805_; lean_object* v_arrParents_806_; lean_object* v_currArrKey_807_; lean_object* v_items_808_; lean_object* v_toCold_820_; lean_object* v_currRecDepth_821_; lean_object* v_ref_822_; uint16_t v_optionFlags_823_; uint8_t v_suppressElabErrors_824_; uint8_t v_isRecordingDeps_825_; lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v_ref_828_; lean_object* v___x_829_; 
v_toCold_820_ = lean_ctor_get(v_a_799_, 0);
v_currRecDepth_821_ = lean_ctor_get(v_a_799_, 1);
v_ref_822_ = lean_ctor_get(v_a_799_, 2);
v_optionFlags_823_ = lean_ctor_get_uint16(v_a_799_, sizeof(void*)*3);
v_suppressElabErrors_824_ = lean_ctor_get_uint8(v_a_799_, sizeof(void*)*3 + 2);
v_isRecordingDeps_825_ = lean_ctor_get_uint8(v_a_799_, sizeof(void*)*3 + 3);
v___x_826_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_797_);
v___x_827_ = l_Lean_Syntax_isOfKind(v_x_797_, v___x_826_);
v_ref_828_ = l_Lean_replaceRef(v_x_797_, v_ref_822_);
lean_inc(v_currRecDepth_821_);
lean_inc_ref(v_toCold_820_);
v___x_829_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_829_, 0, v_toCold_820_);
lean_ctor_set(v___x_829_, 1, v_currRecDepth_821_);
lean_ctor_set(v___x_829_, 2, v_ref_828_);
lean_ctor_set_uint16(v___x_829_, sizeof(void*)*3, v_optionFlags_823_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*3 + 2, v_suppressElabErrors_824_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*3 + 3, v_isRecordingDeps_825_);
if (v___x_827_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4);
v___x_831_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_797_, v___x_830_, v_a_798_, v___x_829_, v_a_800_);
lean_dec_ref_known(v___x_829_, 3);
lean_dec_ref(v_a_798_);
lean_dec(v_x_797_);
return v___x_831_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___y_835_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = l_Lean_Syntax_getArg(v_x_797_, v___x_832_);
v___x_903_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_833_);
v___x_904_ = l_Lean_Syntax_isOfKind(v___x_833_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec(v_x_797_);
v___x_905_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_906_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_833_, v___x_905_, v_a_798_, v___x_829_, v_a_800_);
lean_dec_ref_known(v___x_829_, 3);
lean_dec_ref(v_a_798_);
lean_dec(v___x_833_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = l_Lean_Syntax_getArg(v___x_833_, v___x_907_);
v___x_909_ = l_Lean_Syntax_getArgs(v___x_908_);
lean_dec(v___x_908_);
v___x_910_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_911_ = lean_array_get_size(v___x_909_);
v___x_912_ = lean_nat_dec_lt(v___x_907_, v___x_911_);
if (v___x_912_ == 0)
{
lean_dec_ref(v___x_909_);
v___y_835_ = v___x_910_;
goto v___jp_834_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; lean_object* v_snd_918_; 
v___x_913_ = lean_box(v___x_912_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_910_);
v___x_915_ = ((size_t)0ULL);
v___x_916_ = lean_usize_of_nat(v___x_911_);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_904_, v___x_909_, v___x_915_, v___x_916_, v___x_914_);
lean_dec_ref(v___x_909_);
v_snd_918_ = lean_ctor_get(v___x_917_, 1);
lean_inc(v_snd_918_);
lean_dec_ref(v___x_917_);
v___y_835_ = v_snd_918_;
goto v___jp_834_;
}
}
v___jp_834_:
{
size_t v_sz_836_; size_t v___x_837_; lean_object* v___x_838_; 
v_sz_836_ = lean_array_size(v___y_835_);
v___x_837_ = ((size_t)0ULL);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_836_, v___x_837_, v___y_835_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v_x_797_);
v___x_839_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_840_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_833_, v___x_839_, v_a_798_, v___x_829_, v_a_800_);
lean_dec_ref_known(v___x_829_, 3);
lean_dec_ref(v_a_798_);
lean_dec(v___x_833_);
return v___x_840_;
}
else
{
lean_object* v_val_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_tailKey_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v___x_833_);
v_val_841_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v___x_838_, 1);
v___x_842_ = lean_box(0);
v___x_843_ = lean_array_get_size(v_val_841_);
v___x_844_ = lean_nat_sub(v___x_843_, v___x_832_);
v_tailKey_845_ = lean_array_get(v___x_842_, v_val_841_, v___x_844_);
lean_dec(v___x_844_);
v___x_846_ = lean_array_pop(v_val_841_);
v___x_847_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_846_, v_a_798_, v___x_829_, v_a_800_);
lean_dec_ref(v___x_846_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_894_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v_fst_849_ = lean_ctor_get(v_a_848_, 0);
v_snd_850_ = lean_ctor_get(v_a_848_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_a_848_);
if (v_isSharedCheck_894_ == 0)
{
v___x_852_ = v_a_848_;
v_isShared_853_ = v_isSharedCheck_894_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_inc(v_fst_849_);
lean_dec(v_a_848_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_894_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; 
lean_inc(v_tailKey_845_);
v___x_854_ = l_Lake_Toml_elabSimpleKey(v_tailKey_845_, v___x_829_, v_a_800_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v_keyTys_856_; lean_object* v_arrKeyTys_857_; lean_object* v_arrParents_858_; lean_object* v_currArrKey_859_; lean_object* v_items_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v_keyTys_856_ = lean_ctor_get(v_snd_850_, 0);
v_arrKeyTys_857_ = lean_ctor_get(v_snd_850_, 1);
v_arrParents_858_ = lean_ctor_get(v_snd_850_, 2);
v_currArrKey_859_ = lean_ctor_get(v_snd_850_, 3);
v_items_860_ = lean_ctor_get(v_snd_850_, 5);
v___x_861_ = l_Lean_Name_str___override(v_fst_849_, v_a_855_);
v___x_862_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_856_, v___x_861_);
if (lean_obj_tag(v___x_862_) == 1)
{
lean_object* v_val_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_885_; 
v_val_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_885_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_885_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_val_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_885_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v___x_867_; 
v___x_867_ = lean_unbox(v_val_863_);
if (v___x_867_ == 4)
{
lean_inc_ref(v_items_860_);
lean_inc(v_currArrKey_859_);
lean_inc(v_arrParents_858_);
lean_inc(v_arrKeyTys_857_);
lean_inc(v_keyTys_856_);
lean_del_object(v___x_865_);
lean_dec(v_val_863_);
lean_del_object(v___x_852_);
lean_dec(v_snd_850_);
lean_dec(v_tailKey_845_);
lean_dec_ref_known(v___x_829_, 3);
v___y_803_ = v___x_861_;
v_keyTys_804_ = v_keyTys_856_;
v_arrKeyTys_805_ = v_arrKeyTys_857_;
v_arrParents_806_ = v_arrParents_858_;
v_currArrKey_807_ = v_currArrKey_859_;
v_items_808_ = v_items_860_;
goto v___jp_802_;
}
else
{
lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
lean_dec(v_x_797_);
v___x_868_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_869_ = lean_unbox(v_val_863_);
lean_dec(v_val_863_);
v___x_870_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_869_);
if (v_isShared_866_ == 0)
{
lean_ctor_set_tag(v___x_865_, 3);
lean_ctor_set(v___x_865_, 0, v___x_870_);
v___x_872_ = v___x_865_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_884_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = l_Lean_MessageData_ofFormat(v___x_872_);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 7);
lean_ctor_set(v___x_852_, 1, v___x_873_);
lean_ctor_set(v___x_852_, 0, v___x_868_);
v___x_875_ = v___x_852_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_883_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_876_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Lean_MessageData_ofName(v___x_861_);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_845_, v___x_881_, v_snd_850_, v___x_829_, v_a_800_);
lean_dec_ref_known(v___x_829_, 3);
lean_dec(v_snd_850_);
lean_dec(v_tailKey_845_);
return v___x_882_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_860_);
lean_inc(v_currArrKey_859_);
lean_inc(v_arrParents_858_);
lean_inc(v_arrKeyTys_857_);
lean_inc(v_keyTys_856_);
lean_dec(v___x_862_);
lean_del_object(v___x_852_);
lean_dec(v_snd_850_);
lean_dec(v_tailKey_845_);
lean_dec_ref_known(v___x_829_, 3);
v___y_803_ = v___x_861_;
v_keyTys_804_ = v_keyTys_856_;
v_arrKeyTys_805_ = v_arrKeyTys_857_;
v_arrParents_806_ = v_arrParents_858_;
v_currArrKey_807_ = v_currArrKey_859_;
v_items_808_ = v_items_860_;
goto v___jp_802_;
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_del_object(v___x_852_);
lean_dec(v_snd_850_);
lean_dec(v_fst_849_);
lean_dec(v_tailKey_845_);
lean_dec_ref_known(v___x_829_, 3);
lean_dec(v_x_797_);
v_a_886_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_854_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_854_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_tailKey_845_);
lean_dec_ref_known(v___x_829_, 3);
lean_dec(v_x_797_);
v_a_895_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_847_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_847_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
v___jp_802_:
{
lean_object* v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_809_ = lean_box(0);
v___x_810_ = 1;
v___x_811_ = lean_box(v___x_810_);
lean_inc_n(v___y_803_, 2);
v___x_812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_803_, v___x_811_, v_keyTys_804_);
v___x_813_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_x_797_);
v___x_814_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_814_, 0, v_x_797_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_815_, 0, v_x_797_);
lean_ctor_set(v___x_815_, 1, v___y_803_);
lean_ctor_set(v___x_815_, 2, v___x_814_);
v___x_816_ = lean_array_push(v_items_808_, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_817_, 0, v___x_812_);
lean_ctor_set(v___x_817_, 1, v_arrKeyTys_805_);
lean_ctor_set(v___x_817_, 2, v_arrParents_806_);
lean_ctor_set(v___x_817_, 3, v_currArrKey_807_);
lean_ctor_set(v___x_817_, 4, v___y_803_);
lean_ctor_set(v___x_817_, 5, v___x_816_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_809_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_924_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_toCold_938_; lean_object* v_currRecDepth_939_; lean_object* v_ref_940_; uint16_t v_optionFlags_941_; uint8_t v_suppressElabErrors_942_; uint8_t v_isRecordingDeps_943_; lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v_ref_946_; lean_object* v___x_947_; lean_object* v___y_949_; 
v_toCold_938_ = lean_ctor_get(v_a_935_, 0);
v_currRecDepth_939_ = lean_ctor_get(v_a_935_, 1);
v_ref_940_ = lean_ctor_get(v_a_935_, 2);
v_optionFlags_941_ = lean_ctor_get_uint16(v_a_935_, sizeof(void*)*3);
v_suppressElabErrors_942_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*3 + 2);
v_isRecordingDeps_943_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*3 + 3);
v___x_944_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_933_);
v___x_945_ = l_Lean_Syntax_isOfKind(v_x_933_, v___x_944_);
v_ref_946_ = l_Lean_replaceRef(v_x_933_, v_ref_940_);
lean_inc(v_currRecDepth_939_);
lean_inc_ref(v_toCold_938_);
v___x_947_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_947_, 0, v_toCold_938_);
lean_ctor_set(v___x_947_, 1, v_currRecDepth_939_);
lean_ctor_set(v___x_947_, 2, v_ref_946_);
lean_ctor_set_uint16(v___x_947_, sizeof(void*)*3, v_optionFlags_941_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*3 + 2, v_suppressElabErrors_942_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*3 + 3, v_isRecordingDeps_943_);
if (v___x_945_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_957_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_933_, v___x_956_, v_a_934_, v___x_947_, v_a_936_);
lean_dec_ref_known(v___x_947_, 3);
lean_dec_ref(v_a_934_);
lean_dec(v_x_933_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___y_963_; 
v___x_958_ = lean_unsigned_to_nat(2u);
v___x_959_ = l_Lean_Syntax_getArg(v_x_933_, v___x_958_);
v___x_960_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_959_);
v___x_961_ = l_Lean_Syntax_isOfKind(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v___x_959_);
v___x_1097_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1098_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_933_, v___x_1097_, v_a_934_, v___x_947_, v_a_936_);
lean_dec_ref_known(v___x_947_, 3);
lean_dec_ref(v_a_934_);
lean_dec(v_x_933_);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = l_Lean_Syntax_getArg(v___x_959_, v___x_1099_);
lean_dec(v___x_959_);
v___x_1101_ = l_Lean_Syntax_getArgs(v___x_1100_);
lean_dec(v___x_1100_);
v___x_1102_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1103_ = lean_array_get_size(v___x_1101_);
v___x_1104_ = lean_nat_dec_lt(v___x_1099_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec_ref(v___x_1101_);
v___y_963_ = v___x_1102_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; lean_object* v___x_1109_; lean_object* v_snd_1110_; 
v___x_1105_ = lean_box(v___x_1104_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1102_);
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = lean_usize_of_nat(v___x_1103_);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_961_, v___x_1101_, v___x_1107_, v___x_1108_, v___x_1106_);
lean_dec_ref(v___x_1101_);
v_snd_1110_ = lean_ctor_get(v___x_1109_, 1);
lean_inc(v_snd_1110_);
lean_dec_ref(v___x_1109_);
v___y_963_ = v_snd_1110_;
goto v___jp_962_;
}
}
v___jp_962_:
{
size_t v_sz_964_; size_t v___x_965_; lean_object* v___x_966_; 
v_sz_964_ = lean_array_size(v___y_963_);
v___x_965_ = ((size_t)0ULL);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_964_, v___x_965_, v___y_963_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_968_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_933_, v___x_967_, v_a_934_, v___x_947_, v_a_936_);
lean_dec_ref_known(v___x_947_, 3);
lean_dec_ref(v_a_934_);
lean_dec(v_x_933_);
return v___x_968_;
}
else
{
lean_object* v_val_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_tailKey_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_val_969_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_val_969_);
lean_dec_ref_known(v___x_966_, 1);
v___x_970_ = lean_box(0);
v___x_971_ = lean_array_get_size(v_val_969_);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_sub(v___x_971_, v___x_972_);
v_tailKey_974_ = lean_array_get(v___x_970_, v_val_969_, v___x_973_);
lean_dec(v___x_973_);
v___x_975_ = lean_array_pop(v_val_969_);
v___x_976_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_975_, v_a_934_, v___x_947_, v_a_936_);
lean_dec_ref(v___x_975_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v_fst_978_; lean_object* v_snd_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1088_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v_fst_978_ = lean_ctor_get(v_a_977_, 0);
v_snd_979_ = lean_ctor_get(v_a_977_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_a_977_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_981_ = v_a_977_;
v_isShared_982_ = v_isSharedCheck_1088_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_snd_979_);
lean_inc(v_fst_978_);
lean_dec(v_a_977_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1088_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; 
lean_inc(v_tailKey_974_);
v___x_983_ = l_Lake_Toml_elabSimpleKey(v_tailKey_974_, v___x_947_, v_a_936_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1079_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_1079_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1079_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_keyTys_988_; lean_object* v_arrKeyTys_989_; lean_object* v_arrParents_990_; lean_object* v_currArrKey_991_; lean_object* v_items_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_keyTys_988_ = lean_ctor_get(v_snd_979_, 0);
v_arrKeyTys_989_ = lean_ctor_get(v_snd_979_, 1);
v_arrParents_990_ = lean_ctor_get(v_snd_979_, 2);
v_currArrKey_991_ = lean_ctor_get(v_snd_979_, 3);
v_items_992_ = lean_ctor_get(v_snd_979_, 5);
v___x_993_ = l_Lean_Name_str___override(v_fst_978_, v_a_984_);
v___x_994_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_988_, v___x_993_);
if (lean_obj_tag(v___x_994_) == 1)
{
lean_object* v_val_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1046_; 
v_val_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1046_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_val_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1046_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
uint8_t v___x_999_; 
v___x_999_ = lean_unbox(v_val_995_);
if (v___x_999_ == 2)
{
lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1024_; 
lean_inc_ref(v_items_992_);
lean_inc(v_arrParents_990_);
lean_inc(v_arrKeyTys_989_);
lean_del_object(v___x_997_);
lean_dec(v_val_995_);
lean_dec(v_tailKey_974_);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_snd_979_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; lean_object* v_unused_1026_; lean_object* v_unused_1027_; lean_object* v_unused_1028_; lean_object* v_unused_1029_; lean_object* v_unused_1030_; 
v_unused_1025_ = lean_ctor_get(v_snd_979_, 5);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_snd_979_, 4);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_snd_979_, 3);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_snd_979_, 2);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_snd_979_, 1);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_snd_979_, 0);
lean_dec(v_unused_1030_);
v___x_1001_ = v_snd_979_;
v_isShared_1002_ = v_isSharedCheck_1024_;
goto v_resetjp_1000_;
}
else
{
lean_dec(v_snd_979_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1024_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_990_, v___x_993_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_del_object(v___x_1001_);
lean_dec_ref(v_items_992_);
lean_dec(v_arrParents_990_);
lean_dec(v_arrKeyTys_989_);
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_dec(v_x_933_);
v___y_949_ = v___x_993_;
goto v___jp_948_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1005_; 
v_val_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_989_, v_val_1004_);
lean_dec(v_val_1004_);
if (lean_obj_tag(v___x_1005_) == 1)
{
lean_object* v_val_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec_ref_known(v___x_947_, 3);
v_val_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_933_, 2);
v___x_1009_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_x_933_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_mk_empty_array_with_capacity(v___x_972_);
v___x_1011_ = lean_array_push(v___x_1010_, v___x_1009_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_x_933_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
lean_inc_n(v___x_993_, 2);
v___x_1013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1013_, 0, v_x_933_);
lean_ctor_set(v___x_1013_, 1, v___x_993_);
lean_ctor_set(v___x_1013_, 2, v___x_1012_);
v___x_1014_ = lean_array_push(v_items_992_, v___x_1013_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 5, v___x_1014_);
lean_ctor_set(v___x_1001_, 4, v___x_993_);
lean_ctor_set(v___x_1001_, 3, v___x_993_);
lean_ctor_set(v___x_1001_, 0, v_val_1006_);
v___x_1016_ = v___x_1001_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_val_1006_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_arrKeyTys_989_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_arrParents_990_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1023_, 5, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v___x_1016_);
lean_ctor_set(v___x_981_, 0, v___x_1007_);
v___x_1018_ = v___x_981_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1020_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_1018_);
v___x_1020_ = v___x_986_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_dec(v___x_1005_);
lean_del_object(v___x_1001_);
lean_dec_ref(v_items_992_);
lean_dec(v_arrParents_990_);
lean_dec(v_arrKeyTys_989_);
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_dec(v_x_933_);
v___y_949_ = v___x_993_;
goto v___jp_948_;
}
}
}
}
else
{
lean_object* v___x_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_dec(v_x_933_);
v___x_1031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1032_ = lean_unbox(v_val_995_);
lean_dec(v_val_995_);
v___x_1033_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1032_);
v___x_1034_ = lean_string_append(v___x_1031_, v___x_1033_);
lean_dec_ref(v___x_1033_);
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1036_ = lean_string_append(v___x_1034_, v___x_1035_);
v___x_1037_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_993_, v___x_961_);
v___x_1038_ = lean_string_append(v___x_1036_, v___x_1037_);
lean_dec_ref(v___x_1037_);
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1040_ = lean_string_append(v___x_1038_, v___x_1039_);
if (v_isShared_998_ == 0)
{
lean_ctor_set_tag(v___x_997_, 3);
lean_ctor_set(v___x_997_, 0, v___x_1040_);
v___x_1042_ = v___x_997_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = l_Lean_MessageData_ofFormat(v___x_1042_);
v___x_1044_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_974_, v___x_1043_, v_snd_979_, v___x_947_, v_a_936_);
lean_dec_ref_known(v___x_947_, 3);
lean_dec(v_snd_979_);
lean_dec(v_tailKey_974_);
return v___x_1044_;
}
}
}
}
else
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1072_; 
lean_inc_ref(v_items_992_);
lean_inc(v_currArrKey_991_);
lean_inc(v_arrParents_990_);
lean_inc(v_arrKeyTys_989_);
lean_inc(v_keyTys_988_);
lean_dec(v___x_994_);
lean_dec(v_tailKey_974_);
lean_dec_ref_known(v___x_947_, 3);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_snd_979_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; 
v_unused_1073_ = lean_ctor_get(v_snd_979_, 5);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_snd_979_, 4);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_snd_979_, 3);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_snd_979_, 2);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_snd_979_, 1);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_snd_979_, 0);
lean_dec(v_unused_1078_);
v___x_1048_ = v_snd_979_;
v_isShared_1049_ = v_isSharedCheck_1072_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v_snd_979_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1072_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = 2;
v___x_1052_ = lean_box(v___x_1051_);
lean_inc_n(v___x_993_, 4);
v___x_1053_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_993_, v___x_1052_, v_keyTys_988_);
lean_inc(v___x_1053_);
lean_inc(v_currArrKey_991_);
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_991_, v___x_1053_, v_arrKeyTys_989_);
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_993_, v_currArrKey_991_, v_arrParents_990_);
v___x_1056_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_933_, 2);
v___x_1057_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_x_933_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_mk_empty_array_with_capacity(v___x_972_);
v___x_1059_ = lean_array_push(v___x_1058_, v___x_1057_);
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_x_933_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1061_, 0, v_x_933_);
lean_ctor_set(v___x_1061_, 1, v___x_993_);
lean_ctor_set(v___x_1061_, 2, v___x_1060_);
v___x_1062_ = lean_array_push(v_items_992_, v___x_1061_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 5, v___x_1062_);
lean_ctor_set(v___x_1048_, 4, v___x_993_);
lean_ctor_set(v___x_1048_, 3, v___x_993_);
lean_ctor_set(v___x_1048_, 2, v___x_1055_);
lean_ctor_set(v___x_1048_, 1, v___x_1054_);
lean_ctor_set(v___x_1048_, 0, v___x_1053_);
v___x_1064_ = v___x_1048_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1071_, 5, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v___x_1064_);
lean_ctor_set(v___x_981_, 0, v___x_1050_);
v___x_1066_ = v___x_981_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_1066_);
v___x_1068_ = v___x_986_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_del_object(v___x_981_);
lean_dec(v_snd_979_);
lean_dec(v_fst_978_);
lean_dec(v_tailKey_974_);
lean_dec_ref_known(v___x_947_, 3);
lean_dec(v_x_933_);
v_a_1080_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_983_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_983_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_tailKey_974_);
lean_dec_ref_known(v___x_947_, 3);
lean_dec(v_x_933_);
v_a_1089_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_976_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_976_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
v___jp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_950_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_951_ = l_Lean_MessageData_ofName(v___y_949_);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_954_, v___x_947_, v_a_936_);
lean_dec_ref_known(v___x_947_, 3);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1116_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1119_ = l_Lean_stringToMessageData(v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1120_);
v___x_1126_ = l_Lean_Syntax_isOfKind(v_x_1120_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_1120_);
v___x_1128_ = l_Lean_Syntax_isOfKind(v_x_1120_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1120_);
v___x_1130_ = l_Lean_Syntax_isOfKind(v_x_1120_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1132_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1120_, v___x_1131_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec_ref(v_a_1121_);
lean_dec(v_x_1120_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
return v___x_1133_;
}
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
return v___x_1134_;
}
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1143_, lean_object* v_as_1144_, size_t v_i_1145_, size_t v_stop_1146_, lean_object* v_b_1147_){
_start:
{
lean_object* v___y_1149_; uint8_t v___x_1153_; 
v___x_1153_ = lean_usize_dec_eq(v_i_1145_, v_stop_1146_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v_fst_1155_; lean_object* v_snd_1156_; lean_object* v___x_1157_; 
v___x_1154_ = lean_array_uget_borrowed(v_as_1144_, v_i_1145_);
v_fst_1155_ = lean_ctor_get(v___x_1154_, 0);
v_snd_1156_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_fst_1155_);
v___x_1157_ = l_Lean_Name_components(v_fst_1155_);
if (lean_obj_tag(v___x_1157_) == 0)
{
v___y_1149_ = v_b_1147_;
goto v___jp_1148_;
}
else
{
lean_object* v_head_1158_; lean_object* v_tail_1159_; lean_object* v___x_1160_; 
v_head_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_head_1158_);
v_tail_1159_ = lean_ctor_get(v___x_1157_, 1);
lean_inc(v_tail_1159_);
lean_dec_ref_known(v___x_1157_, 2);
lean_inc(v_snd_1156_);
lean_inc(v_ref_1143_);
v___x_1160_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1147_, v_ref_1143_, v_head_1158_, v_tail_1159_, v_snd_1156_);
v___y_1149_ = v___x_1160_;
goto v___jp_1148_;
}
}
else
{
lean_dec(v_ref_1143_);
return v_b_1147_;
}
v___jp_1148_:
{
size_t v___x_1150_; size_t v___x_1151_; 
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_add(v_i_1145_, v___x_1150_);
v_i_1145_ = v___x_1151_;
v_b_1147_ = v___y_1149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1161_, size_t v_i_1162_, lean_object* v_bs_1163_){
_start:
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_usize_dec_lt(v_i_1162_, v_sz_1161_);
if (v___x_1164_ == 0)
{
return v_bs_1163_;
}
else
{
lean_object* v_v_1165_; lean_object* v___x_1166_; lean_object* v_bs_x27_1167_; lean_object* v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; lean_object* v___x_1171_; 
v_v_1165_ = lean_array_uget(v_bs_1163_, v_i_1162_);
v___x_1166_ = lean_unsigned_to_nat(0u);
v_bs_x27_1167_ = lean_array_uset(v_bs_1163_, v_i_1162_, v___x_1166_);
v___x_1168_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1165_);
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_add(v_i_1162_, v___x_1169_);
v___x_1171_ = lean_array_uset(v_bs_x27_1167_, v_i_1162_, v___x_1168_);
v_i_1162_ = v___x_1170_;
v_bs_1163_ = v___x_1171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1173_){
_start:
{
switch(lean_obj_tag(v_a_1173_))
{
case 6:
{
lean_object* v_xs_1174_; lean_object* v_ref_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1203_; 
v_xs_1174_ = lean_ctor_get(v_a_1173_, 1);
v_ref_1175_ = lean_ctor_get(v_a_1173_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_a_1173_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1177_ = v_a_1173_;
v_isShared_1178_ = v_isSharedCheck_1203_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_xs_1174_);
lean_inc(v_ref_1175_);
lean_dec(v_a_1173_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1203_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_items_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v_items_1179_ = lean_ctor_get(v_xs_1174_, 0);
lean_inc_ref(v_items_1179_);
lean_dec_ref(v_xs_1174_);
v___x_1180_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_array_get_size(v_items_1179_);
v___x_1183_ = lean_nat_dec_lt(v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1185_; 
lean_dec_ref(v_items_1179_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1180_);
v___x_1185_ = v___x_1177_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_ref_1175_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_nat_dec_le(v___x_1182_, v___x_1182_);
if (v___x_1187_ == 0)
{
if (v___x_1183_ == 0)
{
lean_object* v___x_1189_; 
lean_dec_ref(v_items_1179_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1180_);
v___x_1189_ = v___x_1177_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_ref_1175_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1180_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
else
{
size_t v___x_1191_; size_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = lean_usize_of_nat(v___x_1182_);
lean_inc(v_ref_1175_);
v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1175_, v_items_1179_, v___x_1191_, v___x_1192_, v___x_1180_);
lean_dec_ref(v_items_1179_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1193_);
v___x_1195_ = v___x_1177_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_ref_1175_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
size_t v___x_1197_; size_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1197_ = ((size_t)0ULL);
v___x_1198_ = lean_usize_of_nat(v___x_1182_);
lean_inc(v_ref_1175_);
v___x_1199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1175_, v_items_1179_, v___x_1197_, v___x_1198_, v___x_1180_);
lean_dec_ref(v_items_1179_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1199_);
v___x_1201_ = v___x_1177_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_ref_1175_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
case 5:
{
lean_object* v_ref_1204_; lean_object* v_xs_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1215_; 
v_ref_1204_ = lean_ctor_get(v_a_1173_, 0);
v_xs_1205_ = lean_ctor_get(v_a_1173_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_a_1173_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1207_ = v_a_1173_;
v_isShared_1208_ = v_isSharedCheck_1215_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_xs_1205_);
lean_inc(v_ref_1204_);
lean_dec(v_a_1173_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1215_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
size_t v_sz_1209_; size_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v_sz_1209_ = lean_array_size(v_xs_1205_);
v___x_1210_ = ((size_t)0ULL);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1209_, v___x_1210_, v_xs_1205_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1211_);
v___x_1213_ = v___x_1207_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_ref_1204_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
default: 
{
return v_a_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1216_, lean_object* v___x_1217_, lean_object* v_v_x3f_1218_){
_start:
{
if (lean_obj_tag(v_v_x3f_1218_) == 1)
{
lean_object* v_val_1219_; 
v_val_1219_ = lean_ctor_get(v_v_x3f_1218_, 0);
lean_inc(v_val_1219_);
lean_dec_ref_known(v_v_x3f_1218_, 1);
switch(lean_obj_tag(v_val_1219_))
{
case 6:
{
lean_object* v_ref_1220_; lean_object* v_xs_1221_; lean_object* v___x_1222_; 
v_ref_1220_ = lean_ctor_get(v_val_1219_, 0);
lean_inc(v_ref_1220_);
v_xs_1221_ = lean_ctor_get(v_val_1219_, 1);
lean_inc_ref(v_xs_1221_);
lean_dec_ref_known(v_val_1219_, 2);
v___x_1222_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1216_);
if (lean_obj_tag(v___x_1222_) == 6)
{
lean_object* v_xs_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1232_; 
v_xs_1223_ = lean_ctor_get(v___x_1222_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v___x_1222_, 0);
lean_dec(v_unused_1233_);
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1232_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_xs_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1232_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_items_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v_items_1227_ = lean_ctor_get(v_xs_1223_, 0);
lean_inc_ref(v_items_1227_);
lean_dec_ref(v_xs_1223_);
v___x_1228_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1217_, v_xs_1221_, v_items_1227_);
lean_dec_ref(v_items_1227_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 1, v___x_1228_);
lean_ctor_set(v___x_1225_, 0, v_ref_1220_);
v___x_1230_ = v___x_1225_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_ref_1220_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
else
{
lean_dec_ref(v_xs_1221_);
lean_dec(v_ref_1220_);
lean_dec_ref(v___x_1217_);
return v___x_1222_;
}
}
case 5:
{
lean_object* v_ref_1234_; lean_object* v_xs_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v___x_1217_);
v_ref_1234_ = lean_ctor_get(v_val_1219_, 0);
v_xs_1235_ = lean_ctor_get(v_val_1219_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_val_1219_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1237_ = v_val_1219_;
v_isShared_1238_ = v_isSharedCheck_1254_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_xs_1235_);
lean_inc(v_ref_1234_);
lean_dec(v_val_1219_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1254_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1216_);
if (lean_obj_tag(v___x_1239_) == 5)
{
lean_object* v_xs_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1248_; 
lean_del_object(v___x_1237_);
v_xs_1240_ = lean_ctor_get(v___x_1239_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1239_, 0);
lean_dec(v_unused_1249_);
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_xs_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = l_Array_append___redArg(v_xs_1235_, v_xs_1240_);
lean_dec_ref(v_xs_1240_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1244_);
lean_ctor_set(v___x_1242_, 0, v_ref_1234_);
v___x_1246_ = v___x_1242_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_ref_1234_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_array_push(v_xs_1235_, v___x_1239_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v___x_1250_);
v___x_1252_ = v___x_1237_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_ref_1234_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
default: 
{
lean_object* v___x_1255_; 
lean_dec(v_val_1219_);
lean_dec_ref(v___x_1217_);
v___x_1255_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1216_);
return v___x_1255_;
}
}
}
else
{
lean_object* v___x_1256_; 
lean_dec(v_v_x3f_1218_);
lean_dec_ref(v___x_1217_);
v___x_1256_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1216_);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1257_, lean_object* v_k_1258_, lean_object* v_t_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1259_);
lean_inc(v_k_1258_);
v___x_1261_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1260_, v_k_1258_, v_t_1259_);
if (lean_obj_tag(v___x_1261_) == 1)
{
lean_object* v_val_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_k_1258_);
v_val_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1297_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_val_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1297_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v_items_1266_; lean_object* v_indices_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1296_; 
v_items_1266_ = lean_ctor_get(v_t_1259_, 0);
v_indices_1267_ = lean_ctor_get(v_t_1259_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_t_1259_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1269_ = v_t_1259_;
v_isShared_1270_ = v_isSharedCheck_1296_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_indices_1267_);
lean_inc(v_items_1266_);
lean_dec(v_t_1259_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1296_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = lean_array_get_size(v_items_1266_);
v___x_1272_ = lean_nat_dec_lt(v_val_1262_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1274_; 
lean_del_object(v___x_1264_);
lean_dec(v_val_1262_);
lean_dec_ref(v_newV_1257_);
if (v_isShared_1270_ == 0)
{
v___x_1274_ = v___x_1269_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_items_1266_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_indices_1267_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
else
{
lean_object* v_v_1276_; lean_object* v_fst_1277_; lean_object* v_snd_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1295_; 
v_v_1276_ = lean_array_fget(v_items_1266_, v_val_1262_);
v_fst_1277_ = lean_ctor_get(v_v_1276_, 0);
v_snd_1278_ = lean_ctor_get(v_v_1276_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_v_1276_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1280_ = v_v_1276_;
v_isShared_1281_ = v_isSharedCheck_1295_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_snd_1278_);
lean_inc(v_fst_1277_);
lean_dec(v_v_1276_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1295_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v_xs_x27_1283_; lean_object* v___x_1285_; 
v___x_1282_ = lean_box(0);
v_xs_x27_1283_ = lean_array_fset(v_items_1266_, v_val_1262_, v___x_1282_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_snd_1278_);
v___x_1285_ = v___x_1264_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_snd_1278_);
v___x_1285_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1257_, v___x_1260_, v___x_1285_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1286_);
v___x_1288_ = v___x_1280_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_fst_1277_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = lean_array_fset(v_xs_x27_1283_, v_val_1262_, v___x_1288_);
lean_dec(v_val_1262_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1289_);
v___x_1291_ = v___x_1269_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_indices_1267_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v___x_1261_);
v___x_1298_ = lean_box(0);
v___x_1299_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1257_, v___x_1260_, v___x_1298_);
v___x_1300_ = l_Lake_Toml_RBDict_push___redArg(v___x_1260_, v_k_1258_, v___x_1299_, v_t_1259_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1301_, lean_object* v_head_1302_, lean_object* v_tail_1303_, lean_object* v_newV_1304_, lean_object* v_v_x3f_1305_){
_start:
{
if (lean_obj_tag(v_v_x3f_1305_) == 1)
{
lean_object* v_val_1306_; 
v_val_1306_ = lean_ctor_get(v_v_x3f_1305_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v_v_x3f_1305_, 1);
switch(lean_obj_tag(v_val_1306_))
{
case 5:
{
lean_object* v_ref_1307_; lean_object* v_xs_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_ref_1307_ = lean_ctor_get(v_val_1306_, 0);
v_xs_1308_ = lean_ctor_get(v_val_1306_, 1);
v___x_1309_ = lean_array_get_size(v_xs_1308_);
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_nat_sub(v___x_1309_, v___x_1310_);
v___x_1312_ = lean_nat_dec_lt(v___x_1311_, v___x_1309_);
if (v___x_1312_ == 0)
{
lean_dec(v___x_1311_);
lean_dec_ref(v_newV_1304_);
lean_dec(v_tail_1303_);
lean_dec(v_head_1302_);
lean_dec(v_kRef_1301_);
return v_val_1306_;
}
else
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1337_; 
lean_inc_ref(v_xs_1308_);
lean_inc(v_ref_1307_);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_val_1306_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; lean_object* v_unused_1339_; 
v_unused_1338_ = lean_ctor_get(v_val_1306_, 1);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_val_1306_, 0);
lean_dec(v_unused_1339_);
v___x_1314_ = v_val_1306_;
v_isShared_1315_ = v_isSharedCheck_1337_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v_val_1306_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1337_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_v_1316_; lean_object* v___x_1317_; lean_object* v_xs_x27_1318_; lean_object* v___y_1320_; 
v_v_1316_ = lean_array_fget(v_xs_1308_, v___x_1311_);
v___x_1317_ = lean_box(0);
v_xs_x27_1318_ = lean_array_fset(v_xs_1308_, v___x_1311_, v___x_1317_);
if (lean_obj_tag(v_v_1316_) == 6)
{
lean_object* v_ref_1325_; lean_object* v_xs_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1334_; 
v_ref_1325_ = lean_ctor_get(v_v_1316_, 0);
v_xs_1326_ = lean_ctor_get(v_v_1316_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_v_1316_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1328_ = v_v_1316_;
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_xs_1326_);
lean_inc(v_ref_1325_);
lean_dec(v_v_1316_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1326_, v_kRef_1301_, v_head_1302_, v_tail_1303_, v_newV_1304_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v___x_1330_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_ref_1325_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
v___y_1320_ = v___x_1332_;
goto v___jp_1319_;
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v_v_1316_);
lean_dec_ref(v_newV_1304_);
lean_dec(v_tail_1303_);
lean_dec(v_head_1302_);
v___x_1335_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1336_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_kRef_1301_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___y_1320_ = v___x_1336_;
goto v___jp_1319_;
}
v___jp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_array_fset(v_xs_x27_1318_, v___x_1311_, v___y_1320_);
lean_dec(v___x_1311_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 1, v___x_1321_);
v___x_1323_ = v___x_1314_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_ref_1307_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1340_; lean_object* v_xs_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1349_; 
v_ref_1340_ = lean_ctor_get(v_val_1306_, 0);
v_xs_1341_ = lean_ctor_get(v_val_1306_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_val_1306_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1343_ = v_val_1306_;
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_xs_1341_);
lean_inc(v_ref_1340_);
lean_dec(v_val_1306_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1345_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1341_, v_kRef_1301_, v_head_1302_, v_tail_1303_, v_newV_1304_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v___x_1345_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_ref_1340_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
default: 
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_dec(v_val_1306_);
v___x_1350_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1301_);
v___x_1351_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1350_, v_kRef_1301_, v_head_1302_, v_tail_1303_, v_newV_1304_);
v___x_1352_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_kRef_1301_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
return v___x_1352_;
}
}
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_v_x3f_1305_);
v___x_1353_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1301_);
v___x_1354_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1353_, v_kRef_1301_, v_head_1302_, v_tail_1303_, v_newV_1304_);
v___x_1355_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_kRef_1301_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1356_, lean_object* v_head_1357_, lean_object* v_tail_1358_, lean_object* v_newV_1359_, lean_object* v_k_1360_, lean_object* v_t_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1361_);
lean_inc(v_k_1360_);
v___x_1363_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1362_, v_k_1360_, v_t_1361_);
if (lean_obj_tag(v___x_1363_) == 1)
{
lean_object* v_val_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v_k_1360_);
v_val_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1399_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_val_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1399_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_items_1368_; lean_object* v_indices_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1398_; 
v_items_1368_ = lean_ctor_get(v_t_1361_, 0);
v_indices_1369_ = lean_ctor_get(v_t_1361_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_t_1361_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1371_ = v_t_1361_;
v_isShared_1372_ = v_isSharedCheck_1398_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_indices_1369_);
lean_inc(v_items_1368_);
lean_dec(v_t_1361_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1398_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_array_get_size(v_items_1368_);
v___x_1374_ = lean_nat_dec_lt(v_val_1364_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1376_; 
lean_del_object(v___x_1366_);
lean_dec(v_val_1364_);
lean_dec_ref(v_newV_1359_);
lean_dec(v_tail_1358_);
lean_dec(v_head_1357_);
lean_dec(v_kRef_1356_);
if (v_isShared_1372_ == 0)
{
v___x_1376_ = v___x_1371_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_items_1368_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_indices_1369_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
else
{
lean_object* v_v_1378_; lean_object* v_fst_1379_; lean_object* v_snd_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1397_; 
v_v_1378_ = lean_array_fget(v_items_1368_, v_val_1364_);
v_fst_1379_ = lean_ctor_get(v_v_1378_, 0);
v_snd_1380_ = lean_ctor_get(v_v_1378_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_v_1378_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1382_ = v_v_1378_;
v_isShared_1383_ = v_isSharedCheck_1397_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_snd_1380_);
lean_inc(v_fst_1379_);
lean_dec(v_v_1378_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1397_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v_xs_x27_1385_; lean_object* v___x_1387_; 
v___x_1384_ = lean_box(0);
v_xs_x27_1385_ = lean_array_fset(v_items_1368_, v_val_1364_, v___x_1384_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v_snd_1380_);
v___x_1387_ = v___x_1366_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_snd_1380_);
v___x_1387_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1356_, v_head_1357_, v_tail_1358_, v_newV_1359_, v___x_1387_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v___x_1388_);
v___x_1390_ = v___x_1382_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_fst_1379_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_array_fset(v_xs_x27_1385_, v_val_1364_, v___x_1390_);
lean_dec(v_val_1364_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1391_);
v___x_1393_ = v___x_1371_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_indices_1369_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec(v___x_1363_);
v___x_1400_ = lean_box(0);
v___x_1401_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1356_, v_head_1357_, v_tail_1358_, v_newV_1359_, v___x_1400_);
v___x_1402_ = l_Lake_Toml_RBDict_push___redArg(v___x_1362_, v_k_1360_, v___x_1401_, v_t_1361_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1403_, lean_object* v_kRef_1404_, lean_object* v_k_1405_, lean_object* v_ks_1406_, lean_object* v_newV_1407_){
_start:
{
if (lean_obj_tag(v_ks_1406_) == 0)
{
lean_object* v___x_1408_; 
lean_dec(v_kRef_1404_);
v___x_1408_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1407_, v_k_1405_, v_t_1403_);
return v___x_1408_;
}
else
{
lean_object* v_head_1409_; lean_object* v_tail_1410_; lean_object* v___x_1411_; 
v_head_1409_ = lean_ctor_get(v_ks_1406_, 0);
lean_inc(v_head_1409_);
v_tail_1410_ = lean_ctor_get(v_ks_1406_, 1);
lean_inc(v_tail_1410_);
lean_dec_ref_known(v_ks_1406_, 2);
v___x_1411_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1404_, v_head_1409_, v_tail_1410_, v_newV_1407_, v_k_1405_, v_t_1403_);
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1412_, lean_object* v_i_1413_, lean_object* v_bs_1414_){
_start:
{
size_t v_sz_boxed_1415_; size_t v_i_boxed_1416_; lean_object* v_res_1417_; 
v_sz_boxed_1415_ = lean_unbox_usize(v_sz_1412_);
lean_dec(v_sz_1412_);
v_i_boxed_1416_ = lean_unbox_usize(v_i_1413_);
lean_dec(v_i_1413_);
v_res_1417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1415_, v_i_boxed_1416_, v_bs_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1418_, lean_object* v_as_1419_, lean_object* v_i_1420_, lean_object* v_stop_1421_, lean_object* v_b_1422_){
_start:
{
size_t v_i_boxed_1423_; size_t v_stop_boxed_1424_; lean_object* v_res_1425_; 
v_i_boxed_1423_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_stop_boxed_1424_ = lean_unbox_usize(v_stop_1421_);
lean_dec(v_stop_1421_);
v_res_1425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1418_, v_as_1419_, v_i_boxed_1423_, v_stop_boxed_1424_, v_b_1422_);
lean_dec_ref(v_as_1419_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1426_, size_t v_i_1427_, size_t v_stop_1428_, lean_object* v_b_1429_){
_start:
{
lean_object* v___y_1431_; uint8_t v___x_1435_; 
v___x_1435_ = lean_usize_dec_eq(v_i_1427_, v_stop_1428_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v_ref_1437_; lean_object* v_key_1438_; lean_object* v_val_1439_; lean_object* v___x_1440_; 
v___x_1436_ = lean_array_uget_borrowed(v_as_1426_, v_i_1427_);
v_ref_1437_ = lean_ctor_get(v___x_1436_, 0);
v_key_1438_ = lean_ctor_get(v___x_1436_, 1);
v_val_1439_ = lean_ctor_get(v___x_1436_, 2);
lean_inc(v_key_1438_);
v___x_1440_ = l_Lean_Name_components(v_key_1438_);
if (lean_obj_tag(v___x_1440_) == 0)
{
v___y_1431_ = v_b_1429_;
goto v___jp_1430_;
}
else
{
lean_object* v_head_1441_; lean_object* v_tail_1442_; lean_object* v___x_1443_; 
v_head_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_head_1441_);
v_tail_1442_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_tail_1442_);
lean_dec_ref_known(v___x_1440_, 2);
lean_inc_ref(v_val_1439_);
lean_inc(v_ref_1437_);
v___x_1443_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1429_, v_ref_1437_, v_head_1441_, v_tail_1442_, v_val_1439_);
v___y_1431_ = v___x_1443_;
goto v___jp_1430_;
}
}
else
{
return v_b_1429_;
}
v___jp_1430_:
{
size_t v___x_1432_; size_t v___x_1433_; 
v___x_1432_ = ((size_t)1ULL);
v___x_1433_ = lean_usize_add(v_i_1427_, v___x_1432_);
v_i_1427_ = v___x_1433_;
v_b_1429_ = v___y_1431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1444_, lean_object* v_i_1445_, lean_object* v_stop_1446_, lean_object* v_b_1447_){
_start:
{
size_t v_i_boxed_1448_; size_t v_stop_boxed_1449_; lean_object* v_res_1450_; 
v_i_boxed_1448_ = lean_unbox_usize(v_i_1445_);
lean_dec(v_i_1445_);
v_stop_boxed_1449_ = lean_unbox_usize(v_stop_1446_);
lean_dec(v_stop_1446_);
v_res_1450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1444_, v_i_boxed_1448_, v_stop_boxed_1449_, v_b_1447_);
lean_dec_ref(v_as_1444_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1451_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1452_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_array_get_size(v_items_1451_);
v___x_1455_ = lean_nat_dec_lt(v___x_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
return v___x_1452_;
}
else
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_nat_dec_le(v___x_1454_, v___x_1454_);
if (v___x_1456_ == 0)
{
if (v___x_1455_ == 0)
{
return v___x_1452_;
}
else
{
size_t v___x_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = ((size_t)0ULL);
v___x_1458_ = lean_usize_of_nat(v___x_1454_);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1451_, v___x_1457_, v___x_1458_, v___x_1452_);
return v___x_1459_;
}
}
else
{
size_t v___x_1460_; size_t v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = lean_usize_of_nat(v___x_1454_);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1451_, v___x_1460_, v___x_1461_, v___x_1452_);
return v___x_1462_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1463_);
lean_dec_ref(v_items_1463_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1467_);
lean_inc_ref(v_a_1466_);
v___x_1470_ = lean_apply_4(v_x_1465_, v___x_1469_, v_a_1466_, v_a_1467_, lean_box(0));
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1481_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_snd_1475_; lean_object* v_items_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v_snd_1475_ = lean_ctor_get(v_a_1471_, 1);
lean_inc(v_snd_1475_);
lean_dec(v_a_1471_);
v_items_1476_ = lean_ctor_get(v_snd_1475_, 5);
lean_inc_ref(v_items_1476_);
lean_dec(v_snd_1475_);
v___x_1477_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1476_);
lean_dec_ref(v_items_1476_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1477_);
v___x_1479_ = v___x_1473_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1470_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1470_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1503_, uint8_t v___y_1504_, lean_object* v_x_1505_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 1)
{
lean_object* v_pre_1506_; 
v_pre_1506_ = lean_ctor_get(v_x_1505_, 0);
switch(lean_obj_tag(v_pre_1506_))
{
case 1:
{
lean_object* v_pre_1507_; 
v_pre_1507_ = lean_ctor_get(v_pre_1506_, 0);
switch(lean_obj_tag(v_pre_1507_))
{
case 0:
{
lean_object* v_str_1508_; lean_object* v_str_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_str_1508_ = lean_ctor_get(v_x_1505_, 1);
v_str_1509_ = lean_ctor_get(v_pre_1506_, 1);
v___x_1510_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1511_ = lean_string_dec_eq(v_str_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1513_ = lean_string_dec_eq(v_str_1509_, v___x_1512_);
if (v___x_1513_ == 0)
{
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1515_ = lean_string_dec_eq(v_str_1508_, v___x_1514_);
if (v___x_1515_ == 0)
{
return v___x_1515_;
}
else
{
return v_suppressElabErrors_1503_;
}
}
}
else
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1517_ = lean_string_dec_eq(v_str_1508_, v___x_1516_);
if (v___x_1517_ == 0)
{
return v___x_1517_;
}
else
{
return v_suppressElabErrors_1503_;
}
}
}
case 1:
{
lean_object* v_pre_1518_; 
v_pre_1518_ = lean_ctor_get(v_pre_1507_, 0);
if (lean_obj_tag(v_pre_1518_) == 0)
{
lean_object* v_str_1519_; lean_object* v_str_1520_; lean_object* v_str_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_str_1519_ = lean_ctor_get(v_x_1505_, 1);
v_str_1520_ = lean_ctor_get(v_pre_1506_, 1);
v_str_1521_ = lean_ctor_get(v_pre_1507_, 1);
v___x_1522_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1523_ = lean_string_dec_eq(v_str_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
return v___x_1523_;
}
else
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1525_ = lean_string_dec_eq(v_str_1520_, v___x_1524_);
if (v___x_1525_ == 0)
{
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1527_ = lean_string_dec_eq(v_str_1519_, v___x_1526_);
if (v___x_1527_ == 0)
{
return v___x_1527_;
}
else
{
return v_suppressElabErrors_1503_;
}
}
}
}
else
{
return v___y_1504_;
}
}
default: 
{
return v___y_1504_;
}
}
}
case 0:
{
lean_object* v_str_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_str_1528_ = lean_ctor_get(v_x_1505_, 1);
v___x_1529_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1530_ = lean_string_dec_eq(v_str_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
return v___x_1530_;
}
else
{
return v_suppressElabErrors_1503_;
}
}
default: 
{
return v___y_1504_;
}
}
}
else
{
return v___y_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1531_, lean_object* v___y_1532_, lean_object* v_x_1533_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1534_; uint8_t v___y_10676__boxed_1535_; uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_suppressElabErrors_boxed_1534_ = lean_unbox(v_suppressElabErrors_1531_);
v___y_10676__boxed_1535_ = lean_unbox(v___y_1532_);
v_res_1536_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1534_, v___y_10676__boxed_1535_, v_x_1533_);
lean_dec(v_x_1533_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1538_, lean_object* v_opt_1539_){
_start:
{
lean_object* v_name_1540_; lean_object* v_defValue_1541_; lean_object* v_map_1542_; lean_object* v___x_1543_; 
v_name_1540_ = lean_ctor_get(v_opt_1539_, 0);
v_defValue_1541_ = lean_ctor_get(v_opt_1539_, 1);
v_map_1542_ = lean_ctor_get(v_opts_1538_, 0);
v___x_1543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1542_, v_name_1540_);
if (lean_obj_tag(v___x_1543_) == 0)
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_unbox(v_defValue_1541_);
return v___x_1544_;
}
else
{
lean_object* v_val_1545_; 
v_val_1545_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v___x_1543_, 1);
if (lean_obj_tag(v_val_1545_) == 1)
{
uint8_t v_v_1546_; 
v_v_1546_ = lean_ctor_get_uint8(v_val_1545_, 0);
lean_dec_ref_known(v_val_1545_, 0);
return v_v_1546_;
}
else
{
uint8_t v___x_1547_; 
lean_dec(v_val_1545_);
v___x_1547_ = lean_unbox(v_defValue_1541_);
return v___x_1547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1548_, lean_object* v_opt_1549_){
_start:
{
uint8_t v_res_1550_; lean_object* v_r_1551_; 
v_res_1550_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1548_, v_opt_1549_);
lean_dec_ref(v_opt_1549_);
lean_dec_ref(v_opts_1548_);
v_r_1551_ = lean_box(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1553_, lean_object* v_msgData_1554_, uint8_t v_severity_1555_, uint8_t v_isSilent_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_a_1562_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; uint8_t v___y_1569_; lean_object* v___y_1570_; uint8_t v___y_1571_; lean_object* v___y_1572_; lean_object* v_toCold_1573_; lean_object* v___y_1574_; lean_object* v___y_1602_; lean_object* v___y_1603_; uint8_t v___y_1604_; uint8_t v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; lean_object* v___y_1609_; uint8_t v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; uint8_t v___y_1632_; uint8_t v___y_1633_; lean_object* v___y_1634_; uint8_t v___y_1638_; uint8_t v___y_1639_; uint8_t v___y_1640_; uint8_t v___x_1651_; uint8_t v___y_1653_; uint8_t v___y_1654_; uint8_t v___y_1655_; uint8_t v___y_1657_; uint8_t v___x_1666_; 
v___x_1651_ = 2;
v___x_1666_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1555_, v___x_1651_);
if (v___x_1666_ == 0)
{
v___y_1657_ = v___x_1666_;
goto v___jp_1656_;
}
else
{
uint8_t v___x_1667_; 
lean_inc_ref(v_msgData_1554_);
v___x_1667_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1554_);
v___y_1657_ = v___x_1667_;
goto v___jp_1656_;
}
v___jp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_a_1562_);
lean_ctor_set(v___x_1563_, 1, v___y_1557_);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
v___jp_1565_:
{
lean_object* v_currNamespace_1575_; lean_object* v_openDecls_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_env_1581_; lean_object* v_nextMacroScope_1582_; lean_object* v_ngen_1583_; lean_object* v_auxDeclNGen_1584_; lean_object* v_traceState_1585_; lean_object* v_cache_1586_; lean_object* v_recordedDeps_1587_; lean_object* v_messages_1588_; lean_object* v_infoState_1589_; lean_object* v_snapshotTasks_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1600_; 
v_currNamespace_1575_ = lean_ctor_get(v_toCold_1573_, 4);
v_openDecls_1576_ = lean_ctor_get(v_toCold_1573_, 5);
lean_inc(v_openDecls_1576_);
lean_inc(v_currNamespace_1575_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_currNamespace_1575_);
lean_ctor_set(v___x_1577_, 1, v_openDecls_1576_);
v___x_1578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v___y_1572_);
lean_inc_ref(v___y_1570_);
lean_inc_ref(v___y_1566_);
v___x_1579_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1579_, 0, v___y_1566_);
lean_ctor_set(v___x_1579_, 1, v___y_1568_);
lean_ctor_set(v___x_1579_, 2, v___y_1567_);
lean_ctor_set(v___x_1579_, 3, v___y_1570_);
lean_ctor_set(v___x_1579_, 4, v___x_1578_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*5, v___y_1569_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*5 + 1, v___y_1571_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*5 + 2, v_isSilent_1556_);
v___x_1580_ = lean_st_ref_take(v___y_1574_);
v_env_1581_ = lean_ctor_get(v___x_1580_, 0);
v_nextMacroScope_1582_ = lean_ctor_get(v___x_1580_, 1);
v_ngen_1583_ = lean_ctor_get(v___x_1580_, 2);
v_auxDeclNGen_1584_ = lean_ctor_get(v___x_1580_, 3);
v_traceState_1585_ = lean_ctor_get(v___x_1580_, 4);
v_cache_1586_ = lean_ctor_get(v___x_1580_, 5);
v_recordedDeps_1587_ = lean_ctor_get(v___x_1580_, 6);
v_messages_1588_ = lean_ctor_get(v___x_1580_, 7);
v_infoState_1589_ = lean_ctor_get(v___x_1580_, 8);
v_snapshotTasks_1590_ = lean_ctor_get(v___x_1580_, 9);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1592_ = v___x_1580_;
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_snapshotTasks_1590_);
lean_inc(v_infoState_1589_);
lean_inc(v_messages_1588_);
lean_inc(v_recordedDeps_1587_);
lean_inc(v_cache_1586_);
lean_inc(v_traceState_1585_);
lean_inc(v_auxDeclNGen_1584_);
lean_inc(v_ngen_1583_);
lean_inc(v_nextMacroScope_1582_);
lean_inc(v_env_1581_);
lean_dec(v___x_1580_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Lean_MessageLog_add(v___x_1579_, v_messages_1588_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 7, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_env_1581_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_nextMacroScope_1582_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_ngen_1583_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_auxDeclNGen_1584_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_traceState_1585_);
lean_ctor_set(v_reuseFailAlloc_1599_, 5, v_cache_1586_);
lean_ctor_set(v_reuseFailAlloc_1599_, 6, v_recordedDeps_1587_);
lean_ctor_set(v_reuseFailAlloc_1599_, 7, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1599_, 8, v_infoState_1589_);
lean_ctor_set(v_reuseFailAlloc_1599_, 9, v_snapshotTasks_1590_);
v___x_1597_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_st_ref_put(v___y_1574_, v___x_1597_);
v_a_1562_ = v___x_1594_;
goto v___jp_1561_;
}
}
}
v___jp_1601_:
{
lean_object* v_fileName_1610_; lean_object* v_fileMap_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1626_; 
v_fileName_1610_ = lean_ctor_get(v___y_1607_, 0);
v_fileMap_1611_ = lean_ctor_get(v___y_1607_, 1);
v___x_1612_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1554_);
v___x_1613_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1612_, v___y_1558_, v___y_1559_);
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1626_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1626_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_inc_ref_n(v_fileMap_1611_, 2);
v___x_1618_ = l_Lean_FileMap_toPosition(v_fileMap_1611_, v___y_1606_);
lean_dec(v___y_1606_);
v___x_1619_ = l_Lean_FileMap_toPosition(v_fileMap_1611_, v___y_1609_);
lean_dec(v___y_1609_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set_tag(v___x_1616_, 1);
lean_ctor_set(v___x_1616_, 0, v___x_1619_);
v___x_1621_ = v___x_1616_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; 
v___x_1622_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1604_ == 0)
{
lean_dec_ref(v___y_1602_);
v___y_1566_ = v_fileName_1610_;
v___y_1567_ = v___x_1621_;
v___y_1568_ = v___x_1618_;
v___y_1569_ = v___y_1605_;
v___y_1570_ = v___x_1622_;
v___y_1571_ = v___y_1608_;
v___y_1572_ = v_a_1614_;
v_toCold_1573_ = v___y_1603_;
v___y_1574_ = v___y_1559_;
goto v___jp_1565_;
}
else
{
uint8_t v___x_1623_; 
lean_inc(v_a_1614_);
v___x_1623_ = l_Lean_MessageData_hasTag(v___y_1602_, v_a_1614_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; 
lean_dec_ref(v___x_1621_);
lean_dec_ref(v___x_1618_);
lean_dec(v_a_1614_);
v___x_1624_ = lean_box(0);
v_a_1562_ = v___x_1624_;
goto v___jp_1561_;
}
else
{
v___y_1566_ = v_fileName_1610_;
v___y_1567_ = v___x_1621_;
v___y_1568_ = v___x_1618_;
v___y_1569_ = v___y_1605_;
v___y_1570_ = v___x_1622_;
v___y_1571_ = v___y_1608_;
v___y_1572_ = v_a_1614_;
v_toCold_1573_ = v___y_1603_;
v___y_1574_ = v___y_1559_;
goto v___jp_1565_;
}
}
}
}
}
v___jp_1627_:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Syntax_getTailPos_x3f(v___y_1631_, v___y_1632_);
lean_dec(v___y_1631_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_inc(v___y_1634_);
v___y_1602_ = v___y_1629_;
v___y_1603_ = v___y_1630_;
v___y_1604_ = v___y_1628_;
v___y_1605_ = v___y_1632_;
v___y_1606_ = v___y_1634_;
v___y_1607_ = v___y_1630_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v___y_1634_;
goto v___jp_1601_;
}
else
{
lean_object* v_val_1636_; 
v_val_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_val_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___y_1602_ = v___y_1629_;
v___y_1603_ = v___y_1630_;
v___y_1604_ = v___y_1628_;
v___y_1605_ = v___y_1632_;
v___y_1606_ = v___y_1634_;
v___y_1607_ = v___y_1630_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v_val_1636_;
goto v___jp_1601_;
}
}
v___jp_1637_:
{
lean_object* v_toCold_1641_; lean_object* v_ref_1642_; uint8_t v_suppressElabErrors_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___f_1646_; lean_object* v_ref_1647_; lean_object* v___x_1648_; 
v_toCold_1641_ = lean_ctor_get(v___y_1558_, 0);
v_ref_1642_ = lean_ctor_get(v___y_1558_, 2);
v_suppressElabErrors_1643_ = lean_ctor_get_uint8(v___y_1558_, sizeof(void*)*3 + 2);
v___x_1644_ = lean_box(v_suppressElabErrors_1643_);
v___x_1645_ = lean_box(v___y_1638_);
v___f_1646_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1646_, 0, v___x_1644_);
lean_closure_set(v___f_1646_, 1, v___x_1645_);
v_ref_1647_ = l_Lean_replaceRef(v_ref_1553_, v_ref_1642_);
v___x_1648_ = l_Lean_Syntax_getPos_x3f(v_ref_1647_, v___y_1639_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_unsigned_to_nat(0u);
v___y_1628_ = v_suppressElabErrors_1643_;
v___y_1629_ = v___f_1646_;
v___y_1630_ = v_toCold_1641_;
v___y_1631_ = v_ref_1647_;
v___y_1632_ = v___y_1639_;
v___y_1633_ = v___y_1640_;
v___y_1634_ = v___x_1649_;
goto v___jp_1627_;
}
else
{
lean_object* v_val_1650_; 
v_val_1650_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_val_1650_);
lean_dec_ref_known(v___x_1648_, 1);
v___y_1628_ = v_suppressElabErrors_1643_;
v___y_1629_ = v___f_1646_;
v___y_1630_ = v_toCold_1641_;
v___y_1631_ = v_ref_1647_;
v___y_1632_ = v___y_1639_;
v___y_1633_ = v___y_1640_;
v___y_1634_ = v_val_1650_;
goto v___jp_1627_;
}
}
v___jp_1652_:
{
if (v___y_1655_ == 0)
{
v___y_1638_ = v___y_1653_;
v___y_1639_ = v___y_1654_;
v___y_1640_ = v_severity_1555_;
goto v___jp_1637_;
}
else
{
v___y_1638_ = v___y_1653_;
v___y_1639_ = v___y_1654_;
v___y_1640_ = v___x_1651_;
goto v___jp_1637_;
}
}
v___jp_1656_:
{
if (v___y_1657_ == 0)
{
uint8_t v___x_1658_; uint8_t v___x_1659_; 
v___x_1658_ = 1;
v___x_1659_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1555_, v___x_1658_);
if (v___x_1659_ == 0)
{
v___y_1653_ = v___y_1657_;
v___y_1654_ = v___y_1657_;
v___y_1655_ = v___x_1659_;
goto v___jp_1652_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1660_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1558_);
v___x_1661_ = l_Lean_warningAsError;
v___x_1662_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v___x_1660_, v___x_1661_);
lean_dec_ref(v___x_1660_);
v___y_1653_ = v___y_1657_;
v___y_1654_ = v___y_1657_;
v___y_1655_ = v___x_1662_;
goto v___jp_1652_;
}
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec_ref(v_msgData_1554_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v___y_1557_);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1668_, lean_object* v_msgData_1669_, lean_object* v_severity_1670_, lean_object* v_isSilent_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_severity_boxed_1676_; uint8_t v_isSilent_boxed_1677_; lean_object* v_res_1678_; 
v_severity_boxed_1676_ = lean_unbox(v_severity_1670_);
v_isSilent_boxed_1677_ = lean_unbox(v_isSilent_1671_);
v_res_1678_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1668_, v_msgData_1669_, v_severity_boxed_1676_, v_isSilent_boxed_1677_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_ref_1668_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1679_, lean_object* v_msgData_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
uint8_t v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = 2;
v___x_1686_ = 0;
v___x_1687_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1679_, v_msgData_1680_, v___x_1685_, v___x_1686_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1688_, lean_object* v_msgData_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1688_, v_msgData_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v_ref_1688_);
return v_res_1694_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1698_ = l_Lean_MessageData_ofFormat(v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1699_, lean_object* v_as_1700_, size_t v_sz_1701_, size_t v_i_1702_, uint8_t v_b_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_snd_1709_; lean_object* v_snd_1710_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v_a_1734_; uint8_t v___x_1737_; 
v___x_1737_ = lean_usize_dec_lt(v_i_1702_, v_sz_1701_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_box(v_b_1703_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v___y_1704_);
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1742_; uint8_t v_recovering_1743_; 
v_a_1741_ = lean_array_uget_borrowed(v_as_1700_, v_i_1702_);
v___x_1742_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1741_);
v_recovering_1743_ = l_Lean_Syntax_isOfKind(v_a_1741_, v___x_1742_);
if (v_recovering_1743_ == 0)
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_a_1741_);
v___x_1745_ = l_Lean_Syntax_isOfKind(v_a_1741_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1741_);
v___x_1747_ = l_Lean_Syntax_isOfKind(v_a_1741_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1704_);
v___x_1749_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1741_, v___x_1748_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v_snd_1751_; lean_object* v___x_1752_; 
lean_dec_ref(v___y_1704_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v_snd_1751_ = lean_ctor_get(v_a_1750_, 1);
lean_inc(v_snd_1751_);
lean_dec(v_a_1750_);
v___x_1752_ = lean_box(v_b_1703_);
v_snd_1709_ = v___x_1752_;
v_snd_1710_ = v_snd_1751_;
goto v___jp_1708_;
}
else
{
lean_object* v_a_1753_; 
v_a_1753_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1749_, 1);
v_a_1734_ = v_a_1753_;
goto v___jp_1733_;
}
}
else
{
lean_object* v___x_1754_; 
lean_inc_ref(v___y_1704_);
lean_inc(v_a_1741_);
v___x_1754_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1741_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v_snd_1756_; lean_object* v___x_1757_; 
lean_dec_ref(v___y_1704_);
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v_snd_1756_ = lean_ctor_get(v_a_1755_, 1);
lean_inc(v_snd_1756_);
lean_dec(v_a_1755_);
v___x_1757_ = lean_box(v_recovering_1743_);
v_snd_1709_ = v___x_1757_;
v_snd_1710_ = v_snd_1756_;
goto v___jp_1708_;
}
else
{
lean_object* v_a_1758_; 
v_a_1758_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1754_, 1);
v_a_1734_ = v_a_1758_;
goto v___jp_1733_;
}
}
}
else
{
lean_object* v___x_1759_; 
lean_inc_ref(v___y_1704_);
lean_inc(v_a_1741_);
v___x_1759_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1741_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v_snd_1761_; lean_object* v___x_1762_; 
lean_dec_ref(v___y_1704_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v_snd_1761_ = lean_ctor_get(v_a_1760_, 1);
lean_inc(v_snd_1761_);
lean_dec(v_a_1760_);
v___x_1762_ = lean_box(v_recovering_1743_);
v_snd_1709_ = v___x_1762_;
v_snd_1710_ = v_snd_1761_;
goto v___jp_1708_;
}
else
{
lean_object* v_a_1763_; 
v_a_1763_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1759_, 1);
v_a_1734_ = v_a_1763_;
goto v___jp_1733_;
}
}
}
else
{
if (v_b_1703_ == 0)
{
lean_object* v___x_1764_; 
lean_inc_ref(v___y_1704_);
lean_inc(v_a_1741_);
v___x_1764_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1741_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v_snd_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v___y_1704_);
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v_snd_1766_ = lean_ctor_get(v_a_1765_, 1);
lean_inc(v_snd_1766_);
lean_dec(v_a_1765_);
v___x_1767_ = lean_box(v_b_1703_);
v_snd_1709_ = v___x_1767_;
v_snd_1710_ = v_snd_1766_;
goto v___jp_1708_;
}
else
{
lean_object* v_a_1768_; 
v_a_1768_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1764_, 1);
v_a_1734_ = v_a_1768_;
goto v___jp_1733_;
}
}
else
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_box(v_b_1703_);
v_snd_1709_ = v___x_1769_;
v_snd_1710_ = v___y_1704_;
goto v___jp_1708_;
}
}
}
v___jp_1708_:
{
size_t v___x_1711_; size_t v___x_1712_; uint8_t v___x_1713_; 
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1702_, v___x_1711_);
v___x_1713_ = lean_unbox(v_snd_1709_);
lean_dec(v_snd_1709_);
v_i_1702_ = v___x_1712_;
v_b_1703_ = v___x_1713_;
v___y_1704_ = v_snd_1710_;
goto _start;
}
v___jp_1715_:
{
if (v___y_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = l_Lean_Exception_getRef(v___y_1716_);
v___x_1719_ = l_Lean_Exception_toMessageData(v___y_1716_);
v___x_1720_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1718_, v___x_1719_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___x_1718_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v_snd_1722_; lean_object* v___x_1723_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v_snd_1722_ = lean_ctor_get(v_a_1721_, 1);
lean_inc(v_snd_1722_);
lean_dec(v_a_1721_);
v___x_1723_ = lean_box(v_recovering_1699_);
v_snd_1709_ = v___x_1723_;
v_snd_1710_ = v_snd_1722_;
goto v___jp_1708_;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v_a_1724_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1720_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1720_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_object* v___x_1732_; 
lean_dec_ref(v___y_1704_);
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___y_1716_);
return v___x_1732_;
}
}
v___jp_1733_:
{
uint8_t v___x_1735_; 
v___x_1735_ = l_Lean_Exception_isInterrupt(v_a_1734_);
if (v___x_1735_ == 0)
{
uint8_t v___x_1736_; 
lean_inc_ref(v_a_1734_);
v___x_1736_ = l_Lean_Exception_isRuntime(v_a_1734_);
v___y_1716_ = v_a_1734_;
v___y_1717_ = v___x_1736_;
goto v___jp_1715_;
}
else
{
v___y_1716_ = v_a_1734_;
v___y_1717_ = v___x_1735_;
goto v___jp_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1770_, lean_object* v_as_1771_, lean_object* v_sz_1772_, lean_object* v_i_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
uint8_t v_recovering_boxed_1779_; size_t v_sz_boxed_1780_; size_t v_i_boxed_1781_; uint8_t v_b_boxed_1782_; lean_object* v_res_1783_; 
v_recovering_boxed_1779_ = lean_unbox(v_recovering_1770_);
v_sz_boxed_1780_ = lean_unbox_usize(v_sz_1772_);
lean_dec(v_sz_1772_);
v_i_boxed_1781_ = lean_unbox_usize(v_i_1773_);
lean_dec(v_i_1773_);
v_b_boxed_1782_ = lean_unbox(v_b_1774_);
v_res_1783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1779_, v_as_1771_, v_sz_boxed_1780_, v_i_boxed_1781_, v_b_boxed_1782_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v_as_1771_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_ref_1788_; lean_object* v___x_1789_; lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1798_; 
v_ref_1788_ = lean_ctor_get(v___y_1785_, 2);
v___x_1789_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1784_, v___y_1785_, v___y_1786_);
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1796_; 
lean_inc(v_ref_1788_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v_ref_1788_);
lean_ctor_set(v___x_1794_, 1, v_a_1790_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 1);
lean_ctor_set(v___x_1792_, 0, v___x_1794_);
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1804_, lean_object* v_msg_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_toCold_1809_; lean_object* v_currRecDepth_1810_; lean_object* v_ref_1811_; uint16_t v_optionFlags_1812_; uint8_t v_suppressElabErrors_1813_; uint8_t v_isRecordingDeps_1814_; lean_object* v_ref_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_toCold_1809_ = lean_ctor_get(v___y_1806_, 0);
v_currRecDepth_1810_ = lean_ctor_get(v___y_1806_, 1);
v_ref_1811_ = lean_ctor_get(v___y_1806_, 2);
v_optionFlags_1812_ = lean_ctor_get_uint16(v___y_1806_, sizeof(void*)*3);
v_suppressElabErrors_1813_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1814_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 3);
v_ref_1815_ = l_Lean_replaceRef(v_ref_1804_, v_ref_1811_);
lean_inc(v_currRecDepth_1810_);
lean_inc_ref(v_toCold_1809_);
v___x_1816_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1816_, 0, v_toCold_1809_);
lean_ctor_set(v___x_1816_, 1, v_currRecDepth_1810_);
lean_ctor_set(v___x_1816_, 2, v_ref_1815_);
lean_ctor_set_uint16(v___x_1816_, sizeof(void*)*3, v_optionFlags_1812_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*3 + 2, v_suppressElabErrors_1813_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*3 + 3, v_isRecordingDeps_1814_);
v___x_1817_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1805_, v___x_1816_, v___y_1807_);
lean_dec_ref_known(v___x_1816_, 3);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1818_, lean_object* v_msg_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1818_, v_msg_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v_ref_1818_);
return v_res_1823_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1836_);
v___x_1841_ = l_Lean_Syntax_isOfKind(v_x_1836_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1843_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1836_, v___x_1842_, v_a_1837_, v_a_1838_);
lean_dec(v_x_1836_);
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v_recovering_1847_; 
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = l_Lean_Syntax_getArg(v_x_1836_, v___x_1844_);
v___x_1846_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1847_ = l_Lean_Syntax_isOfKind(v___x_1845_, v___x_1846_);
if (v_recovering_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1849_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1836_, v___x_1848_, v_a_1837_, v_a_1838_);
lean_dec(v_x_1836_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v_xs_1852_; uint8_t v_recovering_1853_; lean_object* v___x_1854_; size_t v_sz_1855_; size_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1850_ = lean_unsigned_to_nat(1u);
v___x_1851_ = l_Lean_Syntax_getArg(v_x_1836_, v___x_1850_);
lean_dec(v_x_1836_);
v_xs_1852_ = l_Lean_Syntax_getArgs(v___x_1851_);
lean_dec(v___x_1851_);
v_recovering_1853_ = 0;
v___x_1854_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1852_);
lean_dec_ref(v_xs_1852_);
v_sz_1855_ = lean_array_size(v___x_1854_);
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1847_, v___x_1854_, v_sz_1855_, v___x_1856_, v_recovering_1853_, v___x_1857_, v_a_1837_, v_a_1838_);
lean_dec_ref(v___x_1854_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1869_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1869_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1869_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v_snd_1863_; lean_object* v_items_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v_snd_1863_ = lean_ctor_get(v_a_1859_, 1);
lean_inc(v_snd_1863_);
lean_dec(v_a_1859_);
v_items_1864_ = lean_ctor_get(v_snd_1863_, 5);
lean_inc_ref(v_items_1864_);
lean_dec(v_snd_1863_);
v___x_1865_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1864_);
lean_dec_ref(v_items_1864_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1865_);
v___x_1867_ = v___x_1861_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1858_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1858_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lake_Toml_elabToml(v_x_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1883_, lean_object* v_ref_1884_, lean_object* v_msg_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1884_, v_msg_1885_, v___y_1886_, v___y_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1890_, lean_object* v_ref_1891_, lean_object* v_msg_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1890_, v_ref_1891_, v_msg_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v_ref_1891_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1897_, lean_object* v_msg_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1898_, v___y_1899_, v___y_1900_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_msg_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1903_, v_msg_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1908_;
}
}
lean_object* runtime_initialize_Lake_Toml_Elab_Value(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Elab_Expression(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_instInhabitedKeyTy_default = _init_l_Lake_Toml_instInhabitedKeyTy_default();
l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy = _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy();
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Elab_Expression(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Toml_Elab_Value(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Elab_Expression(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Elab_Expression(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Elab_Expression(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Elab_Expression(builtin);
}
#ifdef __cplusplus
}
#endif
