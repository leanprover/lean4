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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
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
default: 
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___boxed(lean_object* v_x_7_){
_start:
{
uint8_t v_x_boxed_8_; lean_object* v_res_9_; 
v_x_boxed_8_ = lean_unbox(v_x_7_);
v_res_9_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(v_x_boxed_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(lean_object* v_k_10_){
_start:
{
lean_inc(v_k_10_);
return v_k_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg___boxed(lean_object* v_k_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(v_k_11_);
lean_dec(v_k_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, uint8_t v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_inc(v_k_17_);
return v_k_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
uint8_t v_t_boxed_23_; lean_object* v_res_24_; 
v_t_boxed_23_ = lean_unbox(v_t_20_);
v_res_24_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_boxed_23_, v_h_21_, v_k_22_);
lean_dec(v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(lean_object* v_value_25_){
_start:
{
lean_inc(v_value_25_);
return v_value_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg___boxed(lean_object* v_value_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(v_value_26_);
lean_dec(v_value_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(lean_object* v_motive_28_, uint8_t v_t_29_, lean_object* v_h_30_, lean_object* v_value_31_){
_start:
{
lean_inc(v_value_31_);
return v_value_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_value_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_value_35_);
lean_dec(v_value_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(lean_object* v_stdTable_38_){
_start:
{
lean_inc(v_stdTable_38_);
return v_stdTable_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg___boxed(lean_object* v_stdTable_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(v_stdTable_39_);
lean_dec(v_stdTable_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_stdTable_44_){
_start:
{
lean_inc(v_stdTable_44_);
return v_stdTable_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___boxed(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_stdTable_48_){
_start:
{
uint8_t v_t_boxed_49_; lean_object* v_res_50_; 
v_t_boxed_49_ = lean_unbox(v_t_46_);
v_res_50_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(v_motive_45_, v_t_boxed_49_, v_h_47_, v_stdTable_48_);
lean_dec(v_stdTable_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(lean_object* v_array_51_){
_start:
{
lean_inc(v_array_51_);
return v_array_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg___boxed(lean_object* v_array_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(v_array_52_);
lean_dec(v_array_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(lean_object* v_motive_54_, uint8_t v_t_55_, lean_object* v_h_56_, lean_object* v_array_57_){
_start:
{
lean_inc(v_array_57_);
return v_array_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___boxed(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_array_61_){
_start:
{
uint8_t v_t_boxed_62_; lean_object* v_res_63_; 
v_t_boxed_62_ = lean_unbox(v_t_59_);
v_res_63_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(v_motive_58_, v_t_boxed_62_, v_h_60_, v_array_61_);
lean_dec(v_array_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(lean_object* v_dottedPrefix_64_){
_start:
{
lean_inc(v_dottedPrefix_64_);
return v_dottedPrefix_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg___boxed(lean_object* v_dottedPrefix_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(v_dottedPrefix_65_);
lean_dec(v_dottedPrefix_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(lean_object* v_motive_67_, uint8_t v_t_68_, lean_object* v_h_69_, lean_object* v_dottedPrefix_70_){
_start:
{
lean_inc(v_dottedPrefix_70_);
return v_dottedPrefix_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___boxed(lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_dottedPrefix_74_){
_start:
{
uint8_t v_t_boxed_75_; lean_object* v_res_76_; 
v_t_boxed_75_ = lean_unbox(v_t_72_);
v_res_76_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(v_motive_71_, v_t_boxed_75_, v_h_73_, v_dottedPrefix_74_);
lean_dec(v_dottedPrefix_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(lean_object* v_headerPrefix_77_){
_start:
{
lean_inc(v_headerPrefix_77_);
return v_headerPrefix_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg___boxed(lean_object* v_headerPrefix_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(v_headerPrefix_78_);
lean_dec(v_headerPrefix_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(lean_object* v_motive_80_, uint8_t v_t_81_, lean_object* v_h_82_, lean_object* v_headerPrefix_83_){
_start:
{
lean_inc(v_headerPrefix_83_);
return v_headerPrefix_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___boxed(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_headerPrefix_87_){
_start:
{
uint8_t v_t_boxed_88_; lean_object* v_res_89_; 
v_t_boxed_88_ = lean_unbox(v_t_85_);
v_res_89_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(v_motive_84_, v_t_boxed_88_, v_h_86_, v_headerPrefix_87_);
lean_dec(v_headerPrefix_87_);
return v_res_89_;
}
}
static uint8_t _init_l_Lake_Toml_instInhabitedKeyTy_default(void){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
static uint8_t _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy(void){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(uint8_t v_ty_97_){
_start:
{
switch(v_ty_97_)
{
case 0:
{
lean_object* v___x_98_; 
v___x_98_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0));
return v___x_98_;
}
case 1:
{
lean_object* v___x_99_; 
v___x_99_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1));
return v___x_99_;
}
case 2:
{
lean_object* v___x_100_; 
v___x_100_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2));
return v___x_100_;
}
case 3:
{
lean_object* v___x_101_; 
v___x_101_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3));
return v___x_101_;
}
default: 
{
lean_object* v___x_102_; 
v___x_102_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4));
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed(lean_object* v_ty_103_){
_start:
{
uint8_t v_ty_boxed_104_; lean_object* v_res_105_; 
v_ty_boxed_104_ = lean_unbox(v_ty_103_);
v_res_105_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v_ty_boxed_104_);
return v_res_105_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(uint8_t v_ty_108_){
_start:
{
switch(v_ty_108_)
{
case 1:
{
uint8_t v___x_109_; 
v___x_109_ = 1;
return v___x_109_;
}
case 4:
{
uint8_t v___x_110_; 
v___x_110_ = 1;
return v___x_110_;
}
case 3:
{
uint8_t v___x_111_; 
v___x_111_ = 1;
return v___x_111_;
}
default: 
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix___boxed(lean_object* v_ty_113_){
_start:
{
uint8_t v_ty_boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_ty_boxed_114_ = lean_unbox(v_ty_113_);
v_res_115_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(v_ty_boxed_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_125_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
lean_ctor_set(v___x_130_, 2, v___x_129_);
lean_ctor_set(v___x_130_, 3, v___x_129_);
lean_ctor_set(v___x_130_, 4, v___x_128_);
lean_ctor_set(v___x_130_, 5, v___x_128_);
lean_ctor_set(v___x_130_, 6, v___x_128_);
lean_ctor_set(v___x_130_, 7, v___x_128_);
lean_ctor_set(v___x_130_, 8, v___x_128_);
lean_ctor_set(v___x_130_, 9, v___x_128_);
lean_ctor_set(v___x_130_, 10, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_unsigned_to_nat(32u);
v___x_132_ = lean_mk_empty_array_with_capacity(v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_134_ = ((size_t)5ULL);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_unsigned_to_nat(32u);
v___x_137_ = lean_mk_empty_array_with_capacity(v___x_136_);
v___x_138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3);
v___x_139_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
lean_ctor_set(v___x_139_, 2, v___x_135_);
lean_ctor_set(v___x_139_, 3, v___x_135_);
lean_ctor_set_usize(v___x_139_, 4, v___x_134_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = lean_box(1);
v___x_141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4);
v___x_142_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_140_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(lean_object* v_msgData_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; lean_object* v_toCold_149_; lean_object* v_env_150_; lean_object* v_options_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_148_ = lean_st_ref_get(v___y_146_);
v_toCold_149_ = lean_ctor_get(v___y_145_, 0);
v_env_150_ = lean_ctor_get(v___x_148_, 0);
lean_inc_ref(v_env_150_);
lean_dec(v___x_148_);
v_options_151_ = lean_ctor_get(v_toCold_149_, 2);
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2);
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_151_);
v___x_154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_154_, 0, v_env_150_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
lean_ctor_set(v___x_154_, 2, v___x_153_);
lean_ctor_set(v___x_154_, 3, v_options_151_);
v___x_155_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_msgData_144_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msgData_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_ref_166_; lean_object* v___x_167_; lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_176_; 
v_ref_166_ = lean_ctor_get(v___y_163_, 2);
v___x_167_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_162_, v___y_163_, v___y_164_);
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_176_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
lean_inc(v_ref_166_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v_ref_166_);
lean_ctor_set(v___x_172_, 1, v_a_168_);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 1);
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg___boxed(lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(lean_object* v_ref_182_, lean_object* v_msg_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_toCold_188_; lean_object* v_currRecDepth_189_; lean_object* v_ref_190_; uint16_t v_optionFlags_191_; uint8_t v_suppressElabErrors_192_; uint8_t v_isRecordingDeps_193_; lean_object* v_ref_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_toCold_188_ = lean_ctor_get(v___y_185_, 0);
v_currRecDepth_189_ = lean_ctor_get(v___y_185_, 1);
v_ref_190_ = lean_ctor_get(v___y_185_, 2);
v_optionFlags_191_ = lean_ctor_get_uint16(v___y_185_, sizeof(void*)*3);
v_suppressElabErrors_192_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 2);
v_isRecordingDeps_193_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 3);
v_ref_194_ = l_Lean_replaceRef(v_ref_182_, v_ref_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_toCold_188_);
v___x_195_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_195_, 0, v_toCold_188_);
lean_ctor_set(v___x_195_, 1, v_currRecDepth_189_);
lean_ctor_set(v___x_195_, 2, v_ref_194_);
lean_ctor_set_uint16(v___x_195_, sizeof(void*)*3, v_optionFlags_191_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*3 + 2, v_suppressElabErrors_192_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*3 + 3, v_isRecordingDeps_193_);
v___x_196_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_183_, v___x_195_, v___y_186_);
lean_dec_ref_known(v___x_195_, 3);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object* v_ref_197_, lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_197_, v_msg_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v_ref_197_);
return v_res_203_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_209_ = l_Lean_stringToMessageData(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object* v_as_213_, size_t v_i_214_, size_t v_stop_215_, lean_object* v_b_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_fst_222_; lean_object* v_snd_223_; uint8_t v___x_227_; 
v___x_227_ = lean_usize_dec_eq(v_i_214_, v_stop_215_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_array_uget_borrowed(v_as_213_, v_i_214_);
lean_inc(v___x_228_);
v___x_229_ = l_Lake_Toml_elabSimpleKey(v___x_228_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v_keyTys_231_; lean_object* v_arrKeyTys_232_; lean_object* v_arrParents_233_; lean_object* v_currArrKey_234_; lean_object* v_currKey_235_; lean_object* v_items_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
v_keyTys_231_ = lean_ctor_get(v___y_217_, 0);
v_arrKeyTys_232_ = lean_ctor_get(v___y_217_, 1);
v_arrParents_233_ = lean_ctor_get(v___y_217_, 2);
v_currArrKey_234_ = lean_ctor_get(v___y_217_, 3);
v_currKey_235_ = lean_ctor_get(v___y_217_, 4);
v_items_236_ = lean_ctor_get(v___y_217_, 5);
v___x_237_ = l_Lean_Name_str___override(v_b_216_, v_a_230_);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_231_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 1)
{
lean_object* v_val_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_269_; 
v_val_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_269_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_269_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_val_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_269_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
uint8_t v___x_243_; 
v___x_243_ = lean_unbox(v_val_239_);
if (v___x_243_ == 3)
{
lean_del_object(v___x_241_);
lean_dec(v_val_239_);
v_fst_222_ = v___x_237_;
v_snd_223_ = v___y_217_;
goto v___jp_221_;
}
else
{
lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_244_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_245_ = lean_unbox(v_val_239_);
lean_dec(v_val_239_);
v___x_246_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_245_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 3);
lean_ctor_set(v___x_241_, 0, v___x_246_);
v___x_248_ = v___x_241_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_268_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_249_ = l_Lean_MessageData_ofFormat(v___x_248_);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_244_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_inc(v___x_237_);
v___x_253_ = l_Lean_MessageData_ofName(v___x_237_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_228_, v___x_256_, v___y_217_, v___y_218_, v___y_219_);
lean_dec_ref(v___y_217_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v_snd_259_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v_snd_259_ = lean_ctor_get(v_a_258_, 1);
lean_inc(v_snd_259_);
lean_dec(v_a_258_);
v_fst_222_ = v___x_237_;
v_snd_223_ = v_snd_259_;
goto v___jp_221_;
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec(v___x_237_);
v_a_260_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_257_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_257_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_279_; 
lean_inc_ref(v_items_236_);
lean_inc(v_currKey_235_);
lean_inc(v_currArrKey_234_);
lean_inc(v_arrParents_233_);
lean_inc(v_arrKeyTys_232_);
lean_inc(v_keyTys_231_);
lean_dec(v___x_238_);
v_isSharedCheck_279_ = !lean_is_exclusive(v___y_217_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; 
v_unused_280_ = lean_ctor_get(v___y_217_, 5);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v___y_217_, 4);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v___y_217_, 3);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v___y_217_, 2);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v___y_217_, 1);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v___y_217_, 0);
lean_dec(v_unused_285_);
v___x_271_ = v___y_217_;
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
else
{
lean_dec(v___y_217_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_273_ = 3;
v___x_274_ = lean_box(v___x_273_);
lean_inc(v___x_237_);
v___x_275_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_237_, v___x_274_, v_keyTys_231_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_275_);
v___x_277_ = v___x_271_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_arrKeyTys_232_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_arrParents_233_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_currArrKey_234_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_currKey_235_);
lean_ctor_set(v_reuseFailAlloc_278_, 5, v_items_236_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
v_fst_222_ = v___x_237_;
v_snd_223_ = v___x_277_;
goto v___jp_221_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v___y_217_);
lean_dec(v_b_216_);
v_a_286_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_229_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_229_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_b_216_);
lean_ctor_set(v___x_294_, 1, v___y_217_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
v___jp_221_:
{
size_t v___x_224_; size_t v___x_225_; 
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_add(v_i_214_, v___x_224_);
v_i_214_ = v___x_225_;
v_b_216_ = v_fst_222_;
v___y_217_ = v_snd_223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object* v_as_296_, lean_object* v_i_297_, lean_object* v_stop_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
size_t v_i_boxed_304_; size_t v_stop_boxed_305_; lean_object* v_res_306_; 
v_i_boxed_304_ = lean_unbox_usize(v_i_297_);
lean_dec(v_i_297_);
v_stop_boxed_305_ = lean_unbox_usize(v_stop_298_);
lean_dec(v_stop_298_);
v_res_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_296_, v_i_boxed_304_, v_stop_boxed_305_, v_b_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec_ref(v_as_296_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object* v_ks_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_currKey_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_currKey_312_ = lean_ctor_get(v_a_308_, 4);
lean_inc(v_currKey_312_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_array_get_size(v_ks_307_);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_currKey_312_);
lean_ctor_set(v___x_316_, 1, v_a_308_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_le(v___x_314_, v___x_314_);
if (v___x_318_ == 0)
{
if (v___x_315_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_currKey_312_);
lean_ctor_set(v___x_319_, 1, v_a_308_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
else
{
size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
v___x_321_ = ((size_t)0ULL);
v___x_322_ = lean_usize_of_nat(v___x_314_);
v___x_323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_307_, v___x_321_, v___x_322_, v_currKey_312_, v_a_308_, v_a_309_, v_a_310_);
return v___x_323_;
}
}
else
{
size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_314_);
v___x_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_307_, v___x_324_, v___x_325_, v_currKey_312_, v_a_308_, v_a_309_, v_a_310_);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object* v_ks_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec_ref(v_ks_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_333_, lean_object* v_ref_334_, lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_334_, v_msg_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_341_, lean_object* v_ref_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_341_, v_ref_342_, v_msg_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v_ref_342_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_350_, v___y_352_, v___y_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_356_, v_msg_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_363_, lean_object* v_as_364_, size_t v_i_365_, size_t v_stop_366_, lean_object* v_b_367_){
_start:
{
lean_object* v___y_369_; uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_eq(v_i_365_, v_stop_366_);
if (v___x_373_ == 0)
{
lean_object* v_fst_374_; uint8_t v___x_375_; 
v_fst_374_ = lean_ctor_get(v_b_367_, 0);
v___x_375_ = lean_unbox(v_fst_374_);
if (v___x_375_ == 0)
{
lean_object* v_snd_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
v_snd_376_ = lean_ctor_get(v_b_367_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_b_367_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_b_367_, 0);
lean_dec(v_unused_385_);
v___x_378_ = v_b_367_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_snd_376_);
lean_dec(v_b_367_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_box(v___x_363_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_snd_376_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
v___y_369_ = v___x_382_;
goto v___jp_368_;
}
}
}
else
{
lean_object* v_snd_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_396_; 
v_snd_386_ = lean_ctor_get(v_b_367_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_b_367_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v_b_367_, 0);
lean_dec(v_unused_397_);
v___x_388_ = v_b_367_;
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_snd_386_);
lean_dec(v_b_367_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_390_ = lean_array_uget_borrowed(v_as_364_, v_i_365_);
lean_inc(v___x_390_);
v___x_391_ = lean_array_push(v_snd_386_, v___x_390_);
v___x_392_ = lean_box(v___x_373_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_391_);
lean_ctor_set(v___x_388_, 0, v___x_392_);
v___x_394_ = v___x_388_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_391_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
v___y_369_ = v___x_394_;
goto v___jp_368_;
}
}
}
}
else
{
return v_b_367_;
}
v___jp_368_:
{
size_t v___x_370_; size_t v___x_371_; 
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_add(v_i_365_, v___x_370_);
v_i_365_ = v___x_371_;
v_b_367_ = v___y_369_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_398_, lean_object* v_as_399_, lean_object* v_i_400_, lean_object* v_stop_401_, lean_object* v_b_402_){
_start:
{
uint8_t v___x_2936__boxed_403_; size_t v_i_boxed_404_; size_t v_stop_boxed_405_; lean_object* v_res_406_; 
v___x_2936__boxed_403_ = lean_unbox(v___x_398_);
v_i_boxed_404_ = lean_unbox_usize(v_i_400_);
lean_dec(v_i_400_);
v_stop_boxed_405_ = lean_unbox_usize(v_stop_401_);
lean_dec(v_stop_401_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2936__boxed_403_, v_as_399_, v_i_boxed_404_, v_stop_boxed_405_, v_b_402_);
lean_dec_ref(v_as_399_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_414_, size_t v_i_415_, lean_object* v_bs_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v_bs_416_);
return v___x_418_;
}
else
{
lean_object* v_v_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_v_419_ = lean_array_uget(v_bs_416_, v_i_415_);
v___x_420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_419_);
v___x_421_ = l_Lean_Syntax_isOfKind(v_v_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec(v_v_419_);
lean_dec_ref(v_bs_416_);
v___x_422_ = lean_box(0);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v_bs_x27_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_423_ = lean_unsigned_to_nat(0u);
v_bs_x27_424_ = lean_array_uset(v_bs_416_, v_i_415_, v___x_423_);
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_add(v_i_415_, v___x_425_);
v___x_427_ = lean_array_uset(v_bs_x27_424_, v_i_415_, v_v_419_);
v_i_415_ = v___x_426_;
v_bs_416_ = v___x_427_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_429_, lean_object* v_i_430_, lean_object* v_bs_431_){
_start:
{
size_t v_sz_boxed_432_; size_t v_i_boxed_433_; lean_object* v_res_434_; 
v_sz_boxed_432_ = lean_unbox_usize(v_sz_429_);
lean_dec(v_sz_429_);
v_i_boxed_433_ = lean_unbox_usize(v_i_430_);
lean_dec(v_i_430_);
v_res_434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_432_, v_i_boxed_433_, v_bs_431_);
return v_res_434_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_453_);
v___x_459_ = l_Lean_Syntax_isOfKind(v_kv_453_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_461_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_453_, v___x_460_, v_a_454_, v_a_455_, v_a_456_);
lean_dec_ref(v_a_454_);
lean_dec(v_kv_453_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = l_Lean_Syntax_getArg(v_kv_453_, v___x_462_);
v___x_464_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_463_);
v___x_465_ = l_Lean_Syntax_isOfKind(v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v_kv_453_);
v___x_466_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_467_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_463_, v___x_466_, v_a_454_, v_a_455_, v_a_456_);
lean_dec_ref(v_a_454_);
lean_dec(v___x_463_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v_v_469_; lean_object* v___y_471_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_468_ = lean_unsigned_to_nat(2u);
v_v_469_ = l_Lean_Syntax_getArg(v_kv_453_, v___x_468_);
lean_dec(v_kv_453_);
v___x_577_ = l_Lean_Syntax_getArg(v___x_463_, v___x_462_);
v___x_578_ = l_Lean_Syntax_getArgs(v___x_577_);
lean_dec(v___x_577_);
v___x_579_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_580_ = lean_array_get_size(v___x_578_);
v___x_581_ = lean_nat_dec_lt(v___x_462_, v___x_580_);
if (v___x_581_ == 0)
{
lean_dec_ref(v___x_578_);
v___y_471_ = v___x_579_;
goto v___jp_470_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; lean_object* v_snd_587_; 
v___x_582_ = lean_box(v___x_581_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_579_);
v___x_584_ = ((size_t)0ULL);
v___x_585_ = lean_usize_of_nat(v___x_580_);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_465_, v___x_578_, v___x_584_, v___x_585_, v___x_583_);
lean_dec_ref(v___x_578_);
v_snd_587_ = lean_ctor_get(v___x_586_, 1);
lean_inc(v_snd_587_);
lean_dec_ref(v___x_586_);
v___y_471_ = v_snd_587_;
goto v___jp_470_;
}
v___jp_470_:
{
size_t v_sz_472_; size_t v___x_473_; lean_object* v___x_474_; 
v_sz_472_ = lean_array_size(v___y_471_);
v___x_473_ = ((size_t)0ULL);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_472_, v___x_473_, v___y_471_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_v_469_);
v___x_475_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_476_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_463_, v___x_475_, v_a_454_, v_a_455_, v_a_456_);
lean_dec_ref(v_a_454_);
lean_dec(v___x_463_);
return v___x_476_;
}
else
{
lean_object* v_val_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_tailKeyStx_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_val_477_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_477_);
lean_dec_ref_known(v___x_474_, 1);
v___x_478_ = lean_box(0);
v___x_479_ = lean_array_get_size(v_val_477_);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_sub(v___x_479_, v___x_480_);
v_tailKeyStx_482_ = lean_array_get(v___x_478_, v_val_477_, v___x_481_);
lean_dec(v___x_481_);
v___x_483_ = lean_array_pop(v_val_477_);
v___x_484_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_483_, v_a_454_, v_a_455_, v_a_456_);
lean_dec_ref(v___x_483_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v_fst_486_; lean_object* v_snd_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_568_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v_fst_486_ = lean_ctor_get(v_a_485_, 0);
v_snd_487_ = lean_ctor_get(v_a_485_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_a_485_);
if (v_isSharedCheck_568_ == 0)
{
v___x_489_ = v_a_485_;
v_isShared_490_ = v_isSharedCheck_568_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_snd_487_);
lean_inc(v_fst_486_);
lean_dec(v_a_485_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_568_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; 
lean_inc(v_tailKeyStx_482_);
v___x_491_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_482_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v_keyTys_493_; lean_object* v_arrKeyTys_494_; lean_object* v_arrParents_495_; lean_object* v_currArrKey_496_; lean_object* v_currKey_497_; lean_object* v_items_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v_keyTys_493_ = lean_ctor_get(v_snd_487_, 0);
v_arrKeyTys_494_ = lean_ctor_get(v_snd_487_, 1);
v_arrParents_495_ = lean_ctor_get(v_snd_487_, 2);
v_currArrKey_496_ = lean_ctor_get(v_snd_487_, 3);
v_currKey_497_ = lean_ctor_get(v_snd_487_, 4);
v_items_498_ = lean_ctor_get(v_snd_487_, 5);
v___x_499_ = l_Lean_Name_str___override(v_fst_486_, v_a_492_);
v___x_500_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_493_, v___x_499_);
if (lean_obj_tag(v___x_500_) == 1)
{
lean_object* v_val_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_520_; 
lean_del_object(v___x_489_);
lean_dec(v_v_469_);
lean_dec(v___x_463_);
v_val_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_520_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_520_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_val_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_520_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; uint8_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_505_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_506_ = lean_unbox(v_val_501_);
lean_dec(v_val_501_);
v___x_507_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_506_);
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 3);
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_509_ = v___x_503_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_519_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_510_ = l_Lean_MessageData_ofFormat(v___x_509_);
v___x_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_505_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = l_Lean_MessageData_ofName(v___x_499_);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_482_, v___x_517_, v_snd_487_, v_a_455_, v_a_456_);
lean_dec(v_snd_487_);
lean_dec(v_tailKeyStx_482_);
return v___x_518_;
}
}
}
else
{
lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_553_; 
lean_inc_ref(v_items_498_);
lean_inc(v_currKey_497_);
lean_inc(v_currArrKey_496_);
lean_inc(v_arrParents_495_);
lean_inc(v_arrKeyTys_494_);
lean_inc(v_keyTys_493_);
lean_dec(v___x_500_);
lean_dec(v_tailKeyStx_482_);
v_isSharedCheck_553_ = !lean_is_exclusive(v_snd_487_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_554_ = lean_ctor_get(v_snd_487_, 5);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_snd_487_, 4);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_snd_487_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_snd_487_, 2);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_snd_487_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_snd_487_, 0);
lean_dec(v_unused_559_);
v___x_522_ = v_snd_487_;
v_isShared_523_ = v_isSharedCheck_553_;
goto v_resetjp_521_;
}
else
{
lean_dec(v_snd_487_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_553_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lake_Toml_elabVal(v_v_469_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_544_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_544_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_544_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_544_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_529_ = lean_box(0);
v___x_530_ = 0;
v___x_531_ = lean_box(v___x_530_);
lean_inc(v___x_499_);
v___x_532_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_499_, v___x_531_, v_keyTys_493_);
v___x_533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_533_, 0, v___x_463_);
lean_ctor_set(v___x_533_, 1, v___x_499_);
lean_ctor_set(v___x_533_, 2, v_a_525_);
v___x_534_ = lean_array_push(v_items_498_, v___x_533_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 5, v___x_534_);
lean_ctor_set(v___x_522_, 0, v___x_532_);
v___x_536_ = v___x_522_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_arrKeyTys_494_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_arrParents_495_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v_currArrKey_496_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v_currKey_497_);
lean_ctor_set(v_reuseFailAlloc_543_, 5, v___x_534_);
v___x_536_ = v_reuseFailAlloc_543_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_536_);
lean_ctor_set(v___x_489_, 0, v___x_529_);
v___x_538_ = v___x_489_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_542_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_538_);
v___x_540_ = v___x_527_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_del_object(v___x_522_);
lean_dec(v___x_499_);
lean_dec_ref(v_items_498_);
lean_dec(v_currKey_497_);
lean_dec(v_currArrKey_496_);
lean_dec(v_arrParents_495_);
lean_dec(v_arrKeyTys_494_);
lean_dec(v_keyTys_493_);
lean_del_object(v___x_489_);
lean_dec(v___x_463_);
v_a_545_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_524_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_524_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_del_object(v___x_489_);
lean_dec(v_snd_487_);
lean_dec(v_fst_486_);
lean_dec(v_tailKeyStx_482_);
lean_dec(v_v_469_);
lean_dec(v___x_463_);
v_a_560_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_491_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_491_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_tailKeyStx_482_);
lean_dec(v_v_469_);
lean_dec(v___x_463_);
v_a_569_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_484_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_484_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_593_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_596_ = l_Lean_stringToMessageData(v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_597_, size_t v_i_598_, size_t v_stop_599_, lean_object* v_b_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_fst_606_; lean_object* v_snd_607_; uint8_t v___x_611_; 
v___x_611_ = lean_usize_dec_eq(v_i_598_, v_stop_599_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_array_uget_borrowed(v_as_597_, v_i_598_);
lean_inc(v___x_612_);
v___x_613_ = l_Lake_Toml_elabSimpleKey(v___x_612_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v_keyTys_615_; lean_object* v_arrKeyTys_616_; lean_object* v_arrParents_617_; lean_object* v_currArrKey_618_; lean_object* v_currKey_619_; lean_object* v_items_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v_keyTys_615_ = lean_ctor_get(v___y_601_, 0);
v_arrKeyTys_616_ = lean_ctor_get(v___y_601_, 1);
v_arrParents_617_ = lean_ctor_get(v___y_601_, 2);
v_currArrKey_618_ = lean_ctor_get(v___y_601_, 3);
v_currKey_619_ = lean_ctor_get(v___y_601_, 4);
v_items_620_ = lean_ctor_get(v___y_601_, 5);
v___x_621_ = l_Lean_Name_str___override(v_b_600_, v_a_614_);
v___x_622_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_615_, v___x_621_);
if (lean_obj_tag(v___x_622_) == 1)
{
lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_684_; 
v_val_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_684_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_684_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_684_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; 
v___x_627_ = lean_unbox(v_val_623_);
switch(v___x_627_)
{
case 2:
{
lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_652_; 
lean_inc_ref(v_items_620_);
lean_inc(v_currKey_619_);
lean_inc(v_arrParents_617_);
lean_inc(v_arrKeyTys_616_);
lean_del_object(v___x_625_);
lean_dec(v_val_623_);
v_isSharedCheck_652_ = !lean_is_exclusive(v___y_601_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; lean_object* v_unused_657_; lean_object* v_unused_658_; 
v_unused_653_ = lean_ctor_get(v___y_601_, 5);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v___y_601_, 4);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v___y_601_, 3);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v___y_601_, 2);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v___y_601_, 1);
lean_dec(v_unused_657_);
v_unused_658_ = lean_ctor_get(v___y_601_, 0);
lean_dec(v_unused_658_);
v___x_629_ = v___y_601_;
v_isShared_630_ = v_isSharedCheck_652_;
goto v_resetjp_628_;
}
else
{
lean_dec(v___y_601_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_652_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_616_, v___x_621_);
if (lean_obj_tag(v___x_631_) == 1)
{
lean_object* v_val_632_; lean_object* v___x_634_; 
v_val_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v___x_631_, 1);
lean_inc(v___x_621_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 3, v___x_621_);
lean_ctor_set(v___x_629_, 0, v_val_632_);
v___x_634_ = v___x_629_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_val_632_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_arrKeyTys_616_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_arrParents_617_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_currKey_619_);
lean_ctor_set(v_reuseFailAlloc_635_, 5, v_items_620_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
v_fst_606_ = v___x_621_;
v_snd_607_ = v___x_634_;
goto v___jp_605_;
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v___x_631_);
lean_del_object(v___x_629_);
lean_dec_ref(v_items_620_);
lean_dec(v_currKey_619_);
lean_dec(v_arrParents_617_);
lean_dec(v_arrKeyTys_616_);
v___x_636_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_621_);
v___x_637_ = l_Lean_MessageData_ofName(v___x_621_);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_640_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v_snd_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v_snd_643_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_snd_643_);
lean_dec(v_a_642_);
v_fst_606_ = v___x_621_;
v_snd_607_ = v_snd_643_;
goto v___jp_605_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v___x_621_);
v_a_644_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_641_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
case 1:
{
lean_del_object(v___x_625_);
lean_dec(v_val_623_);
v_fst_606_ = v___x_621_;
v_snd_607_ = v___y_601_;
goto v___jp_605_;
}
case 4:
{
lean_del_object(v___x_625_);
lean_dec(v_val_623_);
v_fst_606_ = v___x_621_;
v_snd_607_ = v___y_601_;
goto v___jp_605_;
}
case 3:
{
lean_del_object(v___x_625_);
lean_dec(v_val_623_);
v_fst_606_ = v___x_621_;
v_snd_607_ = v___y_601_;
goto v___jp_605_;
}
default: 
{
lean_object* v___x_659_; uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_660_ = lean_unbox(v_val_623_);
lean_dec(v_val_623_);
v___x_661_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_660_);
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 3);
lean_ctor_set(v___x_625_, 0, v___x_661_);
v___x_663_ = v___x_625_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_683_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_664_ = l_Lean_MessageData_ofFormat(v___x_663_);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_659_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
lean_inc(v___x_621_);
v___x_668_ = l_Lean_MessageData_ofName(v___x_621_);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_612_, v___x_671_, v___y_601_, v___y_602_, v___y_603_);
lean_dec_ref(v___y_601_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v_snd_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v_snd_674_ = lean_ctor_get(v_a_673_, 1);
lean_inc(v_snd_674_);
lean_dec(v_a_673_);
v_fst_606_ = v___x_621_;
v_snd_607_ = v_snd_674_;
goto v___jp_605_;
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec(v___x_621_);
v_a_675_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_672_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
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
lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_694_; 
lean_inc_ref(v_items_620_);
lean_inc(v_currKey_619_);
lean_inc(v_currArrKey_618_);
lean_inc(v_arrParents_617_);
lean_inc(v_arrKeyTys_616_);
lean_inc(v_keyTys_615_);
lean_dec(v___x_622_);
v_isSharedCheck_694_ = !lean_is_exclusive(v___y_601_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_695_ = lean_ctor_get(v___y_601_, 5);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v___y_601_, 4);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v___y_601_, 3);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v___y_601_, 2);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v___y_601_, 1);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v___y_601_, 0);
lean_dec(v_unused_700_);
v___x_686_ = v___y_601_;
v_isShared_687_ = v_isSharedCheck_694_;
goto v_resetjp_685_;
}
else
{
lean_dec(v___y_601_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_694_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_688_ = 4;
v___x_689_ = lean_box(v___x_688_);
lean_inc(v___x_621_);
v___x_690_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_621_, v___x_689_, v_keyTys_615_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_690_);
v___x_692_ = v___x_686_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_arrKeyTys_616_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_arrParents_617_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_currArrKey_618_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_currKey_619_);
lean_ctor_set(v_reuseFailAlloc_693_, 5, v_items_620_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v_fst_606_ = v___x_621_;
v_snd_607_ = v___x_692_;
goto v___jp_605_;
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v___y_601_);
lean_dec(v_b_600_);
v_a_701_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_613_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_613_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_b_600_);
lean_ctor_set(v___x_709_, 1, v___y_601_);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
v___jp_605_:
{
size_t v___x_608_; size_t v___x_609_; 
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_i_598_, v___x_608_);
v_i_598_ = v___x_609_;
v_b_600_ = v_fst_606_;
v___y_601_ = v_snd_607_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_711_, lean_object* v_i_712_, lean_object* v_stop_713_, lean_object* v_b_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
size_t v_i_boxed_719_; size_t v_stop_boxed_720_; lean_object* v_res_721_; 
v_i_boxed_719_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_stop_boxed_720_ = lean_unbox_usize(v_stop_713_);
lean_dec(v_stop_713_);
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_711_, v_i_boxed_719_, v_stop_boxed_720_, v_b_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_as_711_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_722_, lean_object* v_k_723_){
_start:
{
if (lean_obj_tag(v_t_722_) == 0)
{
lean_object* v_k_724_; lean_object* v_v_725_; lean_object* v_l_726_; lean_object* v_r_727_; uint8_t v___x_728_; 
v_k_724_ = lean_ctor_get(v_t_722_, 1);
v_v_725_ = lean_ctor_get(v_t_722_, 2);
v_l_726_ = lean_ctor_get(v_t_722_, 3);
v_r_727_ = lean_ctor_get(v_t_722_, 4);
v___x_728_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_723_, v_k_724_);
switch(v___x_728_)
{
case 0:
{
v_t_722_ = v_l_726_;
goto _start;
}
case 1:
{
lean_object* v___x_730_; 
lean_inc(v_v_725_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_v_725_);
return v___x_730_;
}
default: 
{
v_t_722_ = v_r_727_;
goto _start;
}
}
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_733_, lean_object* v_k_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_733_, v_k_734_);
lean_dec(v_k_734_);
lean_dec(v_t_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_keyTys_741_; lean_object* v_arrKeyTys_742_; lean_object* v_arrParents_743_; lean_object* v_currArrKey_744_; lean_object* v_currKey_745_; lean_object* v_items_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_774_; 
v_keyTys_741_ = lean_ctor_get(v_a_737_, 0);
v_arrKeyTys_742_ = lean_ctor_get(v_a_737_, 1);
v_arrParents_743_ = lean_ctor_get(v_a_737_, 2);
v_currArrKey_744_ = lean_ctor_get(v_a_737_, 3);
v_currKey_745_ = lean_ctor_get(v_a_737_, 4);
v_items_746_ = lean_ctor_get(v_a_737_, 5);
v_isSharedCheck_774_ = !lean_is_exclusive(v_a_737_);
if (v_isSharedCheck_774_ == 0)
{
v___x_748_ = v_a_737_;
v_isShared_749_ = v_isSharedCheck_774_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_items_746_);
lean_inc(v_currKey_745_);
lean_inc(v_currArrKey_744_);
lean_inc(v_arrParents_743_);
lean_inc(v_arrKeyTys_742_);
lean_inc(v_keyTys_741_);
lean_dec(v_a_737_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_774_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_arrKeyTys_750_; lean_object* v___x_751_; lean_object* v___y_753_; lean_object* v___x_771_; 
v_arrKeyTys_750_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_744_, v_keyTys_741_, v_arrKeyTys_742_);
v___x_751_ = lean_box(0);
v___x_771_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_750_, v___x_751_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_772_; 
v___x_772_ = lean_box(1);
v___y_753_ = v___x_772_;
goto v___jp_752_;
}
else
{
lean_object* v_val_773_; 
v_val_773_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v___x_771_, 1);
v___y_753_ = v_val_773_;
goto v___jp_752_;
}
v___jp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 3, v___x_751_);
lean_ctor_set(v___x_748_, 1, v_arrKeyTys_750_);
lean_ctor_set(v___x_748_, 0, v___y_753_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___y_753_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_arrKeyTys_750_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_arrParents_743_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_currKey_745_);
lean_ctor_set(v_reuseFailAlloc_770_, 5, v_items_746_);
v___x_755_ = v_reuseFailAlloc_770_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_array_get_size(v_ks_736_);
v___x_758_ = lean_nat_dec_lt(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_751_);
lean_ctor_set(v___x_759_, 1, v___x_755_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = lean_nat_dec_le(v___x_757_, v___x_757_);
if (v___x_761_ == 0)
{
if (v___x_758_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_751_);
lean_ctor_set(v___x_762_, 1, v___x_755_);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
else
{
size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_of_nat(v___x_757_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_736_, v___x_764_, v___x_765_, v___x_751_, v___x_755_, v_a_738_, v_a_739_);
return v___x_766_;
}
}
else
{
size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((size_t)0ULL);
v___x_768_ = lean_usize_of_nat(v___x_757_);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_736_, v___x_767_, v___x_768_, v___x_751_, v___x_755_, v_a_738_, v_a_739_);
return v___x_769_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec_ref(v_ks_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_781_, lean_object* v_t_782_, lean_object* v_k_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_782_, v_k_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_785_, lean_object* v_t_786_, lean_object* v_k_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_785_, v_t_786_, v_k_787_);
lean_dec(v_k_787_);
lean_dec(v_t_786_);
return v_res_788_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0(void){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_789_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___y_804_; lean_object* v_keyTys_805_; lean_object* v_arrKeyTys_806_; lean_object* v_arrParents_807_; lean_object* v_currArrKey_808_; lean_object* v_items_809_; lean_object* v_toCold_821_; lean_object* v_currRecDepth_822_; lean_object* v_ref_823_; uint16_t v_optionFlags_824_; uint8_t v_suppressElabErrors_825_; uint8_t v_isRecordingDeps_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v_ref_829_; lean_object* v___x_830_; 
v_toCold_821_ = lean_ctor_get(v_a_800_, 0);
v_currRecDepth_822_ = lean_ctor_get(v_a_800_, 1);
v_ref_823_ = lean_ctor_get(v_a_800_, 2);
v_optionFlags_824_ = lean_ctor_get_uint16(v_a_800_, sizeof(void*)*3);
v_suppressElabErrors_825_ = lean_ctor_get_uint8(v_a_800_, sizeof(void*)*3 + 2);
v_isRecordingDeps_826_ = lean_ctor_get_uint8(v_a_800_, sizeof(void*)*3 + 3);
v___x_827_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_798_);
v___x_828_ = l_Lean_Syntax_isOfKind(v_x_798_, v___x_827_);
v_ref_829_ = l_Lean_replaceRef(v_x_798_, v_ref_823_);
lean_inc(v_currRecDepth_822_);
lean_inc_ref(v_toCold_821_);
v___x_830_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_830_, 0, v_toCold_821_);
lean_ctor_set(v___x_830_, 1, v_currRecDepth_822_);
lean_ctor_set(v___x_830_, 2, v_ref_829_);
lean_ctor_set_uint16(v___x_830_, sizeof(void*)*3, v_optionFlags_824_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*3 + 2, v_suppressElabErrors_825_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*3 + 3, v_isRecordingDeps_826_);
if (v___x_828_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4);
v___x_832_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_798_, v___x_831_, v_a_799_, v___x_830_, v_a_801_);
lean_dec_ref_known(v___x_830_, 3);
lean_dec_ref(v_a_799_);
lean_dec(v_x_798_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___y_836_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = l_Lean_Syntax_getArg(v_x_798_, v___x_833_);
v___x_904_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_834_);
v___x_905_ = l_Lean_Syntax_isOfKind(v___x_834_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec(v_x_798_);
v___x_906_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_907_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_834_, v___x_906_, v_a_799_, v___x_830_, v_a_801_);
lean_dec_ref_known(v___x_830_, 3);
lean_dec_ref(v_a_799_);
lean_dec(v___x_834_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = l_Lean_Syntax_getArg(v___x_834_, v___x_908_);
v___x_910_ = l_Lean_Syntax_getArgs(v___x_909_);
lean_dec(v___x_909_);
v___x_911_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_912_ = lean_array_get_size(v___x_910_);
v___x_913_ = lean_nat_dec_lt(v___x_908_, v___x_912_);
if (v___x_913_ == 0)
{
lean_dec_ref(v___x_910_);
v___y_836_ = v___x_911_;
goto v___jp_835_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; lean_object* v_snd_919_; 
v___x_914_ = lean_box(v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_911_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = lean_usize_of_nat(v___x_912_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_905_, v___x_910_, v___x_916_, v___x_917_, v___x_915_);
lean_dec_ref(v___x_910_);
v_snd_919_ = lean_ctor_get(v___x_918_, 1);
lean_inc(v_snd_919_);
lean_dec_ref(v___x_918_);
v___y_836_ = v_snd_919_;
goto v___jp_835_;
}
}
v___jp_835_:
{
size_t v_sz_837_; size_t v___x_838_; lean_object* v___x_839_; 
v_sz_837_ = lean_array_size(v___y_836_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_837_, v___x_838_, v___y_836_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v_x_798_);
v___x_840_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_841_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_834_, v___x_840_, v_a_799_, v___x_830_, v_a_801_);
lean_dec_ref_known(v___x_830_, 3);
lean_dec_ref(v_a_799_);
lean_dec(v___x_834_);
return v___x_841_;
}
else
{
lean_object* v_val_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_tailKey_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v___x_834_);
v_val_842_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_val_842_);
lean_dec_ref_known(v___x_839_, 1);
v___x_843_ = lean_box(0);
v___x_844_ = lean_array_get_size(v_val_842_);
v___x_845_ = lean_nat_sub(v___x_844_, v___x_833_);
v_tailKey_846_ = lean_array_get(v___x_843_, v_val_842_, v___x_845_);
lean_dec(v___x_845_);
v___x_847_ = lean_array_pop(v_val_842_);
v___x_848_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_847_, v_a_799_, v___x_830_, v_a_801_);
lean_dec_ref(v___x_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v_fst_850_; lean_object* v_snd_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_895_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v_fst_850_ = lean_ctor_get(v_a_849_, 0);
v_snd_851_ = lean_ctor_get(v_a_849_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_849_);
if (v_isSharedCheck_895_ == 0)
{
v___x_853_ = v_a_849_;
v_isShared_854_ = v_isSharedCheck_895_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_snd_851_);
lean_inc(v_fst_850_);
lean_dec(v_a_849_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_895_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; 
lean_inc(v_tailKey_846_);
v___x_855_ = l_Lake_Toml_elabSimpleKey(v_tailKey_846_, v___x_830_, v_a_801_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v_keyTys_857_; lean_object* v_arrKeyTys_858_; lean_object* v_arrParents_859_; lean_object* v_currArrKey_860_; lean_object* v_items_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v_keyTys_857_ = lean_ctor_get(v_snd_851_, 0);
v_arrKeyTys_858_ = lean_ctor_get(v_snd_851_, 1);
v_arrParents_859_ = lean_ctor_get(v_snd_851_, 2);
v_currArrKey_860_ = lean_ctor_get(v_snd_851_, 3);
v_items_861_ = lean_ctor_get(v_snd_851_, 5);
v___x_862_ = l_Lean_Name_str___override(v_fst_850_, v_a_856_);
v___x_863_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_857_, v___x_862_);
if (lean_obj_tag(v___x_863_) == 1)
{
lean_object* v_val_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_886_; 
v_val_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_886_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_886_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_val_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_886_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___x_868_; 
v___x_868_ = lean_unbox(v_val_864_);
if (v___x_868_ == 4)
{
lean_inc_ref(v_items_861_);
lean_inc(v_currArrKey_860_);
lean_inc(v_arrParents_859_);
lean_inc(v_arrKeyTys_858_);
lean_inc(v_keyTys_857_);
lean_del_object(v___x_866_);
lean_dec(v_val_864_);
lean_del_object(v___x_853_);
lean_dec(v_snd_851_);
lean_dec(v_tailKey_846_);
lean_dec_ref_known(v___x_830_, 3);
v___y_804_ = v___x_862_;
v_keyTys_805_ = v_keyTys_857_;
v_arrKeyTys_806_ = v_arrKeyTys_858_;
v_arrParents_807_ = v_arrParents_859_;
v_currArrKey_808_ = v_currArrKey_860_;
v_items_809_ = v_items_861_;
goto v___jp_803_;
}
else
{
lean_object* v___x_869_; uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
lean_dec(v_x_798_);
v___x_869_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_870_ = lean_unbox(v_val_864_);
lean_dec(v_val_864_);
v___x_871_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_870_);
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 3);
lean_ctor_set(v___x_866_, 0, v___x_871_);
v___x_873_ = v___x_866_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_885_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = l_Lean_MessageData_ofFormat(v___x_873_);
if (v_isShared_854_ == 0)
{
lean_ctor_set_tag(v___x_853_, 7);
lean_ctor_set(v___x_853_, 1, v___x_874_);
lean_ctor_set(v___x_853_, 0, v___x_869_);
v___x_876_ = v___x_853_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_884_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_877_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_MessageData_ofName(v___x_862_);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_846_, v___x_882_, v_snd_851_, v___x_830_, v_a_801_);
lean_dec_ref_known(v___x_830_, 3);
lean_dec(v_snd_851_);
lean_dec(v_tailKey_846_);
return v___x_883_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_861_);
lean_inc(v_currArrKey_860_);
lean_inc(v_arrParents_859_);
lean_inc(v_arrKeyTys_858_);
lean_inc(v_keyTys_857_);
lean_dec(v___x_863_);
lean_del_object(v___x_853_);
lean_dec(v_snd_851_);
lean_dec(v_tailKey_846_);
lean_dec_ref_known(v___x_830_, 3);
v___y_804_ = v___x_862_;
v_keyTys_805_ = v_keyTys_857_;
v_arrKeyTys_806_ = v_arrKeyTys_858_;
v_arrParents_807_ = v_arrParents_859_;
v_currArrKey_808_ = v_currArrKey_860_;
v_items_809_ = v_items_861_;
goto v___jp_803_;
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_del_object(v___x_853_);
lean_dec(v_snd_851_);
lean_dec(v_fst_850_);
lean_dec(v_tailKey_846_);
lean_dec_ref_known(v___x_830_, 3);
lean_dec(v_x_798_);
v_a_887_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_855_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_855_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_tailKey_846_);
lean_dec_ref_known(v___x_830_, 3);
lean_dec(v_x_798_);
v_a_896_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_848_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_848_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
v___jp_803_:
{
lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_810_ = lean_box(0);
v___x_811_ = 1;
v___x_812_ = lean_box(v___x_811_);
lean_inc_n(v___y_804_, 2);
v___x_813_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_804_, v___x_812_, v_keyTys_805_);
v___x_814_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_x_798_);
v___x_815_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_815_, 0, v_x_798_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_816_, 0, v_x_798_);
lean_ctor_set(v___x_816_, 1, v___y_804_);
lean_ctor_set(v___x_816_, 2, v___x_815_);
v___x_817_ = lean_array_push(v_items_809_, v___x_816_);
v___x_818_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_818_, 0, v___x_813_);
lean_ctor_set(v___x_818_, 1, v_arrKeyTys_806_);
lean_ctor_set(v___x_818_, 2, v_arrParents_807_);
lean_ctor_set(v___x_818_, 3, v_currArrKey_808_);
lean_ctor_set(v___x_818_, 4, v___y_804_);
lean_ctor_set(v___x_818_, 5, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_810_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_920_, v_a_921_, v_a_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_925_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_toCold_939_; lean_object* v_currRecDepth_940_; lean_object* v_ref_941_; uint16_t v_optionFlags_942_; uint8_t v_suppressElabErrors_943_; uint8_t v_isRecordingDeps_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v_ref_947_; lean_object* v___x_948_; lean_object* v___y_950_; 
v_toCold_939_ = lean_ctor_get(v_a_936_, 0);
v_currRecDepth_940_ = lean_ctor_get(v_a_936_, 1);
v_ref_941_ = lean_ctor_get(v_a_936_, 2);
v_optionFlags_942_ = lean_ctor_get_uint16(v_a_936_, sizeof(void*)*3);
v_suppressElabErrors_943_ = lean_ctor_get_uint8(v_a_936_, sizeof(void*)*3 + 2);
v_isRecordingDeps_944_ = lean_ctor_get_uint8(v_a_936_, sizeof(void*)*3 + 3);
v___x_945_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_934_);
v___x_946_ = l_Lean_Syntax_isOfKind(v_x_934_, v___x_945_);
v_ref_947_ = l_Lean_replaceRef(v_x_934_, v_ref_941_);
lean_inc(v_currRecDepth_940_);
lean_inc_ref(v_toCold_939_);
v___x_948_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_948_, 0, v_toCold_939_);
lean_ctor_set(v___x_948_, 1, v_currRecDepth_940_);
lean_ctor_set(v___x_948_, 2, v_ref_947_);
lean_ctor_set_uint16(v___x_948_, sizeof(void*)*3, v_optionFlags_942_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*3 + 2, v_suppressElabErrors_943_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*3 + 3, v_isRecordingDeps_944_);
if (v___x_946_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_958_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_934_, v___x_957_, v_a_935_, v___x_948_, v_a_937_);
lean_dec_ref_known(v___x_948_, 3);
lean_dec_ref(v_a_935_);
lean_dec(v_x_934_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___y_964_; 
v___x_959_ = lean_unsigned_to_nat(2u);
v___x_960_ = l_Lean_Syntax_getArg(v_x_934_, v___x_959_);
v___x_961_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_960_);
v___x_962_ = l_Lean_Syntax_isOfKind(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v___x_960_);
v___x_1098_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1099_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_934_, v___x_1098_, v_a_935_, v___x_948_, v_a_937_);
lean_dec_ref_known(v___x_948_, 3);
lean_dec_ref(v_a_935_);
lean_dec(v_x_934_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = l_Lean_Syntax_getArg(v___x_960_, v___x_1100_);
lean_dec(v___x_960_);
v___x_1102_ = l_Lean_Syntax_getArgs(v___x_1101_);
lean_dec(v___x_1101_);
v___x_1103_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1104_ = lean_array_get_size(v___x_1102_);
v___x_1105_ = lean_nat_dec_lt(v___x_1100_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v___x_1102_);
v___y_964_ = v___x_1103_;
goto v___jp_963_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v_snd_1111_; 
v___x_1106_ = lean_box(v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1103_);
v___x_1108_ = ((size_t)0ULL);
v___x_1109_ = lean_usize_of_nat(v___x_1104_);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_962_, v___x_1102_, v___x_1108_, v___x_1109_, v___x_1107_);
lean_dec_ref(v___x_1102_);
v_snd_1111_ = lean_ctor_get(v___x_1110_, 1);
lean_inc(v_snd_1111_);
lean_dec_ref(v___x_1110_);
v___y_964_ = v_snd_1111_;
goto v___jp_963_;
}
}
v___jp_963_:
{
size_t v_sz_965_; size_t v___x_966_; lean_object* v___x_967_; 
v_sz_965_ = lean_array_size(v___y_964_);
v___x_966_ = ((size_t)0ULL);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_965_, v___x_966_, v___y_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_969_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_934_, v___x_968_, v_a_935_, v___x_948_, v_a_937_);
lean_dec_ref_known(v___x_948_, 3);
lean_dec_ref(v_a_935_);
lean_dec(v_x_934_);
return v___x_969_;
}
else
{
lean_object* v_val_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_tailKey_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_val_970_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_val_970_);
lean_dec_ref_known(v___x_967_, 1);
v___x_971_ = lean_box(0);
v___x_972_ = lean_array_get_size(v_val_970_);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_sub(v___x_972_, v___x_973_);
v_tailKey_975_ = lean_array_get(v___x_971_, v_val_970_, v___x_974_);
lean_dec(v___x_974_);
v___x_976_ = lean_array_pop(v_val_970_);
v___x_977_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_976_, v_a_935_, v___x_948_, v_a_937_);
lean_dec_ref(v___x_976_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1089_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v_fst_979_ = lean_ctor_get(v_a_978_, 0);
v_snd_980_ = lean_ctor_get(v_a_978_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_a_978_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_982_ = v_a_978_;
v_isShared_983_ = v_isSharedCheck_1089_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_snd_980_);
lean_inc(v_fst_979_);
lean_dec(v_a_978_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1089_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; 
lean_inc(v_tailKey_975_);
v___x_984_ = l_Lake_Toml_elabSimpleKey(v_tailKey_975_, v___x_948_, v_a_937_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1080_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_1080_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1080_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_keyTys_989_; lean_object* v_arrKeyTys_990_; lean_object* v_arrParents_991_; lean_object* v_currArrKey_992_; lean_object* v_items_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_keyTys_989_ = lean_ctor_get(v_snd_980_, 0);
v_arrKeyTys_990_ = lean_ctor_get(v_snd_980_, 1);
v_arrParents_991_ = lean_ctor_get(v_snd_980_, 2);
v_currArrKey_992_ = lean_ctor_get(v_snd_980_, 3);
v_items_993_ = lean_ctor_get(v_snd_980_, 5);
v___x_994_ = l_Lean_Name_str___override(v_fst_979_, v_a_985_);
v___x_995_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_989_, v___x_994_);
if (lean_obj_tag(v___x_995_) == 1)
{
lean_object* v_val_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1047_; 
v_val_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1047_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_val_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1047_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_unbox(v_val_996_);
if (v___x_1000_ == 2)
{
lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1025_; 
lean_inc_ref(v_items_993_);
lean_inc(v_arrParents_991_);
lean_inc(v_arrKeyTys_990_);
lean_del_object(v___x_998_);
lean_dec(v_val_996_);
lean_dec(v_tailKey_975_);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_snd_980_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; lean_object* v_unused_1027_; lean_object* v_unused_1028_; lean_object* v_unused_1029_; lean_object* v_unused_1030_; lean_object* v_unused_1031_; 
v_unused_1026_ = lean_ctor_get(v_snd_980_, 5);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_snd_980_, 4);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_snd_980_, 3);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_snd_980_, 2);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_snd_980_, 1);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_snd_980_, 0);
lean_dec(v_unused_1031_);
v___x_1002_ = v_snd_980_;
v_isShared_1003_ = v_isSharedCheck_1025_;
goto v_resetjp_1001_;
}
else
{
lean_dec(v_snd_980_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1025_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_991_, v___x_994_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_del_object(v___x_1002_);
lean_dec_ref(v_items_993_);
lean_dec(v_arrParents_991_);
lean_dec(v_arrKeyTys_990_);
lean_del_object(v___x_987_);
lean_del_object(v___x_982_);
lean_dec(v_x_934_);
v___y_950_ = v___x_994_;
goto v___jp_949_;
}
else
{
lean_object* v_val_1005_; lean_object* v___x_1006_; 
v_val_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_990_, v_val_1005_);
lean_dec(v_val_1005_);
if (lean_obj_tag(v___x_1006_) == 1)
{
lean_object* v_val_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
lean_dec_ref_known(v___x_948_, 3);
v_val_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_934_, 2);
v___x_1010_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_x_934_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_973_);
v___x_1012_ = lean_array_push(v___x_1011_, v___x_1010_);
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_x_934_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
lean_inc_n(v___x_994_, 2);
v___x_1014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1014_, 0, v_x_934_);
lean_ctor_set(v___x_1014_, 1, v___x_994_);
lean_ctor_set(v___x_1014_, 2, v___x_1013_);
v___x_1015_ = lean_array_push(v_items_993_, v___x_1014_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 5, v___x_1015_);
lean_ctor_set(v___x_1002_, 4, v___x_994_);
lean_ctor_set(v___x_1002_, 3, v___x_994_);
lean_ctor_set(v___x_1002_, 0, v_val_1007_);
v___x_1017_ = v___x_1002_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_val_1007_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_arrKeyTys_990_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_arrParents_991_);
lean_ctor_set(v_reuseFailAlloc_1024_, 3, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1024_, 4, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1024_, 5, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_1017_);
lean_ctor_set(v___x_982_, 0, v___x_1008_);
v___x_1019_ = v___x_982_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_1019_);
v___x_1021_ = v___x_987_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_dec(v___x_1006_);
lean_del_object(v___x_1002_);
lean_dec_ref(v_items_993_);
lean_dec(v_arrParents_991_);
lean_dec(v_arrKeyTys_990_);
lean_del_object(v___x_987_);
lean_del_object(v___x_982_);
lean_dec(v_x_934_);
v___y_950_ = v___x_994_;
goto v___jp_949_;
}
}
}
}
else
{
lean_object* v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_del_object(v___x_987_);
lean_del_object(v___x_982_);
lean_dec(v_x_934_);
v___x_1032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1033_ = lean_unbox(v_val_996_);
lean_dec(v_val_996_);
v___x_1034_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1033_);
v___x_1035_ = lean_string_append(v___x_1032_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1037_ = lean_string_append(v___x_1035_, v___x_1036_);
v___x_1038_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_994_, v___x_962_);
v___x_1039_ = lean_string_append(v___x_1037_, v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
if (v_isShared_999_ == 0)
{
lean_ctor_set_tag(v___x_998_, 3);
lean_ctor_set(v___x_998_, 0, v___x_1041_);
v___x_1043_ = v___x_998_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = l_Lean_MessageData_ofFormat(v___x_1043_);
v___x_1045_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_975_, v___x_1044_, v_snd_980_, v___x_948_, v_a_937_);
lean_dec_ref_known(v___x_948_, 3);
lean_dec(v_snd_980_);
lean_dec(v_tailKey_975_);
return v___x_1045_;
}
}
}
}
else
{
lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1073_; 
lean_inc_ref(v_items_993_);
lean_inc(v_currArrKey_992_);
lean_inc(v_arrParents_991_);
lean_inc(v_arrKeyTys_990_);
lean_inc(v_keyTys_989_);
lean_dec(v___x_995_);
lean_dec(v_tailKey_975_);
lean_dec_ref_known(v___x_948_, 3);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_snd_980_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; lean_object* v_unused_1079_; 
v_unused_1074_ = lean_ctor_get(v_snd_980_, 5);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_snd_980_, 4);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_snd_980_, 3);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_snd_980_, 2);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_snd_980_, 1);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_snd_980_, 0);
lean_dec(v_unused_1079_);
v___x_1049_ = v_snd_980_;
v_isShared_1050_ = v_isSharedCheck_1073_;
goto v_resetjp_1048_;
}
else
{
lean_dec(v_snd_980_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1073_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = 2;
v___x_1053_ = lean_box(v___x_1052_);
lean_inc_n(v___x_994_, 4);
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_994_, v___x_1053_, v_keyTys_989_);
lean_inc(v___x_1054_);
lean_inc(v_currArrKey_992_);
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_992_, v___x_1054_, v_arrKeyTys_990_);
v___x_1056_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_994_, v_currArrKey_992_, v_arrParents_991_);
v___x_1057_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_934_, 2);
v___x_1058_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_x_934_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_mk_empty_array_with_capacity(v___x_973_);
v___x_1060_ = lean_array_push(v___x_1059_, v___x_1058_);
v___x_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_x_934_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1062_, 0, v_x_934_);
lean_ctor_set(v___x_1062_, 1, v___x_994_);
lean_ctor_set(v___x_1062_, 2, v___x_1061_);
v___x_1063_ = lean_array_push(v_items_993_, v___x_1062_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 5, v___x_1063_);
lean_ctor_set(v___x_1049_, 4, v___x_994_);
lean_ctor_set(v___x_1049_, 3, v___x_994_);
lean_ctor_set(v___x_1049_, 2, v___x_1056_);
lean_ctor_set(v___x_1049_, 1, v___x_1055_);
lean_ctor_set(v___x_1049_, 0, v___x_1054_);
v___x_1065_ = v___x_1049_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1072_, 5, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_1065_);
lean_ctor_set(v___x_982_, 0, v___x_1051_);
v___x_1067_ = v___x_982_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_1067_);
v___x_1069_ = v___x_987_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_del_object(v___x_982_);
lean_dec(v_snd_980_);
lean_dec(v_fst_979_);
lean_dec(v_tailKey_975_);
lean_dec_ref_known(v___x_948_, 3);
lean_dec(v_x_934_);
v_a_1081_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_984_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_984_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_tailKey_975_);
lean_dec_ref_known(v___x_948_, 3);
lean_dec(v_x_934_);
v_a_1090_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_977_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_977_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
v___jp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_951_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_952_ = l_Lean_MessageData_ofName(v___y_950_);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_955_, v___x_948_, v_a_937_);
lean_dec_ref_known(v___x_948_, 3);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
return v_res_1117_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1120_ = l_Lean_stringToMessageData(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1121_);
v___x_1127_ = l_Lean_Syntax_isOfKind(v_x_1121_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_1121_);
v___x_1129_ = l_Lean_Syntax_isOfKind(v_x_1121_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1121_);
v___x_1131_ = l_Lean_Syntax_isOfKind(v_x_1121_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1133_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1121_, v___x_1132_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec_ref(v_a_1122_);
lean_dec(v_x_1121_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1134_;
}
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1135_;
}
}
else
{
lean_object* v___x_1136_; 
v___x_1136_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1144_, lean_object* v_as_1145_, size_t v_i_1146_, size_t v_stop_1147_, lean_object* v_b_1148_){
_start:
{
lean_object* v___y_1150_; uint8_t v___x_1154_; 
v___x_1154_ = lean_usize_dec_eq(v_i_1146_, v_stop_1147_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_array_uget_borrowed(v_as_1145_, v_i_1146_);
v_fst_1156_ = lean_ctor_get(v___x_1155_, 0);
v_snd_1157_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_fst_1156_);
v___x_1158_ = l_Lean_Name_components(v_fst_1156_);
if (lean_obj_tag(v___x_1158_) == 0)
{
v___y_1150_ = v_b_1148_;
goto v___jp_1149_;
}
else
{
lean_object* v_head_1159_; lean_object* v_tail_1160_; lean_object* v___x_1161_; 
v_head_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_head_1159_);
v_tail_1160_ = lean_ctor_get(v___x_1158_, 1);
lean_inc(v_tail_1160_);
lean_dec_ref_known(v___x_1158_, 2);
lean_inc(v_snd_1157_);
lean_inc(v_ref_1144_);
v___x_1161_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1148_, v_ref_1144_, v_head_1159_, v_tail_1160_, v_snd_1157_);
v___y_1150_ = v___x_1161_;
goto v___jp_1149_;
}
}
else
{
lean_dec(v_ref_1144_);
return v_b_1148_;
}
v___jp_1149_:
{
size_t v___x_1151_; size_t v___x_1152_; 
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_add(v_i_1146_, v___x_1151_);
v_i_1146_ = v___x_1152_;
v_b_1148_ = v___y_1150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1162_, size_t v_i_1163_, lean_object* v_bs_1164_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_usize_dec_lt(v_i_1163_, v_sz_1162_);
if (v___x_1165_ == 0)
{
return v_bs_1164_;
}
else
{
lean_object* v_v_1166_; lean_object* v___x_1167_; lean_object* v_bs_x27_1168_; lean_object* v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; lean_object* v___x_1172_; 
v_v_1166_ = lean_array_uget(v_bs_1164_, v_i_1163_);
v___x_1167_ = lean_unsigned_to_nat(0u);
v_bs_x27_1168_ = lean_array_uset(v_bs_1164_, v_i_1163_, v___x_1167_);
v___x_1169_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1166_);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_add(v_i_1163_, v___x_1170_);
v___x_1172_ = lean_array_uset(v_bs_x27_1168_, v_i_1163_, v___x_1169_);
v_i_1163_ = v___x_1171_;
v_bs_1164_ = v___x_1172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1174_){
_start:
{
switch(lean_obj_tag(v_a_1174_))
{
case 6:
{
lean_object* v_xs_1175_; lean_object* v_ref_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1204_; 
v_xs_1175_ = lean_ctor_get(v_a_1174_, 1);
v_ref_1176_ = lean_ctor_get(v_a_1174_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_a_1174_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1178_ = v_a_1174_;
v_isShared_1179_ = v_isSharedCheck_1204_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_xs_1175_);
lean_inc(v_ref_1176_);
lean_dec(v_a_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1204_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_items_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_items_1180_ = lean_ctor_get(v_xs_1175_, 0);
lean_inc_ref(v_items_1180_);
lean_dec_ref(v_xs_1175_);
v___x_1181_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = lean_array_get_size(v_items_1180_);
v___x_1184_ = lean_nat_dec_lt(v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref(v_items_1180_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1181_);
v___x_1186_ = v___x_1178_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_ref_1176_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
else
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_nat_dec_le(v___x_1183_, v___x_1183_);
if (v___x_1188_ == 0)
{
if (v___x_1184_ == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref(v_items_1180_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1181_);
v___x_1190_ = v___x_1178_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_ref_1176_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1181_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
else
{
size_t v___x_1192_; size_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = lean_usize_of_nat(v___x_1183_);
lean_inc(v_ref_1176_);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1176_, v_items_1180_, v___x_1192_, v___x_1193_, v___x_1181_);
lean_dec_ref(v_items_1180_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1194_);
v___x_1196_ = v___x_1178_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_ref_1176_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
size_t v___x_1198_; size_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1198_ = ((size_t)0ULL);
v___x_1199_ = lean_usize_of_nat(v___x_1183_);
lean_inc(v_ref_1176_);
v___x_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1176_, v_items_1180_, v___x_1198_, v___x_1199_, v___x_1181_);
lean_dec_ref(v_items_1180_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1200_);
v___x_1202_ = v___x_1178_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_ref_1176_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
case 5:
{
lean_object* v_ref_1205_; lean_object* v_xs_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1216_; 
v_ref_1205_ = lean_ctor_get(v_a_1174_, 0);
v_xs_1206_ = lean_ctor_get(v_a_1174_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_a_1174_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1208_ = v_a_1174_;
v_isShared_1209_ = v_isSharedCheck_1216_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_xs_1206_);
lean_inc(v_ref_1205_);
lean_dec(v_a_1174_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1216_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
size_t v_sz_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v_sz_1210_ = lean_array_size(v_xs_1206_);
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1210_, v___x_1211_, v_xs_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v___x_1212_);
v___x_1214_ = v___x_1208_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_ref_1205_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
default: 
{
return v_a_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1217_, lean_object* v___x_1218_, lean_object* v_v_x3f_1219_){
_start:
{
if (lean_obj_tag(v_v_x3f_1219_) == 1)
{
lean_object* v_val_1220_; 
v_val_1220_ = lean_ctor_get(v_v_x3f_1219_, 0);
lean_inc(v_val_1220_);
lean_dec_ref_known(v_v_x3f_1219_, 1);
switch(lean_obj_tag(v_val_1220_))
{
case 6:
{
lean_object* v_ref_1221_; lean_object* v_xs_1222_; lean_object* v___x_1223_; 
v_ref_1221_ = lean_ctor_get(v_val_1220_, 0);
lean_inc(v_ref_1221_);
v_xs_1222_ = lean_ctor_get(v_val_1220_, 1);
lean_inc_ref(v_xs_1222_);
lean_dec_ref_known(v_val_1220_, 2);
v___x_1223_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1217_);
if (lean_obj_tag(v___x_1223_) == 6)
{
lean_object* v_xs_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1233_; 
v_xs_1224_ = lean_ctor_get(v___x_1223_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v___x_1223_, 0);
lean_dec(v_unused_1234_);
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1233_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_xs_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1233_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_items_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v_items_1228_ = lean_ctor_get(v_xs_1224_, 0);
lean_inc_ref(v_items_1228_);
lean_dec_ref(v_xs_1224_);
v___x_1229_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1218_, v_xs_1222_, v_items_1228_);
lean_dec_ref(v_items_1228_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1229_);
lean_ctor_set(v___x_1226_, 0, v_ref_1221_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_ref_1221_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_dec_ref(v_xs_1222_);
lean_dec(v_ref_1221_);
lean_dec_ref(v___x_1218_);
return v___x_1223_;
}
}
case 5:
{
lean_object* v_ref_1235_; lean_object* v_xs_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v___x_1218_);
v_ref_1235_ = lean_ctor_get(v_val_1220_, 0);
v_xs_1236_ = lean_ctor_get(v_val_1220_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_val_1220_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1238_ = v_val_1220_;
v_isShared_1239_ = v_isSharedCheck_1255_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_xs_1236_);
lean_inc(v_ref_1235_);
lean_dec(v_val_1220_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1255_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1217_);
if (lean_obj_tag(v___x_1240_) == 5)
{
lean_object* v_xs_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
lean_del_object(v___x_1238_);
v_xs_1241_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1240_, 0);
lean_dec(v_unused_1250_);
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_xs_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = l_Array_append___redArg(v_xs_1236_, v_xs_1241_);
lean_dec_ref(v_xs_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1245_);
lean_ctor_set(v___x_1243_, 0, v_ref_1235_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_ref_1235_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_array_push(v_xs_1236_, v___x_1240_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1251_);
v___x_1253_ = v___x_1238_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_ref_1235_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
default: 
{
lean_object* v___x_1256_; 
lean_dec(v_val_1220_);
lean_dec_ref(v___x_1218_);
v___x_1256_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1217_);
return v___x_1256_;
}
}
}
else
{
lean_object* v___x_1257_; 
lean_dec(v_v_x3f_1219_);
lean_dec_ref(v___x_1218_);
v___x_1257_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1217_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1258_, lean_object* v_k_1259_, lean_object* v_t_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1260_);
lean_inc(v_k_1259_);
v___x_1262_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1261_, v_k_1259_, v_t_1260_);
if (lean_obj_tag(v___x_1262_) == 1)
{
lean_object* v_val_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_k_1259_);
v_val_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1298_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_val_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1298_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_items_1267_; lean_object* v_indices_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1297_; 
v_items_1267_ = lean_ctor_get(v_t_1260_, 0);
v_indices_1268_ = lean_ctor_get(v_t_1260_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_t_1260_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1270_ = v_t_1260_;
v_isShared_1271_ = v_isSharedCheck_1297_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_indices_1268_);
lean_inc(v_items_1267_);
lean_dec(v_t_1260_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1297_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = lean_array_get_size(v_items_1267_);
v___x_1273_ = lean_nat_dec_lt(v_val_1263_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1275_; 
lean_del_object(v___x_1265_);
lean_dec(v_val_1263_);
lean_dec_ref(v_newV_1258_);
if (v_isShared_1271_ == 0)
{
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_items_1267_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_indices_1268_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
else
{
lean_object* v_v_1277_; lean_object* v_fst_1278_; lean_object* v_snd_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1296_; 
v_v_1277_ = lean_array_fget(v_items_1267_, v_val_1263_);
v_fst_1278_ = lean_ctor_get(v_v_1277_, 0);
v_snd_1279_ = lean_ctor_get(v_v_1277_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_v_1277_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1281_ = v_v_1277_;
v_isShared_1282_ = v_isSharedCheck_1296_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_snd_1279_);
lean_inc(v_fst_1278_);
lean_dec(v_v_1277_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1296_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v_xs_x27_1284_; lean_object* v___x_1286_; 
v___x_1283_ = lean_box(0);
v_xs_x27_1284_ = lean_array_fset(v_items_1267_, v_val_1263_, v___x_1283_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v_snd_1279_);
v___x_1286_ = v___x_1265_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_snd_1279_);
v___x_1286_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1258_, v___x_1261_, v___x_1286_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1287_);
v___x_1289_ = v___x_1281_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_fst_1278_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_array_fset(v_xs_x27_1284_, v_val_1263_, v___x_1289_);
lean_dec(v_val_1263_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1290_);
v___x_1292_ = v___x_1270_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_indices_1268_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
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
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec(v___x_1262_);
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1258_, v___x_1261_, v___x_1299_);
v___x_1301_ = l_Lake_Toml_RBDict_push___redArg(v___x_1261_, v_k_1259_, v___x_1300_, v_t_1260_);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1302_, lean_object* v_head_1303_, lean_object* v_tail_1304_, lean_object* v_newV_1305_, lean_object* v_v_x3f_1306_){
_start:
{
if (lean_obj_tag(v_v_x3f_1306_) == 1)
{
lean_object* v_val_1307_; 
v_val_1307_ = lean_ctor_get(v_v_x3f_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref_known(v_v_x3f_1306_, 1);
switch(lean_obj_tag(v_val_1307_))
{
case 5:
{
lean_object* v_ref_1308_; lean_object* v_xs_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_ref_1308_ = lean_ctor_get(v_val_1307_, 0);
v_xs_1309_ = lean_ctor_get(v_val_1307_, 1);
v___x_1310_ = lean_array_get_size(v_xs_1309_);
v___x_1311_ = lean_unsigned_to_nat(1u);
v___x_1312_ = lean_nat_sub(v___x_1310_, v___x_1311_);
v___x_1313_ = lean_nat_dec_lt(v___x_1312_, v___x_1310_);
if (v___x_1313_ == 0)
{
lean_dec(v___x_1312_);
lean_dec_ref(v_newV_1305_);
lean_dec(v_tail_1304_);
lean_dec(v_head_1303_);
lean_dec(v_kRef_1302_);
return v_val_1307_;
}
else
{
lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1338_; 
lean_inc_ref(v_xs_1309_);
lean_inc(v_ref_1308_);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_val_1307_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; lean_object* v_unused_1340_; 
v_unused_1339_ = lean_ctor_get(v_val_1307_, 1);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v_val_1307_, 0);
lean_dec(v_unused_1340_);
v___x_1315_ = v_val_1307_;
v_isShared_1316_ = v_isSharedCheck_1338_;
goto v_resetjp_1314_;
}
else
{
lean_dec(v_val_1307_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1338_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_v_1317_; lean_object* v___x_1318_; lean_object* v_xs_x27_1319_; lean_object* v___y_1321_; 
v_v_1317_ = lean_array_fget(v_xs_1309_, v___x_1312_);
v___x_1318_ = lean_box(0);
v_xs_x27_1319_ = lean_array_fset(v_xs_1309_, v___x_1312_, v___x_1318_);
if (lean_obj_tag(v_v_1317_) == 6)
{
lean_object* v_ref_1326_; lean_object* v_xs_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
v_ref_1326_ = lean_ctor_get(v_v_1317_, 0);
v_xs_1327_ = lean_ctor_get(v_v_1317_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_v_1317_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v_v_1317_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_xs_1327_);
lean_inc(v_ref_1326_);
lean_dec(v_v_1317_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1327_, v_kRef_1302_, v_head_1303_, v_tail_1304_, v_newV_1305_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v___x_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_ref_1326_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
v___y_1321_ = v___x_1333_;
goto v___jp_1320_;
}
}
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec(v_v_1317_);
lean_dec_ref(v_newV_1305_);
lean_dec(v_tail_1304_);
lean_dec(v_head_1303_);
v___x_1336_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1337_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_kRef_1302_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___y_1321_ = v___x_1337_;
goto v___jp_1320_;
}
v___jp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_array_fset(v_xs_x27_1319_, v___x_1312_, v___y_1321_);
lean_dec(v___x_1312_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v___x_1322_);
v___x_1324_ = v___x_1315_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_ref_1308_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1341_; lean_object* v_xs_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1350_; 
v_ref_1341_ = lean_ctor_get(v_val_1307_, 0);
v_xs_1342_ = lean_ctor_get(v_val_1307_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_val_1307_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1344_ = v_val_1307_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_xs_1342_);
lean_inc(v_ref_1341_);
lean_dec(v_val_1307_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1342_, v_kRef_1302_, v_head_1303_, v_tail_1304_, v_newV_1305_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_ref_1341_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
default: 
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec(v_val_1307_);
v___x_1351_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1302_);
v___x_1352_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1351_, v_kRef_1302_, v_head_1303_, v_tail_1304_, v_newV_1305_);
v___x_1353_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_kRef_1302_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
return v___x_1353_;
}
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_v_x3f_1306_);
v___x_1354_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1302_);
v___x_1355_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1354_, v_kRef_1302_, v_head_1303_, v_tail_1304_, v_newV_1305_);
v___x_1356_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_kRef_1302_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1357_, lean_object* v_head_1358_, lean_object* v_tail_1359_, lean_object* v_newV_1360_, lean_object* v_k_1361_, lean_object* v_t_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1362_);
lean_inc(v_k_1361_);
v___x_1364_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1363_, v_k_1361_, v_t_1362_);
if (lean_obj_tag(v___x_1364_) == 1)
{
lean_object* v_val_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_k_1361_);
v_val_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1400_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_val_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1400_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_items_1369_; lean_object* v_indices_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1399_; 
v_items_1369_ = lean_ctor_get(v_t_1362_, 0);
v_indices_1370_ = lean_ctor_get(v_t_1362_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_t_1362_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1372_ = v_t_1362_;
v_isShared_1373_ = v_isSharedCheck_1399_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_indices_1370_);
lean_inc(v_items_1369_);
lean_dec(v_t_1362_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1399_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_array_get_size(v_items_1369_);
v___x_1375_ = lean_nat_dec_lt(v_val_1365_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1377_; 
lean_del_object(v___x_1367_);
lean_dec(v_val_1365_);
lean_dec_ref(v_newV_1360_);
lean_dec(v_tail_1359_);
lean_dec(v_head_1358_);
lean_dec(v_kRef_1357_);
if (v_isShared_1373_ == 0)
{
v___x_1377_ = v___x_1372_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_items_1369_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_indices_1370_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
else
{
lean_object* v_v_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1398_; 
v_v_1379_ = lean_array_fget(v_items_1369_, v_val_1365_);
v_fst_1380_ = lean_ctor_get(v_v_1379_, 0);
v_snd_1381_ = lean_ctor_get(v_v_1379_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_v_1379_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1383_ = v_v_1379_;
v_isShared_1384_ = v_isSharedCheck_1398_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_snd_1381_);
lean_inc(v_fst_1380_);
lean_dec(v_v_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1398_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v_xs_x27_1386_; lean_object* v___x_1388_; 
v___x_1385_ = lean_box(0);
v_xs_x27_1386_ = lean_array_fset(v_items_1369_, v_val_1365_, v___x_1385_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v_snd_1381_);
v___x_1388_ = v___x_1367_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_snd_1381_);
v___x_1388_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1357_, v_head_1358_, v_tail_1359_, v_newV_1360_, v___x_1388_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1389_);
v___x_1391_ = v___x_1383_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_fst_1380_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = lean_array_fset(v_xs_x27_1386_, v_val_1365_, v___x_1391_);
lean_dec(v_val_1365_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1392_);
v___x_1394_ = v___x_1372_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_indices_1370_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
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
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_dec(v___x_1364_);
v___x_1401_ = lean_box(0);
v___x_1402_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1357_, v_head_1358_, v_tail_1359_, v_newV_1360_, v___x_1401_);
v___x_1403_ = l_Lake_Toml_RBDict_push___redArg(v___x_1363_, v_k_1361_, v___x_1402_, v_t_1362_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1404_, lean_object* v_kRef_1405_, lean_object* v_k_1406_, lean_object* v_ks_1407_, lean_object* v_newV_1408_){
_start:
{
if (lean_obj_tag(v_ks_1407_) == 0)
{
lean_object* v___x_1409_; 
lean_dec(v_kRef_1405_);
v___x_1409_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1408_, v_k_1406_, v_t_1404_);
return v___x_1409_;
}
else
{
lean_object* v_head_1410_; lean_object* v_tail_1411_; lean_object* v___x_1412_; 
v_head_1410_ = lean_ctor_get(v_ks_1407_, 0);
lean_inc(v_head_1410_);
v_tail_1411_ = lean_ctor_get(v_ks_1407_, 1);
lean_inc(v_tail_1411_);
lean_dec_ref_known(v_ks_1407_, 2);
v___x_1412_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1405_, v_head_1410_, v_tail_1411_, v_newV_1408_, v_k_1406_, v_t_1404_);
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1413_, lean_object* v_i_1414_, lean_object* v_bs_1415_){
_start:
{
size_t v_sz_boxed_1416_; size_t v_i_boxed_1417_; lean_object* v_res_1418_; 
v_sz_boxed_1416_ = lean_unbox_usize(v_sz_1413_);
lean_dec(v_sz_1413_);
v_i_boxed_1417_ = lean_unbox_usize(v_i_1414_);
lean_dec(v_i_1414_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1416_, v_i_boxed_1417_, v_bs_1415_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1419_, lean_object* v_as_1420_, lean_object* v_i_1421_, lean_object* v_stop_1422_, lean_object* v_b_1423_){
_start:
{
size_t v_i_boxed_1424_; size_t v_stop_boxed_1425_; lean_object* v_res_1426_; 
v_i_boxed_1424_ = lean_unbox_usize(v_i_1421_);
lean_dec(v_i_1421_);
v_stop_boxed_1425_ = lean_unbox_usize(v_stop_1422_);
lean_dec(v_stop_1422_);
v_res_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1419_, v_as_1420_, v_i_boxed_1424_, v_stop_boxed_1425_, v_b_1423_);
lean_dec_ref(v_as_1420_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1427_, size_t v_i_1428_, size_t v_stop_1429_, lean_object* v_b_1430_){
_start:
{
lean_object* v___y_1432_; uint8_t v___x_1436_; 
v___x_1436_ = lean_usize_dec_eq(v_i_1428_, v_stop_1429_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v_ref_1438_; lean_object* v_key_1439_; lean_object* v_val_1440_; lean_object* v___x_1441_; 
v___x_1437_ = lean_array_uget_borrowed(v_as_1427_, v_i_1428_);
v_ref_1438_ = lean_ctor_get(v___x_1437_, 0);
v_key_1439_ = lean_ctor_get(v___x_1437_, 1);
v_val_1440_ = lean_ctor_get(v___x_1437_, 2);
lean_inc(v_key_1439_);
v___x_1441_ = l_Lean_Name_components(v_key_1439_);
if (lean_obj_tag(v___x_1441_) == 0)
{
v___y_1432_ = v_b_1430_;
goto v___jp_1431_;
}
else
{
lean_object* v_head_1442_; lean_object* v_tail_1443_; lean_object* v___x_1444_; 
v_head_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_head_1442_);
v_tail_1443_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_tail_1443_);
lean_dec_ref_known(v___x_1441_, 2);
lean_inc_ref(v_val_1440_);
lean_inc(v_ref_1438_);
v___x_1444_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1430_, v_ref_1438_, v_head_1442_, v_tail_1443_, v_val_1440_);
v___y_1432_ = v___x_1444_;
goto v___jp_1431_;
}
}
else
{
return v_b_1430_;
}
v___jp_1431_:
{
size_t v___x_1433_; size_t v___x_1434_; 
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1428_, v___x_1433_);
v_i_1428_ = v___x_1434_;
v_b_1430_ = v___y_1432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1445_, lean_object* v_i_1446_, lean_object* v_stop_1447_, lean_object* v_b_1448_){
_start:
{
size_t v_i_boxed_1449_; size_t v_stop_boxed_1450_; lean_object* v_res_1451_; 
v_i_boxed_1449_ = lean_unbox_usize(v_i_1446_);
lean_dec(v_i_1446_);
v_stop_boxed_1450_ = lean_unbox_usize(v_stop_1447_);
lean_dec(v_stop_1447_);
v_res_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1445_, v_i_boxed_1449_, v_stop_boxed_1450_, v_b_1448_);
lean_dec_ref(v_as_1445_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1452_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1453_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_array_get_size(v_items_1452_);
v___x_1456_ = lean_nat_dec_lt(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
return v___x_1453_;
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_nat_dec_le(v___x_1455_, v___x_1455_);
if (v___x_1457_ == 0)
{
if (v___x_1456_ == 0)
{
return v___x_1453_;
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1455_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1452_, v___x_1458_, v___x_1459_, v___x_1453_);
return v___x_1460_;
}
}
else
{
size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = lean_usize_of_nat(v___x_1455_);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1452_, v___x_1461_, v___x_1462_, v___x_1453_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1464_);
lean_dec_ref(v_items_1464_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
v___x_1471_ = lean_apply_4(v_x_1466_, v___x_1470_, v_a_1467_, v_a_1468_, lean_box(0));
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1482_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1482_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1482_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_snd_1476_; lean_object* v_items_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v_snd_1476_ = lean_ctor_get(v_a_1472_, 1);
lean_inc(v_snd_1476_);
lean_dec(v_a_1472_);
v_items_1477_ = lean_ctor_get(v_snd_1476_, 5);
lean_inc_ref(v_items_1477_);
lean_dec(v_snd_1476_);
v___x_1478_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1477_);
lean_dec_ref(v_items_1477_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1478_);
v___x_1480_ = v___x_1474_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
v_a_1483_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1471_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1471_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
return v_res_1495_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1504_, uint8_t v___y_1505_, lean_object* v_x_1506_){
_start:
{
if (lean_obj_tag(v_x_1506_) == 1)
{
lean_object* v_pre_1507_; 
v_pre_1507_ = lean_ctor_get(v_x_1506_, 0);
switch(lean_obj_tag(v_pre_1507_))
{
case 1:
{
lean_object* v_pre_1508_; 
v_pre_1508_ = lean_ctor_get(v_pre_1507_, 0);
switch(lean_obj_tag(v_pre_1508_))
{
case 0:
{
lean_object* v_str_1509_; lean_object* v_str_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v_str_1509_ = lean_ctor_get(v_x_1506_, 1);
v_str_1510_ = lean_ctor_get(v_pre_1507_, 1);
v___x_1511_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1512_ = lean_string_dec_eq(v_str_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1514_ = lean_string_dec_eq(v_str_1510_, v___x_1513_);
if (v___x_1514_ == 0)
{
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1516_ = lean_string_dec_eq(v_str_1509_, v___x_1515_);
if (v___x_1516_ == 0)
{
return v___x_1516_;
}
else
{
return v_suppressElabErrors_1504_;
}
}
}
else
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1518_ = lean_string_dec_eq(v_str_1509_, v___x_1517_);
if (v___x_1518_ == 0)
{
return v___x_1518_;
}
else
{
return v_suppressElabErrors_1504_;
}
}
}
case 1:
{
lean_object* v_pre_1519_; 
v_pre_1519_ = lean_ctor_get(v_pre_1508_, 0);
if (lean_obj_tag(v_pre_1519_) == 0)
{
lean_object* v_str_1520_; lean_object* v_str_1521_; lean_object* v_str_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v_str_1520_ = lean_ctor_get(v_x_1506_, 1);
v_str_1521_ = lean_ctor_get(v_pre_1507_, 1);
v_str_1522_ = lean_ctor_get(v_pre_1508_, 1);
v___x_1523_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1524_ = lean_string_dec_eq(v_str_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1526_ = lean_string_dec_eq(v_str_1521_, v___x_1525_);
if (v___x_1526_ == 0)
{
return v___x_1526_;
}
else
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1528_ = lean_string_dec_eq(v_str_1520_, v___x_1527_);
if (v___x_1528_ == 0)
{
return v___x_1528_;
}
else
{
return v_suppressElabErrors_1504_;
}
}
}
}
else
{
return v___y_1505_;
}
}
default: 
{
return v___y_1505_;
}
}
}
case 0:
{
lean_object* v_str_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v_str_1529_ = lean_ctor_get(v_x_1506_, 1);
v___x_1530_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1531_ = lean_string_dec_eq(v_str_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
return v___x_1531_;
}
else
{
return v_suppressElabErrors_1504_;
}
}
default: 
{
return v___y_1505_;
}
}
}
else
{
return v___y_1505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1532_, lean_object* v___y_1533_, lean_object* v_x_1534_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1535_; uint8_t v___y_10676__boxed_1536_; uint8_t v_res_1537_; lean_object* v_r_1538_; 
v_suppressElabErrors_boxed_1535_ = lean_unbox(v_suppressElabErrors_1532_);
v___y_10676__boxed_1536_ = lean_unbox(v___y_1533_);
v_res_1537_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1535_, v___y_10676__boxed_1536_, v_x_1534_);
lean_dec(v_x_1534_);
v_r_1538_ = lean_box(v_res_1537_);
return v_r_1538_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1539_, lean_object* v_opt_1540_){
_start:
{
lean_object* v_name_1541_; lean_object* v_defValue_1542_; lean_object* v_map_1543_; lean_object* v___x_1544_; 
v_name_1541_ = lean_ctor_get(v_opt_1540_, 0);
v_defValue_1542_ = lean_ctor_get(v_opt_1540_, 1);
v_map_1543_ = lean_ctor_get(v_opts_1539_, 0);
v___x_1544_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1543_, v_name_1541_);
if (lean_obj_tag(v___x_1544_) == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_unbox(v_defValue_1542_);
return v___x_1545_;
}
else
{
lean_object* v_val_1546_; 
v_val_1546_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v___x_1544_, 1);
if (lean_obj_tag(v_val_1546_) == 1)
{
uint8_t v_v_1547_; 
v_v_1547_ = lean_ctor_get_uint8(v_val_1546_, 0);
lean_dec_ref_known(v_val_1546_, 0);
return v_v_1547_;
}
else
{
uint8_t v___x_1548_; 
lean_dec(v_val_1546_);
v___x_1548_ = lean_unbox(v_defValue_1542_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1549_, lean_object* v_opt_1550_){
_start:
{
uint8_t v_res_1551_; lean_object* v_r_1552_; 
v_res_1551_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1549_, v_opt_1550_);
lean_dec_ref(v_opt_1550_);
lean_dec_ref(v_opts_1549_);
v_r_1552_ = lean_box(v_res_1551_);
return v_r_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1554_, lean_object* v_msgData_1555_, uint8_t v_severity_1556_, uint8_t v_isSilent_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_a_1563_; lean_object* v___y_1567_; lean_object* v___y_1568_; uint8_t v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; uint8_t v___y_1573_; lean_object* v_toCold_1574_; lean_object* v___y_1575_; lean_object* v___y_1603_; lean_object* v___y_1604_; uint8_t v___y_1605_; uint8_t v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___y_1609_; lean_object* v___y_1610_; uint8_t v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; uint8_t v___y_1633_; uint8_t v___y_1634_; lean_object* v___y_1635_; uint8_t v___y_1639_; uint8_t v___y_1640_; uint8_t v___y_1641_; uint8_t v___x_1652_; uint8_t v___y_1654_; uint8_t v___y_1655_; uint8_t v___y_1656_; uint8_t v___y_1658_; uint8_t v___x_1667_; 
v___x_1652_ = 2;
v___x_1667_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1556_, v___x_1652_);
if (v___x_1667_ == 0)
{
v___y_1658_ = v___x_1667_;
goto v___jp_1657_;
}
else
{
uint8_t v___x_1668_; 
lean_inc_ref(v_msgData_1555_);
v___x_1668_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1555_);
v___y_1658_ = v___x_1668_;
goto v___jp_1657_;
}
v___jp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_a_1563_);
lean_ctor_set(v___x_1564_, 1, v___y_1558_);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
v___jp_1566_:
{
lean_object* v_currNamespace_1576_; lean_object* v_openDecls_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_env_1582_; lean_object* v_nextMacroScope_1583_; lean_object* v_ngen_1584_; lean_object* v_auxDeclNGen_1585_; lean_object* v_traceState_1586_; lean_object* v_cache_1587_; lean_object* v_recordedDeps_1588_; lean_object* v_messages_1589_; lean_object* v_infoState_1590_; lean_object* v_snapshotTasks_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1601_; 
v_currNamespace_1576_ = lean_ctor_get(v_toCold_1574_, 4);
v_openDecls_1577_ = lean_ctor_get(v_toCold_1574_, 5);
lean_inc(v_openDecls_1577_);
lean_inc(v_currNamespace_1576_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v_currNamespace_1576_);
lean_ctor_set(v___x_1578_, 1, v_openDecls_1577_);
v___x_1579_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v___y_1567_);
lean_inc_ref(v___y_1571_);
lean_inc_ref(v___y_1572_);
v___x_1580_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1580_, 0, v___y_1572_);
lean_ctor_set(v___x_1580_, 1, v___y_1570_);
lean_ctor_set(v___x_1580_, 2, v___y_1568_);
lean_ctor_set(v___x_1580_, 3, v___y_1571_);
lean_ctor_set(v___x_1580_, 4, v___x_1579_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*5, v___y_1573_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*5 + 1, v___y_1569_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*5 + 2, v_isSilent_1557_);
v___x_1581_ = lean_st_ref_take(v___y_1575_);
v_env_1582_ = lean_ctor_get(v___x_1581_, 0);
v_nextMacroScope_1583_ = lean_ctor_get(v___x_1581_, 1);
v_ngen_1584_ = lean_ctor_get(v___x_1581_, 2);
v_auxDeclNGen_1585_ = lean_ctor_get(v___x_1581_, 3);
v_traceState_1586_ = lean_ctor_get(v___x_1581_, 4);
v_cache_1587_ = lean_ctor_get(v___x_1581_, 5);
v_recordedDeps_1588_ = lean_ctor_get(v___x_1581_, 6);
v_messages_1589_ = lean_ctor_get(v___x_1581_, 7);
v_infoState_1590_ = lean_ctor_get(v___x_1581_, 8);
v_snapshotTasks_1591_ = lean_ctor_get(v___x_1581_, 9);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1593_ = v___x_1581_;
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_snapshotTasks_1591_);
lean_inc(v_infoState_1590_);
lean_inc(v_messages_1589_);
lean_inc(v_recordedDeps_1588_);
lean_inc(v_cache_1587_);
lean_inc(v_traceState_1586_);
lean_inc(v_auxDeclNGen_1585_);
lean_inc(v_ngen_1584_);
lean_inc(v_nextMacroScope_1583_);
lean_inc(v_env_1582_);
lean_dec(v___x_1581_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = lean_box(0);
v___x_1596_ = l_Lean_MessageLog_add(v___x_1580_, v_messages_1589_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 7, v___x_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_env_1582_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_nextMacroScope_1583_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_ngen_1584_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_auxDeclNGen_1585_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_traceState_1586_);
lean_ctor_set(v_reuseFailAlloc_1600_, 5, v_cache_1587_);
lean_ctor_set(v_reuseFailAlloc_1600_, 6, v_recordedDeps_1588_);
lean_ctor_set(v_reuseFailAlloc_1600_, 7, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1600_, 8, v_infoState_1590_);
lean_ctor_set(v_reuseFailAlloc_1600_, 9, v_snapshotTasks_1591_);
v___x_1598_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_st_ref_put(v___y_1575_, v___x_1598_);
v_a_1563_ = v___x_1595_;
goto v___jp_1562_;
}
}
}
v___jp_1602_:
{
lean_object* v_fileName_1611_; lean_object* v_fileMap_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1627_; 
v_fileName_1611_ = lean_ctor_get(v___y_1607_, 0);
v_fileMap_1612_ = lean_ctor_get(v___y_1607_, 1);
v___x_1613_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1555_);
v___x_1614_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1613_, v___y_1559_, v___y_1560_);
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1627_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1627_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_inc_ref_n(v_fileMap_1612_, 2);
v___x_1619_ = l_Lean_FileMap_toPosition(v_fileMap_1612_, v___y_1608_);
lean_dec(v___y_1608_);
v___x_1620_ = l_Lean_FileMap_toPosition(v_fileMap_1612_, v___y_1610_);
lean_dec(v___y_1610_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set_tag(v___x_1617_, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1620_);
v___x_1622_ = v___x_1617_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; 
v___x_1623_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1605_ == 0)
{
lean_dec_ref(v___y_1604_);
v___y_1567_ = v_a_1615_;
v___y_1568_ = v___x_1622_;
v___y_1569_ = v___y_1606_;
v___y_1570_ = v___x_1619_;
v___y_1571_ = v___x_1623_;
v___y_1572_ = v_fileName_1611_;
v___y_1573_ = v___y_1609_;
v_toCold_1574_ = v___y_1603_;
v___y_1575_ = v___y_1560_;
goto v___jp_1566_;
}
else
{
uint8_t v___x_1624_; 
lean_inc(v_a_1615_);
v___x_1624_ = l_Lean_MessageData_hasTag(v___y_1604_, v_a_1615_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; 
lean_dec_ref(v___x_1622_);
lean_dec_ref(v___x_1619_);
lean_dec(v_a_1615_);
v___x_1625_ = lean_box(0);
v_a_1563_ = v___x_1625_;
goto v___jp_1562_;
}
else
{
v___y_1567_ = v_a_1615_;
v___y_1568_ = v___x_1622_;
v___y_1569_ = v___y_1606_;
v___y_1570_ = v___x_1619_;
v___y_1571_ = v___x_1623_;
v___y_1572_ = v_fileName_1611_;
v___y_1573_ = v___y_1609_;
v_toCold_1574_ = v___y_1603_;
v___y_1575_ = v___y_1560_;
goto v___jp_1566_;
}
}
}
}
}
v___jp_1628_:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Syntax_getTailPos_x3f(v___y_1632_, v___y_1634_);
lean_dec(v___y_1632_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_inc(v___y_1635_);
v___y_1603_ = v___y_1630_;
v___y_1604_ = v___y_1631_;
v___y_1605_ = v___y_1629_;
v___y_1606_ = v___y_1633_;
v___y_1607_ = v___y_1630_;
v___y_1608_ = v___y_1635_;
v___y_1609_ = v___y_1634_;
v___y_1610_ = v___y_1635_;
goto v___jp_1602_;
}
else
{
lean_object* v_val_1637_; 
v_val_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_val_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___y_1603_ = v___y_1630_;
v___y_1604_ = v___y_1631_;
v___y_1605_ = v___y_1629_;
v___y_1606_ = v___y_1633_;
v___y_1607_ = v___y_1630_;
v___y_1608_ = v___y_1635_;
v___y_1609_ = v___y_1634_;
v___y_1610_ = v_val_1637_;
goto v___jp_1602_;
}
}
v___jp_1638_:
{
lean_object* v_toCold_1642_; lean_object* v_ref_1643_; uint8_t v_suppressElabErrors_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___f_1647_; lean_object* v_ref_1648_; lean_object* v___x_1649_; 
v_toCold_1642_ = lean_ctor_get(v___y_1559_, 0);
v_ref_1643_ = lean_ctor_get(v___y_1559_, 2);
v_suppressElabErrors_1644_ = lean_ctor_get_uint8(v___y_1559_, sizeof(void*)*3 + 2);
v___x_1645_ = lean_box(v_suppressElabErrors_1644_);
v___x_1646_ = lean_box(v___y_1639_);
v___f_1647_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1647_, 0, v___x_1645_);
lean_closure_set(v___f_1647_, 1, v___x_1646_);
v_ref_1648_ = l_Lean_replaceRef(v_ref_1554_, v_ref_1643_);
v___x_1649_ = l_Lean_Syntax_getPos_x3f(v_ref_1648_, v___y_1640_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_unsigned_to_nat(0u);
v___y_1629_ = v_suppressElabErrors_1644_;
v___y_1630_ = v_toCold_1642_;
v___y_1631_ = v___f_1647_;
v___y_1632_ = v_ref_1648_;
v___y_1633_ = v___y_1641_;
v___y_1634_ = v___y_1640_;
v___y_1635_ = v___x_1650_;
goto v___jp_1628_;
}
else
{
lean_object* v_val_1651_; 
v_val_1651_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1651_);
lean_dec_ref_known(v___x_1649_, 1);
v___y_1629_ = v_suppressElabErrors_1644_;
v___y_1630_ = v_toCold_1642_;
v___y_1631_ = v___f_1647_;
v___y_1632_ = v_ref_1648_;
v___y_1633_ = v___y_1641_;
v___y_1634_ = v___y_1640_;
v___y_1635_ = v_val_1651_;
goto v___jp_1628_;
}
}
v___jp_1653_:
{
if (v___y_1656_ == 0)
{
v___y_1639_ = v___y_1654_;
v___y_1640_ = v___y_1655_;
v___y_1641_ = v_severity_1556_;
goto v___jp_1638_;
}
else
{
v___y_1639_ = v___y_1654_;
v___y_1640_ = v___y_1655_;
v___y_1641_ = v___x_1652_;
goto v___jp_1638_;
}
}
v___jp_1657_:
{
if (v___y_1658_ == 0)
{
uint8_t v___x_1659_; uint8_t v___x_1660_; 
v___x_1659_ = 1;
v___x_1660_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1556_, v___x_1659_);
if (v___x_1660_ == 0)
{
v___y_1654_ = v___y_1658_;
v___y_1655_ = v___y_1658_;
v___y_1656_ = v___x_1660_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1661_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1559_);
v___x_1662_ = l_Lean_warningAsError;
v___x_1663_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v___x_1661_, v___x_1662_);
lean_dec_ref(v___x_1661_);
v___y_1654_ = v___y_1658_;
v___y_1655_ = v___y_1658_;
v___y_1656_ = v___x_1663_;
goto v___jp_1653_;
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec_ref(v_msgData_1555_);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v___y_1558_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1669_, lean_object* v_msgData_1670_, lean_object* v_severity_1671_, lean_object* v_isSilent_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v_severity_boxed_1677_; uint8_t v_isSilent_boxed_1678_; lean_object* v_res_1679_; 
v_severity_boxed_1677_ = lean_unbox(v_severity_1671_);
v_isSilent_boxed_1678_ = lean_unbox(v_isSilent_1672_);
v_res_1679_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1669_, v_msgData_1670_, v_severity_boxed_1677_, v_isSilent_boxed_1678_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v_ref_1669_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1680_, lean_object* v_msgData_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v___x_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = 2;
v___x_1687_ = 0;
v___x_1688_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1680_, v_msgData_1681_, v___x_1686_, v___x_1687_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1689_, lean_object* v_msgData_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1689_, v_msgData_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v_ref_1689_);
return v_res_1695_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1699_ = l_Lean_MessageData_ofFormat(v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1700_, lean_object* v_as_1701_, size_t v_sz_1702_, size_t v_i_1703_, uint8_t v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_snd_1710_; lean_object* v_snd_1711_; lean_object* v___y_1717_; uint8_t v___y_1718_; lean_object* v_a_1735_; uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_lt(v_i_1703_, v_sz_1702_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = lean_box(v_b_1704_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v___y_1705_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1743_; uint8_t v_recovering_1744_; 
v_a_1742_ = lean_array_uget_borrowed(v_as_1701_, v_i_1703_);
v___x_1743_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1742_);
v_recovering_1744_ = l_Lean_Syntax_isOfKind(v_a_1742_, v___x_1743_);
if (v_recovering_1744_ == 0)
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_a_1742_);
v___x_1746_ = l_Lean_Syntax_isOfKind(v_a_1742_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1742_);
v___x_1748_ = l_Lean_Syntax_isOfKind(v_a_1742_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1705_);
v___x_1750_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1742_, v___x_1749_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v_snd_1752_; lean_object* v___x_1753_; 
lean_dec_ref(v___y_1705_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v_snd_1752_ = lean_ctor_get(v_a_1751_, 1);
lean_inc(v_snd_1752_);
lean_dec(v_a_1751_);
v___x_1753_ = lean_box(v_b_1704_);
v_snd_1710_ = v___x_1753_;
v_snd_1711_ = v_snd_1752_;
goto v___jp_1709_;
}
else
{
lean_object* v_a_1754_; 
v_a_1754_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1750_, 1);
v_a_1735_ = v_a_1754_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1755_; 
lean_inc_ref(v___y_1705_);
lean_inc(v_a_1742_);
v___x_1755_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1742_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v_snd_1757_; lean_object* v___x_1758_; 
lean_dec_ref(v___y_1705_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v_snd_1757_ = lean_ctor_get(v_a_1756_, 1);
lean_inc(v_snd_1757_);
lean_dec(v_a_1756_);
v___x_1758_ = lean_box(v_recovering_1744_);
v_snd_1710_ = v___x_1758_;
v_snd_1711_ = v_snd_1757_;
goto v___jp_1709_;
}
else
{
lean_object* v_a_1759_; 
v_a_1759_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1755_, 1);
v_a_1735_ = v_a_1759_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v___x_1760_; 
lean_inc_ref(v___y_1705_);
lean_inc(v_a_1742_);
v___x_1760_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1742_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v_snd_1762_; lean_object* v___x_1763_; 
lean_dec_ref(v___y_1705_);
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v_snd_1762_ = lean_ctor_get(v_a_1761_, 1);
lean_inc(v_snd_1762_);
lean_dec(v_a_1761_);
v___x_1763_ = lean_box(v_recovering_1744_);
v_snd_1710_ = v___x_1763_;
v_snd_1711_ = v_snd_1762_;
goto v___jp_1709_;
}
else
{
lean_object* v_a_1764_; 
v_a_1764_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1760_, 1);
v_a_1735_ = v_a_1764_;
goto v___jp_1734_;
}
}
}
else
{
if (v_b_1704_ == 0)
{
lean_object* v___x_1765_; 
lean_inc_ref(v___y_1705_);
lean_inc(v_a_1742_);
v___x_1765_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1742_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v_snd_1767_; lean_object* v___x_1768_; 
lean_dec_ref(v___y_1705_);
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v_snd_1767_ = lean_ctor_get(v_a_1766_, 1);
lean_inc(v_snd_1767_);
lean_dec(v_a_1766_);
v___x_1768_ = lean_box(v_b_1704_);
v_snd_1710_ = v___x_1768_;
v_snd_1711_ = v_snd_1767_;
goto v___jp_1709_;
}
else
{
lean_object* v_a_1769_; 
v_a_1769_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1765_, 1);
v_a_1735_ = v_a_1769_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_box(v_b_1704_);
v_snd_1710_ = v___x_1770_;
v_snd_1711_ = v___y_1705_;
goto v___jp_1709_;
}
}
}
v___jp_1709_:
{
size_t v___x_1712_; size_t v___x_1713_; uint8_t v___x_1714_; 
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_add(v_i_1703_, v___x_1712_);
v___x_1714_ = lean_unbox(v_snd_1710_);
lean_dec(v_snd_1710_);
v_i_1703_ = v___x_1713_;
v_b_1704_ = v___x_1714_;
v___y_1705_ = v_snd_1711_;
goto _start;
}
v___jp_1716_:
{
if (v___y_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = l_Lean_Exception_getRef(v___y_1717_);
v___x_1720_ = l_Lean_Exception_toMessageData(v___y_1717_);
v___x_1721_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1719_, v___x_1720_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___x_1719_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v_snd_1723_; lean_object* v___x_1724_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v_snd_1723_ = lean_ctor_get(v_a_1722_, 1);
lean_inc(v_snd_1723_);
lean_dec(v_a_1722_);
v___x_1724_ = lean_box(v_recovering_1700_);
v_snd_1710_ = v___x_1724_;
v_snd_1711_ = v_snd_1723_;
goto v___jp_1709_;
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v_a_1725_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1721_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1721_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v___x_1733_; 
lean_dec_ref(v___y_1705_);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___y_1717_);
return v___x_1733_;
}
}
v___jp_1734_:
{
uint8_t v___x_1736_; 
v___x_1736_ = l_Lean_Exception_isInterrupt(v_a_1735_);
if (v___x_1736_ == 0)
{
uint8_t v___x_1737_; 
lean_inc_ref(v_a_1735_);
v___x_1737_ = l_Lean_Exception_isRuntime(v_a_1735_);
v___y_1717_ = v_a_1735_;
v___y_1718_ = v___x_1737_;
goto v___jp_1716_;
}
else
{
v___y_1717_ = v_a_1735_;
v___y_1718_ = v___x_1736_;
goto v___jp_1716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1771_, lean_object* v_as_1772_, lean_object* v_sz_1773_, lean_object* v_i_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
uint8_t v_recovering_boxed_1780_; size_t v_sz_boxed_1781_; size_t v_i_boxed_1782_; uint8_t v_b_boxed_1783_; lean_object* v_res_1784_; 
v_recovering_boxed_1780_ = lean_unbox(v_recovering_1771_);
v_sz_boxed_1781_ = lean_unbox_usize(v_sz_1773_);
lean_dec(v_sz_1773_);
v_i_boxed_1782_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_b_boxed_1783_ = lean_unbox(v_b_1775_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1780_, v_as_1772_, v_sz_boxed_1781_, v_i_boxed_1782_, v_b_boxed_1783_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v_as_1772_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_ref_1789_; lean_object* v___x_1790_; lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1799_; 
v_ref_1789_ = lean_ctor_get(v___y_1786_, 2);
v___x_1790_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1785_, v___y_1786_, v___y_1787_);
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_inc(v_ref_1789_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_ref_1789_);
lean_ctor_set(v___x_1795_, 1, v_a_1791_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set_tag(v___x_1793_, 1);
lean_ctor_set(v___x_1793_, 0, v___x_1795_);
v___x_1797_ = v___x_1793_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1805_, lean_object* v_msg_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_toCold_1810_; lean_object* v_currRecDepth_1811_; lean_object* v_ref_1812_; uint16_t v_optionFlags_1813_; uint8_t v_suppressElabErrors_1814_; uint8_t v_isRecordingDeps_1815_; lean_object* v_ref_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_toCold_1810_ = lean_ctor_get(v___y_1807_, 0);
v_currRecDepth_1811_ = lean_ctor_get(v___y_1807_, 1);
v_ref_1812_ = lean_ctor_get(v___y_1807_, 2);
v_optionFlags_1813_ = lean_ctor_get_uint16(v___y_1807_, sizeof(void*)*3);
v_suppressElabErrors_1814_ = lean_ctor_get_uint8(v___y_1807_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1815_ = lean_ctor_get_uint8(v___y_1807_, sizeof(void*)*3 + 3);
v_ref_1816_ = l_Lean_replaceRef(v_ref_1805_, v_ref_1812_);
lean_inc(v_currRecDepth_1811_);
lean_inc_ref(v_toCold_1810_);
v___x_1817_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1817_, 0, v_toCold_1810_);
lean_ctor_set(v___x_1817_, 1, v_currRecDepth_1811_);
lean_ctor_set(v___x_1817_, 2, v_ref_1816_);
lean_ctor_set_uint16(v___x_1817_, sizeof(void*)*3, v_optionFlags_1813_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*3 + 2, v_suppressElabErrors_1814_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*3 + 3, v_isRecordingDeps_1815_);
v___x_1818_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1806_, v___x_1817_, v___y_1808_);
lean_dec_ref_known(v___x_1817_, 3);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1819_, lean_object* v_msg_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1819_, v_msg_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v_ref_1819_);
return v_res_1824_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1832_ = l_Lean_stringToMessageData(v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1837_);
v___x_1842_ = l_Lean_Syntax_isOfKind(v_x_1837_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1844_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1837_, v___x_1843_, v_a_1838_, v_a_1839_);
lean_dec(v_x_1837_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v_recovering_1848_; 
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = l_Lean_Syntax_getArg(v_x_1837_, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1848_ = l_Lean_Syntax_isOfKind(v___x_1846_, v___x_1847_);
if (v_recovering_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1850_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1837_, v___x_1849_, v_a_1838_, v_a_1839_);
lean_dec(v_x_1837_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v_xs_1853_; uint8_t v_recovering_1854_; lean_object* v___x_1855_; size_t v_sz_1856_; size_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1851_ = lean_unsigned_to_nat(1u);
v___x_1852_ = l_Lean_Syntax_getArg(v_x_1837_, v___x_1851_);
lean_dec(v_x_1837_);
v_xs_1853_ = l_Lean_Syntax_getArgs(v___x_1852_);
lean_dec(v___x_1852_);
v_recovering_1854_ = 0;
v___x_1855_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1853_);
lean_dec_ref(v_xs_1853_);
v_sz_1856_ = lean_array_size(v___x_1855_);
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1848_, v___x_1855_, v_sz_1856_, v___x_1857_, v_recovering_1854_, v___x_1858_, v_a_1838_, v_a_1839_);
lean_dec_ref(v___x_1855_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1870_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1870_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1870_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_snd_1864_; lean_object* v_items_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
v_snd_1864_ = lean_ctor_get(v_a_1860_, 1);
lean_inc(v_snd_1864_);
lean_dec(v_a_1860_);
v_items_1865_ = lean_ctor_get(v_snd_1864_, 5);
lean_inc_ref(v_items_1865_);
lean_dec(v_snd_1864_);
v___x_1866_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1865_);
lean_dec_ref(v_items_1865_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1866_);
v___x_1868_ = v___x_1862_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
v_a_1871_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1859_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1859_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lake_Toml_elabToml(v_x_1879_, v_a_1880_, v_a_1881_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1884_, lean_object* v_ref_1885_, lean_object* v_msg_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1885_, v_msg_1886_, v___y_1887_, v___y_1888_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1891_, lean_object* v_ref_1892_, lean_object* v_msg_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1891_, v_ref_1892_, v_msg_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v_ref_1892_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1899_, v___y_1900_, v___y_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1904_, lean_object* v_msg_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1904_, v_msg_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1909_;
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
