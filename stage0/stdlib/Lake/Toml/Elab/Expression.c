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
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
static const lean_closure_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdTable"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value),LEAN_SCALAR_PTR_LITERAL(204, 45, 156, 80, 41, 178, 181, 196)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed table syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_125_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_148_; lean_object* v_env_149_; lean_object* v_options_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_148_ = lean_st_ref_get(v___y_146_);
v_env_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc_ref(v_env_149_);
lean_dec(v___x_148_);
v_options_150_ = lean_ctor_get(v___y_145_, 2);
v___x_151_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2);
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_150_);
v___x_153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_153_, 0, v_env_149_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_152_);
lean_ctor_set(v___x_153_, 3, v_options_150_);
v___x_154_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_msgData_144_);
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
v_ref_165_ = lean_ctor_get(v___y_162_, 5);
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
lean_object* v_fileName_187_; lean_object* v_fileMap_188_; lean_object* v_options_189_; lean_object* v_currRecDepth_190_; lean_object* v_maxRecDepth_191_; lean_object* v_ref_192_; lean_object* v_currNamespace_193_; lean_object* v_openDecls_194_; lean_object* v_initHeartbeats_195_; lean_object* v_maxHeartbeats_196_; lean_object* v_quotContext_197_; lean_object* v_currMacroScope_198_; uint8_t v_diag_199_; lean_object* v_cancelTk_x3f_200_; uint8_t v_suppressElabErrors_201_; lean_object* v_inheritedTraceOptions_202_; lean_object* v_ref_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_fileName_187_ = lean_ctor_get(v___y_184_, 0);
v_fileMap_188_ = lean_ctor_get(v___y_184_, 1);
v_options_189_ = lean_ctor_get(v___y_184_, 2);
v_currRecDepth_190_ = lean_ctor_get(v___y_184_, 3);
v_maxRecDepth_191_ = lean_ctor_get(v___y_184_, 4);
v_ref_192_ = lean_ctor_get(v___y_184_, 5);
v_currNamespace_193_ = lean_ctor_get(v___y_184_, 6);
v_openDecls_194_ = lean_ctor_get(v___y_184_, 7);
v_initHeartbeats_195_ = lean_ctor_get(v___y_184_, 8);
v_maxHeartbeats_196_ = lean_ctor_get(v___y_184_, 9);
v_quotContext_197_ = lean_ctor_get(v___y_184_, 10);
v_currMacroScope_198_ = lean_ctor_get(v___y_184_, 11);
v_diag_199_ = lean_ctor_get_uint8(v___y_184_, sizeof(void*)*14);
v_cancelTk_x3f_200_ = lean_ctor_get(v___y_184_, 12);
v_suppressElabErrors_201_ = lean_ctor_get_uint8(v___y_184_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_202_ = lean_ctor_get(v___y_184_, 13);
v_ref_203_ = l_Lean_replaceRef(v_ref_181_, v_ref_192_);
lean_inc_ref(v_inheritedTraceOptions_202_);
lean_inc(v_cancelTk_x3f_200_);
lean_inc(v_currMacroScope_198_);
lean_inc(v_quotContext_197_);
lean_inc(v_maxHeartbeats_196_);
lean_inc(v_initHeartbeats_195_);
lean_inc(v_openDecls_194_);
lean_inc(v_currNamespace_193_);
lean_inc(v_maxRecDepth_191_);
lean_inc(v_currRecDepth_190_);
lean_inc_ref(v_options_189_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___x_204_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_204_, 0, v_fileName_187_);
lean_ctor_set(v___x_204_, 1, v_fileMap_188_);
lean_ctor_set(v___x_204_, 2, v_options_189_);
lean_ctor_set(v___x_204_, 3, v_currRecDepth_190_);
lean_ctor_set(v___x_204_, 4, v_maxRecDepth_191_);
lean_ctor_set(v___x_204_, 5, v_ref_203_);
lean_ctor_set(v___x_204_, 6, v_currNamespace_193_);
lean_ctor_set(v___x_204_, 7, v_openDecls_194_);
lean_ctor_set(v___x_204_, 8, v_initHeartbeats_195_);
lean_ctor_set(v___x_204_, 9, v_maxHeartbeats_196_);
lean_ctor_set(v___x_204_, 10, v_quotContext_197_);
lean_ctor_set(v___x_204_, 11, v_currMacroScope_198_);
lean_ctor_set(v___x_204_, 12, v_cancelTk_x3f_200_);
lean_ctor_set(v___x_204_, 13, v_inheritedTraceOptions_202_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*14, v_diag_199_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*14 + 1, v_suppressElabErrors_201_);
v___x_205_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_182_, v___x_204_, v___y_185_);
lean_dec_ref_known(v___x_204_, 14);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object* v_ref_206_, lean_object* v_msg_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_206_, v_msg_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v_ref_206_);
return v_res_212_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_215_ = l_Lean_stringToMessageData(v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_218_ = l_Lean_stringToMessageData(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_221_ = l_Lean_stringToMessageData(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object* v_as_222_, size_t v_i_223_, size_t v_stop_224_, lean_object* v_b_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_fst_231_; lean_object* v_snd_232_; uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_eq(v_i_223_, v_stop_224_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_array_uget_borrowed(v_as_222_, v_i_223_);
lean_inc(v___x_237_);
v___x_238_ = l_Lake_Toml_elabSimpleKey(v___x_237_, v___y_227_, v___y_228_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v_keyTys_240_; lean_object* v_arrKeyTys_241_; lean_object* v_arrParents_242_; lean_object* v_currArrKey_243_; lean_object* v_currKey_244_; lean_object* v_items_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v___x_238_, 1);
v_keyTys_240_ = lean_ctor_get(v___y_226_, 0);
v_arrKeyTys_241_ = lean_ctor_get(v___y_226_, 1);
v_arrParents_242_ = lean_ctor_get(v___y_226_, 2);
v_currArrKey_243_ = lean_ctor_get(v___y_226_, 3);
v_currKey_244_ = lean_ctor_get(v___y_226_, 4);
v_items_245_ = lean_ctor_get(v___y_226_, 5);
v___x_246_ = l_Lean_Name_str___override(v_b_225_, v_a_239_);
v___x_247_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_240_, v___x_246_);
if (lean_obj_tag(v___x_247_) == 1)
{
lean_object* v_val_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_278_; 
v_val_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_278_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_278_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_val_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_278_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
uint8_t v___x_252_; 
v___x_252_ = lean_unbox(v_val_248_);
if (v___x_252_ == 3)
{
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
v_fst_231_ = v___x_246_;
v_snd_232_ = v___y_226_;
goto v___jp_230_;
}
else
{
lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_253_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_254_ = lean_unbox(v_val_248_);
lean_dec(v_val_248_);
v___x_255_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_254_);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 3);
lean_ctor_set(v___x_250_, 0, v___x_255_);
v___x_257_ = v___x_250_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_277_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_258_ = l_Lean_MessageData_ofFormat(v___x_257_);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_253_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
lean_inc(v___x_246_);
v___x_262_ = l_Lean_MessageData_ofName(v___x_246_);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_237_, v___x_265_, v___y_226_, v___y_227_, v___y_228_);
lean_dec_ref(v___y_226_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v_snd_268_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
v_snd_268_ = lean_ctor_get(v_a_267_, 1);
lean_inc(v_snd_268_);
lean_dec(v_a_267_);
v_fst_231_ = v___x_246_;
v_snd_232_ = v_snd_268_;
goto v___jp_230_;
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v___x_246_);
v_a_269_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_266_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_266_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_288_; 
lean_inc_ref(v_items_245_);
lean_inc(v_currKey_244_);
lean_inc(v_currArrKey_243_);
lean_inc(v_arrParents_242_);
lean_inc(v_arrKeyTys_241_);
lean_inc(v_keyTys_240_);
lean_dec(v___x_247_);
v_isSharedCheck_288_ = !lean_is_exclusive(v___y_226_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; lean_object* v_unused_294_; 
v_unused_289_ = lean_ctor_get(v___y_226_, 5);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v___y_226_, 4);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v___y_226_, 3);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v___y_226_, 2);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v___y_226_, 1);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v___y_226_, 0);
lean_dec(v_unused_294_);
v___x_280_ = v___y_226_;
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
else
{
lean_dec(v___y_226_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_282_ = 3;
v___x_283_ = lean_box(v___x_282_);
lean_inc(v___x_246_);
v___x_284_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_246_, v___x_283_, v_keyTys_240_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_284_);
v___x_286_ = v___x_280_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_arrKeyTys_241_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_arrParents_242_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_currArrKey_243_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_currKey_244_);
lean_ctor_set(v_reuseFailAlloc_287_, 5, v_items_245_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
v_fst_231_ = v___x_246_;
v_snd_232_ = v___x_286_;
goto v___jp_230_;
}
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v___y_226_);
lean_dec(v_b_225_);
v_a_295_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_238_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_238_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_b_225_);
lean_ctor_set(v___x_303_, 1, v___y_226_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
v___jp_230_:
{
size_t v___x_233_; size_t v___x_234_; 
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_223_, v___x_233_);
v_i_223_ = v___x_234_;
v_b_225_ = v_fst_231_;
v___y_226_ = v_snd_232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object* v_as_305_, lean_object* v_i_306_, lean_object* v_stop_307_, lean_object* v_b_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
size_t v_i_boxed_313_; size_t v_stop_boxed_314_; lean_object* v_res_315_; 
v_i_boxed_313_ = lean_unbox_usize(v_i_306_);
lean_dec(v_i_306_);
v_stop_boxed_314_ = lean_unbox_usize(v_stop_307_);
lean_dec(v_stop_307_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_305_, v_i_boxed_313_, v_stop_boxed_314_, v_b_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec_ref(v_as_305_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object* v_ks_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_currKey_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_currKey_321_ = lean_ctor_get(v_a_317_, 4);
lean_inc(v_currKey_321_);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_array_get_size(v_ks_316_);
v___x_324_ = lean_nat_dec_lt(v___x_322_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_currKey_321_);
lean_ctor_set(v___x_325_, 1, v_a_317_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
else
{
uint8_t v___x_327_; 
v___x_327_ = lean_nat_dec_le(v___x_323_, v___x_323_);
if (v___x_327_ == 0)
{
if (v___x_324_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_currKey_321_);
lean_ctor_set(v___x_328_, 1, v_a_317_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
else
{
size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((size_t)0ULL);
v___x_331_ = lean_usize_of_nat(v___x_323_);
v___x_332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_316_, v___x_330_, v___x_331_, v_currKey_321_, v_a_317_, v_a_318_, v_a_319_);
return v___x_332_;
}
}
else
{
size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((size_t)0ULL);
v___x_334_ = lean_usize_of_nat(v___x_323_);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_316_, v___x_333_, v___x_334_, v_currKey_321_, v_a_317_, v_a_318_, v_a_319_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object* v_ks_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec_ref(v_ks_336_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_342_, lean_object* v_ref_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_343_, v_msg_344_, v___y_345_, v___y_346_, v___y_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_350_, lean_object* v_ref_351_, lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_350_, v_ref_351_, v_msg_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v_ref_351_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_358_, lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_359_, v___y_361_, v___y_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_365_, lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_365_, v_msg_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_372_, lean_object* v_as_373_, size_t v_i_374_, size_t v_stop_375_, lean_object* v_b_376_){
_start:
{
lean_object* v___y_378_; uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_eq(v_i_374_, v_stop_375_);
if (v___x_382_ == 0)
{
lean_object* v_fst_383_; uint8_t v___x_384_; 
v_fst_383_ = lean_ctor_get(v_b_376_, 0);
v___x_384_ = lean_unbox(v_fst_383_);
if (v___x_384_ == 0)
{
lean_object* v_snd_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_snd_385_ = lean_ctor_get(v_b_376_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v_b_376_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v_b_376_, 0);
lean_dec(v_unused_394_);
v___x_387_ = v_b_376_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snd_385_);
lean_dec(v_b_376_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_box(v___x_372_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_snd_385_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
v___y_378_ = v___x_391_;
goto v___jp_377_;
}
}
}
else
{
lean_object* v_snd_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_405_; 
v_snd_395_ = lean_ctor_get(v_b_376_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_b_376_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v_b_376_, 0);
lean_dec(v_unused_406_);
v___x_397_ = v_b_376_;
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_snd_395_);
lean_dec(v_b_376_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_399_ = lean_array_uget_borrowed(v_as_373_, v_i_374_);
lean_inc(v___x_399_);
v___x_400_ = lean_array_push(v_snd_395_, v___x_399_);
v___x_401_ = lean_box(v___x_382_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_400_);
lean_ctor_set(v___x_397_, 0, v___x_401_);
v___x_403_ = v___x_397_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_400_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
v___y_378_ = v___x_403_;
goto v___jp_377_;
}
}
}
}
else
{
return v_b_376_;
}
v___jp_377_:
{
size_t v___x_379_; size_t v___x_380_; 
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_374_, v___x_379_);
v_i_374_ = v___x_380_;
v_b_376_ = v___y_378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_407_, lean_object* v_as_408_, lean_object* v_i_409_, lean_object* v_stop_410_, lean_object* v_b_411_){
_start:
{
uint8_t v___x_2932__boxed_412_; size_t v_i_boxed_413_; size_t v_stop_boxed_414_; lean_object* v_res_415_; 
v___x_2932__boxed_412_ = lean_unbox(v___x_407_);
v_i_boxed_413_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_stop_boxed_414_ = lean_unbox_usize(v_stop_410_);
lean_dec(v_stop_410_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2932__boxed_412_, v_as_408_, v_i_boxed_413_, v_stop_boxed_414_, v_b_411_);
lean_dec_ref(v_as_408_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_423_, size_t v_i_424_, lean_object* v_bs_425_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = lean_usize_dec_lt(v_i_424_, v_sz_423_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v_bs_425_);
return v___x_427_;
}
else
{
lean_object* v_v_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_v_428_ = lean_array_uget(v_bs_425_, v_i_424_);
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_428_);
v___x_430_ = l_Lean_Syntax_isOfKind(v_v_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec(v_v_428_);
lean_dec_ref(v_bs_425_);
v___x_431_ = lean_box(0);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v_bs_x27_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_432_ = lean_unsigned_to_nat(0u);
v_bs_x27_433_ = lean_array_uset(v_bs_425_, v_i_424_, v___x_432_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_424_, v___x_434_);
v___x_436_ = lean_array_uset(v_bs_x27_433_, v_i_424_, v_v_428_);
v_i_424_ = v___x_435_;
v_bs_425_ = v___x_436_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_438_, lean_object* v_i_439_, lean_object* v_bs_440_){
_start:
{
size_t v_sz_boxed_441_; size_t v_i_boxed_442_; lean_object* v_res_443_; 
v_sz_boxed_441_ = lean_unbox_usize(v_sz_438_);
lean_dec(v_sz_438_);
v_i_boxed_442_ = lean_unbox_usize(v_i_439_);
lean_dec(v_i_439_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_441_, v_i_boxed_442_, v_bs_440_);
return v_res_443_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_451_ = l_Lean_stringToMessageData(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_462_);
v___x_468_ = l_Lean_Syntax_isOfKind(v_kv_462_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_470_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_462_, v___x_469_, v_a_463_, v_a_464_, v_a_465_);
lean_dec_ref(v_a_463_);
lean_dec(v_kv_462_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = l_Lean_Syntax_getArg(v_kv_462_, v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_472_);
v___x_474_ = l_Lean_Syntax_isOfKind(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_kv_462_);
v___x_475_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_476_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_472_, v___x_475_, v_a_463_, v_a_464_, v_a_465_);
lean_dec_ref(v_a_463_);
lean_dec(v___x_472_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; lean_object* v_v_478_; lean_object* v___y_480_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_477_ = lean_unsigned_to_nat(2u);
v_v_478_ = l_Lean_Syntax_getArg(v_kv_462_, v___x_477_);
lean_dec(v_kv_462_);
v___x_586_ = l_Lean_Syntax_getArg(v___x_472_, v___x_471_);
v___x_587_ = l_Lean_Syntax_getArgs(v___x_586_);
lean_dec(v___x_586_);
v___x_588_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_589_ = lean_array_get_size(v___x_587_);
v___x_590_ = lean_nat_dec_lt(v___x_471_, v___x_589_);
if (v___x_590_ == 0)
{
lean_dec_ref(v___x_587_);
v___y_480_ = v___x_588_;
goto v___jp_479_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; lean_object* v_snd_596_; 
v___x_591_ = lean_box(v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_588_);
v___x_593_ = ((size_t)0ULL);
v___x_594_ = lean_usize_of_nat(v___x_589_);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_474_, v___x_587_, v___x_593_, v___x_594_, v___x_592_);
lean_dec_ref(v___x_587_);
v_snd_596_ = lean_ctor_get(v___x_595_, 1);
lean_inc(v_snd_596_);
lean_dec_ref(v___x_595_);
v___y_480_ = v_snd_596_;
goto v___jp_479_;
}
v___jp_479_:
{
size_t v_sz_481_; size_t v___x_482_; lean_object* v___x_483_; 
v_sz_481_ = lean_array_size(v___y_480_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_481_, v___x_482_, v___y_480_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_v_478_);
v___x_484_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_485_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_472_, v___x_484_, v_a_463_, v_a_464_, v_a_465_);
lean_dec_ref(v_a_463_);
lean_dec(v___x_472_);
return v___x_485_;
}
else
{
lean_object* v_val_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_tailKeyStx_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_val_486_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v___x_483_, 1);
v___x_487_ = lean_box(0);
v___x_488_ = lean_array_get_size(v_val_486_);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_sub(v___x_488_, v___x_489_);
v_tailKeyStx_491_ = lean_array_get(v___x_487_, v_val_486_, v___x_490_);
lean_dec(v___x_490_);
v___x_492_ = lean_array_pop(v_val_486_);
v___x_493_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_492_, v_a_463_, v_a_464_, v_a_465_);
lean_dec_ref(v___x_492_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v_fst_495_; lean_object* v_snd_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_577_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v_fst_495_ = lean_ctor_get(v_a_494_, 0);
v_snd_496_ = lean_ctor_get(v_a_494_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_a_494_);
if (v_isSharedCheck_577_ == 0)
{
v___x_498_ = v_a_494_;
v_isShared_499_ = v_isSharedCheck_577_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_snd_496_);
lean_inc(v_fst_495_);
lean_dec(v_a_494_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_577_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; 
lean_inc(v_tailKeyStx_491_);
v___x_500_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_491_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v_keyTys_502_; lean_object* v_arrKeyTys_503_; lean_object* v_arrParents_504_; lean_object* v_currArrKey_505_; lean_object* v_currKey_506_; lean_object* v_items_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v_keyTys_502_ = lean_ctor_get(v_snd_496_, 0);
v_arrKeyTys_503_ = lean_ctor_get(v_snd_496_, 1);
v_arrParents_504_ = lean_ctor_get(v_snd_496_, 2);
v_currArrKey_505_ = lean_ctor_get(v_snd_496_, 3);
v_currKey_506_ = lean_ctor_get(v_snd_496_, 4);
v_items_507_ = lean_ctor_get(v_snd_496_, 5);
v___x_508_ = l_Lean_Name_str___override(v_fst_495_, v_a_501_);
v___x_509_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_502_, v___x_508_);
if (lean_obj_tag(v___x_509_) == 1)
{
lean_object* v_val_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_529_; 
lean_del_object(v___x_498_);
lean_dec(v_v_478_);
lean_dec(v___x_472_);
v_val_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_529_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_529_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_val_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_529_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_514_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_515_ = lean_unbox(v_val_510_);
lean_dec(v_val_510_);
v___x_516_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_515_);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 3);
lean_ctor_set(v___x_512_, 0, v___x_516_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_528_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_519_ = l_Lean_MessageData_ofFormat(v___x_518_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_514_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_MessageData_ofName(v___x_508_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_491_, v___x_526_, v_snd_496_, v_a_464_, v_a_465_);
lean_dec(v_snd_496_);
lean_dec(v_tailKeyStx_491_);
return v___x_527_;
}
}
}
else
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_562_; 
lean_inc_ref(v_items_507_);
lean_inc(v_currKey_506_);
lean_inc(v_currArrKey_505_);
lean_inc(v_arrParents_504_);
lean_inc(v_arrKeyTys_503_);
lean_inc(v_keyTys_502_);
lean_dec(v___x_509_);
lean_dec(v_tailKeyStx_491_);
v_isSharedCheck_562_ = !lean_is_exclusive(v_snd_496_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; 
v_unused_563_ = lean_ctor_get(v_snd_496_, 5);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_snd_496_, 4);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_snd_496_, 3);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_snd_496_, 2);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_snd_496_, 1);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_snd_496_, 0);
lean_dec(v_unused_568_);
v___x_531_ = v_snd_496_;
v_isShared_532_ = v_isSharedCheck_562_;
goto v_resetjp_530_;
}
else
{
lean_dec(v_snd_496_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_562_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lake_Toml_elabVal(v_v_478_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_553_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_553_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_553_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_553_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_538_ = lean_box(0);
v___x_539_ = 0;
v___x_540_ = lean_box(v___x_539_);
lean_inc(v___x_508_);
v___x_541_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_508_, v___x_540_, v_keyTys_502_);
v___x_542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_542_, 0, v___x_472_);
lean_ctor_set(v___x_542_, 1, v___x_508_);
lean_ctor_set(v___x_542_, 2, v_a_534_);
v___x_543_ = lean_array_push(v_items_507_, v___x_542_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 5, v___x_543_);
lean_ctor_set(v___x_531_, 0, v___x_541_);
v___x_545_ = v___x_531_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_arrKeyTys_503_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_arrParents_504_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_currArrKey_505_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_currKey_506_);
lean_ctor_set(v_reuseFailAlloc_552_, 5, v___x_543_);
v___x_545_ = v_reuseFailAlloc_552_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_545_);
lean_ctor_set(v___x_498_, 0, v___x_538_);
v___x_547_ = v___x_498_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_545_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_547_);
v___x_549_ = v___x_536_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
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
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_del_object(v___x_531_);
lean_dec(v___x_508_);
lean_dec_ref(v_items_507_);
lean_dec(v_currKey_506_);
lean_dec(v_currArrKey_505_);
lean_dec(v_arrParents_504_);
lean_dec(v_arrKeyTys_503_);
lean_dec(v_keyTys_502_);
lean_del_object(v___x_498_);
lean_dec(v___x_472_);
v_a_554_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_533_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_533_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_del_object(v___x_498_);
lean_dec(v_snd_496_);
lean_dec(v_fst_495_);
lean_dec(v_tailKeyStx_491_);
lean_dec(v_v_478_);
lean_dec(v___x_472_);
v_a_569_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_500_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_500_);
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
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_tailKeyStx_491_);
lean_dec(v_v_478_);
lean_dec(v___x_472_);
v_a_578_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_493_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_493_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_597_, v_a_598_, v_a_599_, v_a_600_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
return v_res_602_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_605_ = l_Lean_stringToMessageData(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_606_, size_t v_i_607_, size_t v_stop_608_, lean_object* v_b_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; uint8_t v___x_620_; 
v___x_620_ = lean_usize_dec_eq(v_i_607_, v_stop_608_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_array_uget_borrowed(v_as_606_, v_i_607_);
lean_inc(v___x_621_);
v___x_622_ = l_Lake_Toml_elabSimpleKey(v___x_621_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v_keyTys_624_; lean_object* v_arrKeyTys_625_; lean_object* v_arrParents_626_; lean_object* v_currArrKey_627_; lean_object* v_currKey_628_; lean_object* v_items_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v_keyTys_624_ = lean_ctor_get(v___y_610_, 0);
v_arrKeyTys_625_ = lean_ctor_get(v___y_610_, 1);
v_arrParents_626_ = lean_ctor_get(v___y_610_, 2);
v_currArrKey_627_ = lean_ctor_get(v___y_610_, 3);
v_currKey_628_ = lean_ctor_get(v___y_610_, 4);
v_items_629_ = lean_ctor_get(v___y_610_, 5);
v___x_630_ = l_Lean_Name_str___override(v_b_609_, v_a_623_);
v___x_631_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_624_, v___x_630_);
if (lean_obj_tag(v___x_631_) == 1)
{
lean_object* v_val_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_693_; 
v_val_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_693_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_693_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_val_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_693_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; 
v___x_636_ = lean_unbox(v_val_632_);
switch(v___x_636_)
{
case 2:
{
lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_661_; 
lean_inc_ref(v_items_629_);
lean_inc(v_currKey_628_);
lean_inc(v_arrParents_626_);
lean_inc(v_arrKeyTys_625_);
lean_del_object(v___x_634_);
lean_dec(v_val_632_);
v_isSharedCheck_661_ = !lean_is_exclusive(v___y_610_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; lean_object* v_unused_663_; lean_object* v_unused_664_; lean_object* v_unused_665_; lean_object* v_unused_666_; lean_object* v_unused_667_; 
v_unused_662_ = lean_ctor_get(v___y_610_, 5);
lean_dec(v_unused_662_);
v_unused_663_ = lean_ctor_get(v___y_610_, 4);
lean_dec(v_unused_663_);
v_unused_664_ = lean_ctor_get(v___y_610_, 3);
lean_dec(v_unused_664_);
v_unused_665_ = lean_ctor_get(v___y_610_, 2);
lean_dec(v_unused_665_);
v_unused_666_ = lean_ctor_get(v___y_610_, 1);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v___y_610_, 0);
lean_dec(v_unused_667_);
v___x_638_ = v___y_610_;
v_isShared_639_ = v_isSharedCheck_661_;
goto v_resetjp_637_;
}
else
{
lean_dec(v___y_610_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_661_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_625_, v___x_630_);
if (lean_obj_tag(v___x_640_) == 1)
{
lean_object* v_val_641_; lean_object* v___x_643_; 
v_val_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v___x_640_, 1);
lean_inc(v___x_630_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 3, v___x_630_);
lean_ctor_set(v___x_638_, 0, v_val_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_val_641_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_arrKeyTys_625_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_arrParents_626_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_currKey_628_);
lean_ctor_set(v_reuseFailAlloc_644_, 5, v_items_629_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v_fst_615_ = v___x_630_;
v_snd_616_ = v___x_643_;
goto v___jp_614_;
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec(v___x_640_);
lean_del_object(v___x_638_);
lean_dec_ref(v_items_629_);
lean_dec(v_currKey_628_);
lean_dec(v_arrParents_626_);
lean_dec(v_arrKeyTys_625_);
v___x_645_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_630_);
v___x_646_ = l_Lean_MessageData_ofName(v___x_630_);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_649_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v_snd_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v_snd_652_ = lean_ctor_get(v_a_651_, 1);
lean_inc(v_snd_652_);
lean_dec(v_a_651_);
v_fst_615_ = v___x_630_;
v_snd_616_ = v_snd_652_;
goto v___jp_614_;
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v___x_630_);
v_a_653_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_650_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_650_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
case 1:
{
lean_del_object(v___x_634_);
lean_dec(v_val_632_);
v_fst_615_ = v___x_630_;
v_snd_616_ = v___y_610_;
goto v___jp_614_;
}
case 4:
{
lean_del_object(v___x_634_);
lean_dec(v_val_632_);
v_fst_615_ = v___x_630_;
v_snd_616_ = v___y_610_;
goto v___jp_614_;
}
case 3:
{
lean_del_object(v___x_634_);
lean_dec(v_val_632_);
v_fst_615_ = v___x_630_;
v_snd_616_ = v___y_610_;
goto v___jp_614_;
}
default: 
{
lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_668_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_669_ = lean_unbox(v_val_632_);
lean_dec(v_val_632_);
v___x_670_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_669_);
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 3);
lean_ctor_set(v___x_634_, 0, v___x_670_);
v___x_672_ = v___x_634_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_692_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_673_ = l_Lean_MessageData_ofFormat(v___x_672_);
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_668_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
lean_inc(v___x_630_);
v___x_677_ = l_Lean_MessageData_ofName(v___x_630_);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_621_, v___x_680_, v___y_610_, v___y_611_, v___y_612_);
lean_dec_ref(v___y_610_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v_snd_683_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v_snd_683_ = lean_ctor_get(v_a_682_, 1);
lean_inc(v_snd_683_);
lean_dec(v_a_682_);
v_fst_615_ = v___x_630_;
v_snd_616_ = v_snd_683_;
goto v___jp_614_;
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v___x_630_);
v_a_684_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_681_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_681_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
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
lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_703_; 
lean_inc_ref(v_items_629_);
lean_inc(v_currKey_628_);
lean_inc(v_currArrKey_627_);
lean_inc(v_arrParents_626_);
lean_inc(v_arrKeyTys_625_);
lean_inc(v_keyTys_624_);
lean_dec(v___x_631_);
v_isSharedCheck_703_ = !lean_is_exclusive(v___y_610_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_704_ = lean_ctor_get(v___y_610_, 5);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v___y_610_, 4);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v___y_610_, 3);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v___y_610_, 2);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v___y_610_, 1);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v___y_610_, 0);
lean_dec(v_unused_709_);
v___x_695_ = v___y_610_;
v_isShared_696_ = v_isSharedCheck_703_;
goto v_resetjp_694_;
}
else
{
lean_dec(v___y_610_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_703_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_697_ = 4;
v___x_698_ = lean_box(v___x_697_);
lean_inc(v___x_630_);
v___x_699_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_630_, v___x_698_, v_keyTys_624_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_699_);
v___x_701_ = v___x_695_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_arrKeyTys_625_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_arrParents_626_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_currArrKey_627_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_currKey_628_);
lean_ctor_set(v_reuseFailAlloc_702_, 5, v_items_629_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v_fst_615_ = v___x_630_;
v_snd_616_ = v___x_701_;
goto v___jp_614_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v___y_610_);
lean_dec(v_b_609_);
v_a_710_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_622_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_622_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_b_609_);
lean_ctor_set(v___x_718_, 1, v___y_610_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
v___jp_614_:
{
size_t v___x_617_; size_t v___x_618_; 
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_add(v_i_607_, v___x_617_);
v_i_607_ = v___x_618_;
v_b_609_ = v_fst_615_;
v___y_610_ = v_snd_616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_720_, lean_object* v_i_721_, lean_object* v_stop_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
size_t v_i_boxed_728_; size_t v_stop_boxed_729_; lean_object* v_res_730_; 
v_i_boxed_728_ = lean_unbox_usize(v_i_721_);
lean_dec(v_i_721_);
v_stop_boxed_729_ = lean_unbox_usize(v_stop_722_);
lean_dec(v_stop_722_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_720_, v_i_boxed_728_, v_stop_boxed_729_, v_b_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec_ref(v_as_720_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_731_, lean_object* v_k_732_){
_start:
{
if (lean_obj_tag(v_t_731_) == 0)
{
lean_object* v_k_733_; lean_object* v_v_734_; lean_object* v_l_735_; lean_object* v_r_736_; uint8_t v___x_737_; 
v_k_733_ = lean_ctor_get(v_t_731_, 1);
v_v_734_ = lean_ctor_get(v_t_731_, 2);
v_l_735_ = lean_ctor_get(v_t_731_, 3);
v_r_736_ = lean_ctor_get(v_t_731_, 4);
v___x_737_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_732_, v_k_733_);
switch(v___x_737_)
{
case 0:
{
v_t_731_ = v_l_735_;
goto _start;
}
case 1:
{
lean_object* v___x_739_; 
lean_inc(v_v_734_);
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v_v_734_);
return v___x_739_;
}
default: 
{
v_t_731_ = v_r_736_;
goto _start;
}
}
}
else
{
lean_object* v___x_741_; 
v___x_741_ = lean_box(0);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_742_, lean_object* v_k_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_742_, v_k_743_);
lean_dec(v_k_743_);
lean_dec(v_t_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_keyTys_750_; lean_object* v_arrKeyTys_751_; lean_object* v_arrParents_752_; lean_object* v_currArrKey_753_; lean_object* v_currKey_754_; lean_object* v_items_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_783_; 
v_keyTys_750_ = lean_ctor_get(v_a_746_, 0);
v_arrKeyTys_751_ = lean_ctor_get(v_a_746_, 1);
v_arrParents_752_ = lean_ctor_get(v_a_746_, 2);
v_currArrKey_753_ = lean_ctor_get(v_a_746_, 3);
v_currKey_754_ = lean_ctor_get(v_a_746_, 4);
v_items_755_ = lean_ctor_get(v_a_746_, 5);
v_isSharedCheck_783_ = !lean_is_exclusive(v_a_746_);
if (v_isSharedCheck_783_ == 0)
{
v___x_757_ = v_a_746_;
v_isShared_758_ = v_isSharedCheck_783_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_items_755_);
lean_inc(v_currKey_754_);
lean_inc(v_currArrKey_753_);
lean_inc(v_arrParents_752_);
lean_inc(v_arrKeyTys_751_);
lean_inc(v_keyTys_750_);
lean_dec(v_a_746_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_783_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_arrKeyTys_759_; lean_object* v___x_760_; lean_object* v___y_762_; lean_object* v___x_780_; 
v_arrKeyTys_759_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_753_, v_keyTys_750_, v_arrKeyTys_751_);
v___x_760_ = lean_box(0);
v___x_780_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_759_, v___x_760_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_781_; 
v___x_781_ = lean_box(1);
v___y_762_ = v___x_781_;
goto v___jp_761_;
}
else
{
lean_object* v_val_782_; 
v_val_782_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v___x_780_, 1);
v___y_762_ = v_val_782_;
goto v___jp_761_;
}
v___jp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 3, v___x_760_);
lean_ctor_set(v___x_757_, 1, v_arrKeyTys_759_);
lean_ctor_set(v___x_757_, 0, v___y_762_);
v___x_764_ = v___x_757_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___y_762_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_arrKeyTys_759_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_arrParents_752_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_currKey_754_);
lean_ctor_set(v_reuseFailAlloc_779_, 5, v_items_755_);
v___x_764_ = v_reuseFailAlloc_779_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_array_get_size(v_ks_745_);
v___x_767_ = lean_nat_dec_lt(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_760_);
lean_ctor_set(v___x_768_, 1, v___x_764_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = lean_nat_dec_le(v___x_766_, v___x_766_);
if (v___x_770_ == 0)
{
if (v___x_767_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_760_);
lean_ctor_set(v___x_771_, 1, v___x_764_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
else
{
size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
v___x_773_ = ((size_t)0ULL);
v___x_774_ = lean_usize_of_nat(v___x_766_);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_745_, v___x_773_, v___x_774_, v___x_760_, v___x_764_, v_a_747_, v_a_748_);
return v___x_775_;
}
}
else
{
size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
v___x_776_ = ((size_t)0ULL);
v___x_777_ = lean_usize_of_nat(v___x_766_);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_745_, v___x_776_, v___x_777_, v___x_760_, v___x_764_, v_a_747_, v_a_748_);
return v___x_778_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec_ref(v_ks_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_790_, lean_object* v_t_791_, lean_object* v_k_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_791_, v_k_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_794_, lean_object* v_t_795_, lean_object* v_k_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_794_, v_t_795_, v_k_796_);
lean_dec(v_k_796_);
lean_dec(v_t_795_);
return v_res_797_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
v___x_800_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4));
v___x_808_ = l_Lean_stringToMessageData(v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___y_815_; lean_object* v_keyTys_816_; lean_object* v_arrKeyTys_817_; lean_object* v_arrParents_818_; lean_object* v_currArrKey_819_; lean_object* v_items_820_; lean_object* v_fileName_832_; lean_object* v_fileMap_833_; lean_object* v_options_834_; lean_object* v_currRecDepth_835_; lean_object* v_maxRecDepth_836_; lean_object* v_ref_837_; lean_object* v_currNamespace_838_; lean_object* v_openDecls_839_; lean_object* v_initHeartbeats_840_; lean_object* v_maxHeartbeats_841_; lean_object* v_quotContext_842_; lean_object* v_currMacroScope_843_; uint8_t v_diag_844_; lean_object* v_cancelTk_x3f_845_; uint8_t v_suppressElabErrors_846_; lean_object* v_inheritedTraceOptions_847_; lean_object* v___x_848_; uint8_t v___x_849_; lean_object* v_ref_850_; lean_object* v___x_851_; 
v_fileName_832_ = lean_ctor_get(v_a_811_, 0);
v_fileMap_833_ = lean_ctor_get(v_a_811_, 1);
v_options_834_ = lean_ctor_get(v_a_811_, 2);
v_currRecDepth_835_ = lean_ctor_get(v_a_811_, 3);
v_maxRecDepth_836_ = lean_ctor_get(v_a_811_, 4);
v_ref_837_ = lean_ctor_get(v_a_811_, 5);
v_currNamespace_838_ = lean_ctor_get(v_a_811_, 6);
v_openDecls_839_ = lean_ctor_get(v_a_811_, 7);
v_initHeartbeats_840_ = lean_ctor_get(v_a_811_, 8);
v_maxHeartbeats_841_ = lean_ctor_get(v_a_811_, 9);
v_quotContext_842_ = lean_ctor_get(v_a_811_, 10);
v_currMacroScope_843_ = lean_ctor_get(v_a_811_, 11);
v_diag_844_ = lean_ctor_get_uint8(v_a_811_, sizeof(void*)*14);
v_cancelTk_x3f_845_ = lean_ctor_get(v_a_811_, 12);
v_suppressElabErrors_846_ = lean_ctor_get_uint8(v_a_811_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_847_ = lean_ctor_get(v_a_811_, 13);
v___x_848_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_809_);
v___x_849_ = l_Lean_Syntax_isOfKind(v_x_809_, v___x_848_);
v_ref_850_ = l_Lean_replaceRef(v_x_809_, v_ref_837_);
lean_inc_ref(v_inheritedTraceOptions_847_);
lean_inc(v_cancelTk_x3f_845_);
lean_inc(v_currMacroScope_843_);
lean_inc(v_quotContext_842_);
lean_inc(v_maxHeartbeats_841_);
lean_inc(v_initHeartbeats_840_);
lean_inc(v_openDecls_839_);
lean_inc(v_currNamespace_838_);
lean_inc(v_maxRecDepth_836_);
lean_inc(v_currRecDepth_835_);
lean_inc_ref(v_options_834_);
lean_inc_ref(v_fileMap_833_);
lean_inc_ref(v_fileName_832_);
v___x_851_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_851_, 0, v_fileName_832_);
lean_ctor_set(v___x_851_, 1, v_fileMap_833_);
lean_ctor_set(v___x_851_, 2, v_options_834_);
lean_ctor_set(v___x_851_, 3, v_currRecDepth_835_);
lean_ctor_set(v___x_851_, 4, v_maxRecDepth_836_);
lean_ctor_set(v___x_851_, 5, v_ref_850_);
lean_ctor_set(v___x_851_, 6, v_currNamespace_838_);
lean_ctor_set(v___x_851_, 7, v_openDecls_839_);
lean_ctor_set(v___x_851_, 8, v_initHeartbeats_840_);
lean_ctor_set(v___x_851_, 9, v_maxHeartbeats_841_);
lean_ctor_set(v___x_851_, 10, v_quotContext_842_);
lean_ctor_set(v___x_851_, 11, v_currMacroScope_843_);
lean_ctor_set(v___x_851_, 12, v_cancelTk_x3f_845_);
lean_ctor_set(v___x_851_, 13, v_inheritedTraceOptions_847_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*14, v_diag_844_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*14 + 1, v_suppressElabErrors_846_);
if (v___x_849_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5);
v___x_853_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_809_, v___x_852_, v_a_810_, v___x_851_, v_a_812_);
lean_dec_ref_known(v___x_851_, 14);
lean_dec_ref(v_a_810_);
lean_dec(v_x_809_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___y_857_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = l_Lean_Syntax_getArg(v_x_809_, v___x_854_);
v___x_925_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_855_);
v___x_926_ = l_Lean_Syntax_isOfKind(v___x_855_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v_x_809_);
v___x_927_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_928_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_855_, v___x_927_, v_a_810_, v___x_851_, v_a_812_);
lean_dec_ref_known(v___x_851_, 14);
lean_dec_ref(v_a_810_);
lean_dec(v___x_855_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = l_Lean_Syntax_getArg(v___x_855_, v___x_929_);
v___x_931_ = l_Lean_Syntax_getArgs(v___x_930_);
lean_dec(v___x_930_);
v___x_932_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_933_ = lean_array_get_size(v___x_931_);
v___x_934_ = lean_nat_dec_lt(v___x_929_, v___x_933_);
if (v___x_934_ == 0)
{
lean_dec_ref(v___x_931_);
v___y_857_ = v___x_932_;
goto v___jp_856_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; size_t v___x_937_; size_t v___x_938_; lean_object* v___x_939_; lean_object* v_snd_940_; 
v___x_935_ = lean_box(v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_932_);
v___x_937_ = ((size_t)0ULL);
v___x_938_ = lean_usize_of_nat(v___x_933_);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_926_, v___x_931_, v___x_937_, v___x_938_, v___x_936_);
lean_dec_ref(v___x_931_);
v_snd_940_ = lean_ctor_get(v___x_939_, 1);
lean_inc(v_snd_940_);
lean_dec_ref(v___x_939_);
v___y_857_ = v_snd_940_;
goto v___jp_856_;
}
}
v___jp_856_:
{
size_t v_sz_858_; size_t v___x_859_; lean_object* v___x_860_; 
v_sz_858_ = lean_array_size(v___y_857_);
v___x_859_ = ((size_t)0ULL);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_858_, v___x_859_, v___y_857_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec(v_x_809_);
v___x_861_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_862_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_855_, v___x_861_, v_a_810_, v___x_851_, v_a_812_);
lean_dec_ref_known(v___x_851_, 14);
lean_dec_ref(v_a_810_);
lean_dec(v___x_855_);
return v___x_862_;
}
else
{
lean_object* v_val_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_tailKey_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec(v___x_855_);
v_val_863_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v___x_860_, 1);
v___x_864_ = lean_box(0);
v___x_865_ = lean_array_get_size(v_val_863_);
v___x_866_ = lean_nat_sub(v___x_865_, v___x_854_);
v_tailKey_867_ = lean_array_get(v___x_864_, v_val_863_, v___x_866_);
lean_dec(v___x_866_);
v___x_868_ = lean_array_pop(v_val_863_);
v___x_869_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_868_, v_a_810_, v___x_851_, v_a_812_);
lean_dec_ref(v___x_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_916_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 1);
v_fst_871_ = lean_ctor_get(v_a_870_, 0);
v_snd_872_ = lean_ctor_get(v_a_870_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_a_870_);
if (v_isSharedCheck_916_ == 0)
{
v___x_874_ = v_a_870_;
v_isShared_875_ = v_isSharedCheck_916_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_snd_872_);
lean_inc(v_fst_871_);
lean_dec(v_a_870_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_916_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; 
lean_inc(v_tailKey_867_);
v___x_876_ = l_Lake_Toml_elabSimpleKey(v_tailKey_867_, v___x_851_, v_a_812_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v_keyTys_878_; lean_object* v_arrKeyTys_879_; lean_object* v_arrParents_880_; lean_object* v_currArrKey_881_; lean_object* v_items_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v_keyTys_878_ = lean_ctor_get(v_snd_872_, 0);
v_arrKeyTys_879_ = lean_ctor_get(v_snd_872_, 1);
v_arrParents_880_ = lean_ctor_get(v_snd_872_, 2);
v_currArrKey_881_ = lean_ctor_get(v_snd_872_, 3);
v_items_882_ = lean_ctor_get(v_snd_872_, 5);
v___x_883_ = l_Lean_Name_str___override(v_fst_871_, v_a_877_);
v___x_884_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_878_, v___x_883_);
if (lean_obj_tag(v___x_884_) == 1)
{
lean_object* v_val_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_907_; 
v_val_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_907_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_907_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_val_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_907_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
uint8_t v___x_889_; 
v___x_889_ = lean_unbox(v_val_885_);
if (v___x_889_ == 4)
{
lean_inc_ref(v_items_882_);
lean_inc(v_currArrKey_881_);
lean_inc(v_arrParents_880_);
lean_inc(v_arrKeyTys_879_);
lean_inc(v_keyTys_878_);
lean_del_object(v___x_887_);
lean_dec(v_val_885_);
lean_del_object(v___x_874_);
lean_dec(v_snd_872_);
lean_dec(v_tailKey_867_);
lean_dec_ref_known(v___x_851_, 14);
v___y_815_ = v___x_883_;
v_keyTys_816_ = v_keyTys_878_;
v_arrKeyTys_817_ = v_arrKeyTys_879_;
v_arrParents_818_ = v_arrParents_880_;
v_currArrKey_819_ = v_currArrKey_881_;
v_items_820_ = v_items_882_;
goto v___jp_814_;
}
else
{
lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
lean_dec(v_x_809_);
v___x_890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_891_ = lean_unbox(v_val_885_);
lean_dec(v_val_885_);
v___x_892_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_891_);
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 3);
lean_ctor_set(v___x_887_, 0, v___x_892_);
v___x_894_ = v___x_887_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_906_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = l_Lean_MessageData_ofFormat(v___x_894_);
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 7);
lean_ctor_set(v___x_874_, 1, v___x_895_);
lean_ctor_set(v___x_874_, 0, v___x_890_);
v___x_897_ = v___x_874_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_905_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_898_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_MessageData_ofName(v___x_883_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_867_, v___x_903_, v_snd_872_, v___x_851_, v_a_812_);
lean_dec_ref_known(v___x_851_, 14);
lean_dec(v_snd_872_);
lean_dec(v_tailKey_867_);
return v___x_904_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_882_);
lean_inc(v_currArrKey_881_);
lean_inc(v_arrParents_880_);
lean_inc(v_arrKeyTys_879_);
lean_inc(v_keyTys_878_);
lean_dec(v___x_884_);
lean_del_object(v___x_874_);
lean_dec(v_snd_872_);
lean_dec(v_tailKey_867_);
lean_dec_ref_known(v___x_851_, 14);
v___y_815_ = v___x_883_;
v_keyTys_816_ = v_keyTys_878_;
v_arrKeyTys_817_ = v_arrKeyTys_879_;
v_arrParents_818_ = v_arrParents_880_;
v_currArrKey_819_ = v_currArrKey_881_;
v_items_820_ = v_items_882_;
goto v___jp_814_;
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_del_object(v___x_874_);
lean_dec(v_snd_872_);
lean_dec(v_fst_871_);
lean_dec(v_tailKey_867_);
lean_dec_ref_known(v___x_851_, 14);
lean_dec(v_x_809_);
v_a_908_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_876_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_876_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_tailKey_867_);
lean_dec_ref_known(v___x_851_, 14);
lean_dec(v_x_809_);
v_a_917_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_869_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_869_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
v___jp_814_:
{
lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_821_ = lean_box(0);
v___x_822_ = 1;
v___x_823_ = lean_box(v___x_822_);
lean_inc_n(v___y_815_, 2);
v___x_824_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_815_, v___x_823_, v_keyTys_816_);
v___x_825_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc(v_x_809_);
v___x_826_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_826_, 0, v_x_809_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_827_, 0, v_x_809_);
lean_ctor_set(v___x_827_, 1, v___y_815_);
lean_ctor_set(v___x_827_, 2, v___x_826_);
v___x_828_ = lean_array_push(v_items_820_, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_829_, 0, v___x_824_);
lean_ctor_set(v___x_829_, 1, v_arrKeyTys_817_);
lean_ctor_set(v___x_829_, 2, v_arrParents_818_);
lean_ctor_set(v___x_829_, 3, v_currArrKey_819_);
lean_ctor_set(v___x_829_, 4, v___y_815_);
lean_ctor_set(v___x_829_, 5, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_821_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
return v_res_946_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_fileName_960_; lean_object* v_fileMap_961_; lean_object* v_options_962_; lean_object* v_currRecDepth_963_; lean_object* v_maxRecDepth_964_; lean_object* v_ref_965_; lean_object* v_currNamespace_966_; lean_object* v_openDecls_967_; lean_object* v_initHeartbeats_968_; lean_object* v_maxHeartbeats_969_; lean_object* v_quotContext_970_; lean_object* v_currMacroScope_971_; uint8_t v_diag_972_; lean_object* v_cancelTk_x3f_973_; uint8_t v_suppressElabErrors_974_; lean_object* v_inheritedTraceOptions_975_; lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v_ref_978_; lean_object* v___x_979_; lean_object* v___y_981_; 
v_fileName_960_ = lean_ctor_get(v_a_957_, 0);
v_fileMap_961_ = lean_ctor_get(v_a_957_, 1);
v_options_962_ = lean_ctor_get(v_a_957_, 2);
v_currRecDepth_963_ = lean_ctor_get(v_a_957_, 3);
v_maxRecDepth_964_ = lean_ctor_get(v_a_957_, 4);
v_ref_965_ = lean_ctor_get(v_a_957_, 5);
v_currNamespace_966_ = lean_ctor_get(v_a_957_, 6);
v_openDecls_967_ = lean_ctor_get(v_a_957_, 7);
v_initHeartbeats_968_ = lean_ctor_get(v_a_957_, 8);
v_maxHeartbeats_969_ = lean_ctor_get(v_a_957_, 9);
v_quotContext_970_ = lean_ctor_get(v_a_957_, 10);
v_currMacroScope_971_ = lean_ctor_get(v_a_957_, 11);
v_diag_972_ = lean_ctor_get_uint8(v_a_957_, sizeof(void*)*14);
v_cancelTk_x3f_973_ = lean_ctor_get(v_a_957_, 12);
v_suppressElabErrors_974_ = lean_ctor_get_uint8(v_a_957_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_975_ = lean_ctor_get(v_a_957_, 13);
v___x_976_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_955_);
v___x_977_ = l_Lean_Syntax_isOfKind(v_x_955_, v___x_976_);
v_ref_978_ = l_Lean_replaceRef(v_x_955_, v_ref_965_);
lean_inc_ref(v_inheritedTraceOptions_975_);
lean_inc(v_cancelTk_x3f_973_);
lean_inc(v_currMacroScope_971_);
lean_inc(v_quotContext_970_);
lean_inc(v_maxHeartbeats_969_);
lean_inc(v_initHeartbeats_968_);
lean_inc(v_openDecls_967_);
lean_inc(v_currNamespace_966_);
lean_inc(v_maxRecDepth_964_);
lean_inc(v_currRecDepth_963_);
lean_inc_ref(v_options_962_);
lean_inc_ref(v_fileMap_961_);
lean_inc_ref(v_fileName_960_);
v___x_979_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_979_, 0, v_fileName_960_);
lean_ctor_set(v___x_979_, 1, v_fileMap_961_);
lean_ctor_set(v___x_979_, 2, v_options_962_);
lean_ctor_set(v___x_979_, 3, v_currRecDepth_963_);
lean_ctor_set(v___x_979_, 4, v_maxRecDepth_964_);
lean_ctor_set(v___x_979_, 5, v_ref_978_);
lean_ctor_set(v___x_979_, 6, v_currNamespace_966_);
lean_ctor_set(v___x_979_, 7, v_openDecls_967_);
lean_ctor_set(v___x_979_, 8, v_initHeartbeats_968_);
lean_ctor_set(v___x_979_, 9, v_maxHeartbeats_969_);
lean_ctor_set(v___x_979_, 10, v_quotContext_970_);
lean_ctor_set(v___x_979_, 11, v_currMacroScope_971_);
lean_ctor_set(v___x_979_, 12, v_cancelTk_x3f_973_);
lean_ctor_set(v___x_979_, 13, v_inheritedTraceOptions_975_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*14, v_diag_972_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*14 + 1, v_suppressElabErrors_974_);
if (v___x_977_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_989_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_955_, v___x_988_, v_a_956_, v___x_979_, v_a_958_);
lean_dec_ref_known(v___x_979_, 14);
lean_dec_ref(v_a_956_);
lean_dec(v_x_955_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; lean_object* v___y_995_; 
v___x_990_ = lean_unsigned_to_nat(2u);
v___x_991_ = l_Lean_Syntax_getArg(v_x_955_, v___x_990_);
v___x_992_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_991_);
v___x_993_ = l_Lean_Syntax_isOfKind(v___x_991_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec(v___x_991_);
v___x_1129_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1130_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_955_, v___x_1129_, v_a_956_, v___x_979_, v_a_958_);
lean_dec_ref_known(v___x_979_, 14);
lean_dec_ref(v_a_956_);
lean_dec(v_x_955_);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = l_Lean_Syntax_getArg(v___x_991_, v___x_1131_);
lean_dec(v___x_991_);
v___x_1133_ = l_Lean_Syntax_getArgs(v___x_1132_);
lean_dec(v___x_1132_);
v___x_1134_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1135_ = lean_array_get_size(v___x_1133_);
v___x_1136_ = lean_nat_dec_lt(v___x_1131_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v___x_1133_);
v___y_995_ = v___x_1134_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; lean_object* v_snd_1142_; 
v___x_1137_ = lean_box(v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1134_);
v___x_1139_ = ((size_t)0ULL);
v___x_1140_ = lean_usize_of_nat(v___x_1135_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_993_, v___x_1133_, v___x_1139_, v___x_1140_, v___x_1138_);
lean_dec_ref(v___x_1133_);
v_snd_1142_ = lean_ctor_get(v___x_1141_, 1);
lean_inc(v_snd_1142_);
lean_dec_ref(v___x_1141_);
v___y_995_ = v_snd_1142_;
goto v___jp_994_;
}
}
v___jp_994_:
{
size_t v_sz_996_; size_t v___x_997_; lean_object* v___x_998_; 
v_sz_996_ = lean_array_size(v___y_995_);
v___x_997_ = ((size_t)0ULL);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_996_, v___x_997_, v___y_995_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1000_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_955_, v___x_999_, v_a_956_, v___x_979_, v_a_958_);
lean_dec_ref_known(v___x_979_, 14);
lean_dec_ref(v_a_956_);
lean_dec(v_x_955_);
return v___x_1000_;
}
else
{
lean_object* v_val_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_tailKey_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_val_1001_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_array_get_size(v_val_1001_);
v___x_1004_ = lean_unsigned_to_nat(1u);
v___x_1005_ = lean_nat_sub(v___x_1003_, v___x_1004_);
v_tailKey_1006_ = lean_array_get(v___x_1002_, v_val_1001_, v___x_1005_);
lean_dec(v___x_1005_);
v___x_1007_ = lean_array_pop(v_val_1001_);
v___x_1008_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_1007_, v_a_956_, v___x_979_, v_a_958_);
lean_dec_ref(v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v_fst_1010_; lean_object* v_snd_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1120_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v_fst_1010_ = lean_ctor_get(v_a_1009_, 0);
v_snd_1011_ = lean_ctor_get(v_a_1009_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1013_ = v_a_1009_;
v_isShared_1014_ = v_isSharedCheck_1120_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_snd_1011_);
lean_inc(v_fst_1010_);
lean_dec(v_a_1009_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1120_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; 
lean_inc(v_tailKey_1006_);
v___x_1015_ = l_Lake_Toml_elabSimpleKey(v_tailKey_1006_, v___x_979_, v_a_958_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1111_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1111_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1111_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_keyTys_1020_; lean_object* v_arrKeyTys_1021_; lean_object* v_arrParents_1022_; lean_object* v_currArrKey_1023_; lean_object* v_items_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_keyTys_1020_ = lean_ctor_get(v_snd_1011_, 0);
v_arrKeyTys_1021_ = lean_ctor_get(v_snd_1011_, 1);
v_arrParents_1022_ = lean_ctor_get(v_snd_1011_, 2);
v_currArrKey_1023_ = lean_ctor_get(v_snd_1011_, 3);
v_items_1024_ = lean_ctor_get(v_snd_1011_, 5);
v___x_1025_ = l_Lean_Name_str___override(v_fst_1010_, v_a_1016_);
v___x_1026_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_1020_, v___x_1025_);
if (lean_obj_tag(v___x_1026_) == 1)
{
lean_object* v_val_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1078_; 
v_val_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1078_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_val_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1078_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
uint8_t v___x_1031_; 
v___x_1031_ = lean_unbox(v_val_1027_);
if (v___x_1031_ == 2)
{
lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1056_; 
lean_inc_ref(v_items_1024_);
lean_inc(v_arrParents_1022_);
lean_inc(v_arrKeyTys_1021_);
lean_del_object(v___x_1029_);
lean_dec(v_val_1027_);
lean_dec(v_tailKey_1006_);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_snd_1011_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; lean_object* v_unused_1058_; lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; lean_object* v_unused_1062_; 
v_unused_1057_ = lean_ctor_get(v_snd_1011_, 5);
lean_dec(v_unused_1057_);
v_unused_1058_ = lean_ctor_get(v_snd_1011_, 4);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_snd_1011_, 3);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_snd_1011_, 2);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_snd_1011_, 1);
lean_dec(v_unused_1061_);
v_unused_1062_ = lean_ctor_get(v_snd_1011_, 0);
lean_dec(v_unused_1062_);
v___x_1033_ = v_snd_1011_;
v_isShared_1034_ = v_isSharedCheck_1056_;
goto v_resetjp_1032_;
}
else
{
lean_dec(v_snd_1011_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1056_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_1022_, v___x_1025_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_del_object(v___x_1033_);
lean_dec_ref(v_items_1024_);
lean_dec(v_arrParents_1022_);
lean_dec(v_arrKeyTys_1021_);
lean_del_object(v___x_1018_);
lean_del_object(v___x_1013_);
lean_dec(v_x_955_);
v___y_981_ = v___x_1025_;
goto v___jp_980_;
}
else
{
lean_object* v_val_1036_; lean_object* v___x_1037_; 
v_val_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_val_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_1021_, v_val_1036_);
lean_dec(v_val_1036_);
if (lean_obj_tag(v___x_1037_) == 1)
{
lean_object* v_val_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_dec_ref_known(v___x_979_, 14);
v_val_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_955_, 2);
v___x_1041_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_x_955_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_mk_empty_array_with_capacity(v___x_1004_);
v___x_1043_ = lean_array_push(v___x_1042_, v___x_1041_);
v___x_1044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_x_955_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
lean_inc_n(v___x_1025_, 2);
v___x_1045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1045_, 0, v_x_955_);
lean_ctor_set(v___x_1045_, 1, v___x_1025_);
lean_ctor_set(v___x_1045_, 2, v___x_1044_);
v___x_1046_ = lean_array_push(v_items_1024_, v___x_1045_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 5, v___x_1046_);
lean_ctor_set(v___x_1033_, 4, v___x_1025_);
lean_ctor_set(v___x_1033_, 3, v___x_1025_);
lean_ctor_set(v___x_1033_, 0, v_val_1038_);
v___x_1048_ = v___x_1033_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_val_1038_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_arrKeyTys_1021_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v_arrParents_1022_);
lean_ctor_set(v_reuseFailAlloc_1055_, 3, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1055_, 4, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1055_, 5, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v___x_1048_);
lean_ctor_set(v___x_1013_, 0, v___x_1039_);
v___x_1050_ = v___x_1013_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1050_);
v___x_1052_ = v___x_1018_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_dec(v___x_1037_);
lean_del_object(v___x_1033_);
lean_dec_ref(v_items_1024_);
lean_dec(v_arrParents_1022_);
lean_dec(v_arrKeyTys_1021_);
lean_del_object(v___x_1018_);
lean_del_object(v___x_1013_);
lean_dec(v_x_955_);
v___y_981_ = v___x_1025_;
goto v___jp_980_;
}
}
}
}
else
{
lean_object* v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
lean_del_object(v___x_1018_);
lean_del_object(v___x_1013_);
lean_dec(v_x_955_);
v___x_1063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1064_ = lean_unbox(v_val_1027_);
lean_dec(v_val_1027_);
v___x_1065_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1064_);
v___x_1066_ = lean_string_append(v___x_1063_, v___x_1065_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1068_ = lean_string_append(v___x_1066_, v___x_1067_);
v___x_1069_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1025_, v___x_993_);
v___x_1070_ = lean_string_append(v___x_1068_, v___x_1069_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1072_ = lean_string_append(v___x_1070_, v___x_1071_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 3);
lean_ctor_set(v___x_1029_, 0, v___x_1072_);
v___x_1074_ = v___x_1029_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = l_Lean_MessageData_ofFormat(v___x_1074_);
v___x_1076_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_1006_, v___x_1075_, v_snd_1011_, v___x_979_, v_a_958_);
lean_dec_ref_known(v___x_979_, 14);
lean_dec(v_snd_1011_);
lean_dec(v_tailKey_1006_);
return v___x_1076_;
}
}
}
}
else
{
lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1104_; 
lean_inc_ref(v_items_1024_);
lean_inc(v_currArrKey_1023_);
lean_inc(v_arrParents_1022_);
lean_inc(v_arrKeyTys_1021_);
lean_inc(v_keyTys_1020_);
lean_dec(v___x_1026_);
lean_dec(v_tailKey_1006_);
lean_dec_ref_known(v___x_979_, 14);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_snd_1011_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; lean_object* v_unused_1106_; lean_object* v_unused_1107_; lean_object* v_unused_1108_; lean_object* v_unused_1109_; lean_object* v_unused_1110_; 
v_unused_1105_ = lean_ctor_get(v_snd_1011_, 5);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_snd_1011_, 4);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_snd_1011_, 3);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_snd_1011_, 2);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_snd_1011_, 1);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_snd_1011_, 0);
lean_dec(v_unused_1110_);
v___x_1080_ = v_snd_1011_;
v_isShared_1081_ = v_isSharedCheck_1104_;
goto v_resetjp_1079_;
}
else
{
lean_dec(v_snd_1011_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1104_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1082_ = lean_box(0);
v___x_1083_ = 2;
v___x_1084_ = lean_box(v___x_1083_);
lean_inc_n(v___x_1025_, 4);
v___x_1085_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1025_, v___x_1084_, v_keyTys_1020_);
lean_inc(v___x_1085_);
lean_inc(v_currArrKey_1023_);
v___x_1086_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_1023_, v___x_1085_, v_arrKeyTys_1021_);
v___x_1087_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1025_, v_currArrKey_1023_, v_arrParents_1022_);
v___x_1088_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_955_, 2);
v___x_1089_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_x_955_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_mk_empty_array_with_capacity(v___x_1004_);
v___x_1091_ = lean_array_push(v___x_1090_, v___x_1089_);
v___x_1092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_x_955_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1093_, 0, v_x_955_);
lean_ctor_set(v___x_1093_, 1, v___x_1025_);
lean_ctor_set(v___x_1093_, 2, v___x_1092_);
v___x_1094_ = lean_array_push(v_items_1024_, v___x_1093_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 5, v___x_1094_);
lean_ctor_set(v___x_1080_, 4, v___x_1025_);
lean_ctor_set(v___x_1080_, 3, v___x_1025_);
lean_ctor_set(v___x_1080_, 2, v___x_1087_);
lean_ctor_set(v___x_1080_, 1, v___x_1086_);
lean_ctor_set(v___x_1080_, 0, v___x_1085_);
v___x_1096_ = v___x_1080_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1103_, 5, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v___x_1096_);
lean_ctor_set(v___x_1013_, 0, v___x_1082_);
v___x_1098_ = v___x_1013_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1100_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1098_);
v___x_1100_ = v___x_1018_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_del_object(v___x_1013_);
lean_dec(v_snd_1011_);
lean_dec(v_fst_1010_);
lean_dec(v_tailKey_1006_);
lean_dec_ref_known(v___x_979_, 14);
lean_dec(v_x_955_);
v_a_1112_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1015_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1015_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_tailKey_1006_);
lean_dec_ref_known(v___x_979_, 14);
lean_dec(v_x_955_);
v_a_1121_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1008_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1008_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
v___jp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_982_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_983_ = l_Lean_MessageData_ofName(v___y_981_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_986_, v___x_979_, v_a_958_);
lean_dec_ref_known(v___x_979_, 14);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1148_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1152_);
v___x_1158_ = l_Lean_Syntax_isOfKind(v_x_1152_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_1152_);
v___x_1160_ = l_Lean_Syntax_isOfKind(v_x_1152_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1152_);
v___x_1162_ = l_Lean_Syntax_isOfKind(v_x_1152_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1164_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1152_, v___x_1163_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec_ref(v_a_1153_);
lean_dec(v_x_1152_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; 
v___x_1165_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1165_;
}
}
else
{
lean_object* v___x_1166_; 
v___x_1166_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1166_;
}
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1174_, lean_object* v_as_1175_, size_t v_i_1176_, size_t v_stop_1177_, lean_object* v_b_1178_){
_start:
{
lean_object* v___y_1180_; uint8_t v___x_1184_; 
v___x_1184_ = lean_usize_dec_eq(v_i_1176_, v_stop_1177_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1188_; 
v___x_1185_ = lean_array_uget_borrowed(v_as_1175_, v_i_1176_);
v_fst_1186_ = lean_ctor_get(v___x_1185_, 0);
v_snd_1187_ = lean_ctor_get(v___x_1185_, 1);
lean_inc(v_fst_1186_);
v___x_1188_ = l_Lean_Name_components(v_fst_1186_);
if (lean_obj_tag(v___x_1188_) == 0)
{
v___y_1180_ = v_b_1178_;
goto v___jp_1179_;
}
else
{
lean_object* v_head_1189_; lean_object* v_tail_1190_; lean_object* v___x_1191_; 
v_head_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_head_1189_);
v_tail_1190_ = lean_ctor_get(v___x_1188_, 1);
lean_inc(v_tail_1190_);
lean_dec_ref_known(v___x_1188_, 2);
lean_inc(v_snd_1187_);
lean_inc(v_ref_1174_);
v___x_1191_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1178_, v_ref_1174_, v_head_1189_, v_tail_1190_, v_snd_1187_);
v___y_1180_ = v___x_1191_;
goto v___jp_1179_;
}
}
else
{
lean_dec(v_ref_1174_);
return v_b_1178_;
}
v___jp_1179_:
{
size_t v___x_1181_; size_t v___x_1182_; 
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_i_1176_, v___x_1181_);
v_i_1176_ = v___x_1182_;
v_b_1178_ = v___y_1180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1192_, size_t v_i_1193_, lean_object* v_bs_1194_){
_start:
{
uint8_t v___x_1195_; 
v___x_1195_ = lean_usize_dec_lt(v_i_1193_, v_sz_1192_);
if (v___x_1195_ == 0)
{
return v_bs_1194_;
}
else
{
lean_object* v_v_1196_; lean_object* v___x_1197_; lean_object* v_bs_x27_1198_; lean_object* v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
v_v_1196_ = lean_array_uget(v_bs_1194_, v_i_1193_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v_bs_x27_1198_ = lean_array_uset(v_bs_1194_, v_i_1193_, v___x_1197_);
v___x_1199_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1196_);
v___x_1200_ = ((size_t)1ULL);
v___x_1201_ = lean_usize_add(v_i_1193_, v___x_1200_);
v___x_1202_ = lean_array_uset(v_bs_x27_1198_, v_i_1193_, v___x_1199_);
v_i_1193_ = v___x_1201_;
v_bs_1194_ = v___x_1202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1204_){
_start:
{
switch(lean_obj_tag(v_a_1204_))
{
case 6:
{
lean_object* v_xs_1205_; lean_object* v_ref_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1234_; 
v_xs_1205_ = lean_ctor_get(v_a_1204_, 1);
v_ref_1206_ = lean_ctor_get(v_a_1204_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_a_1204_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1208_ = v_a_1204_;
v_isShared_1209_ = v_isSharedCheck_1234_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_xs_1205_);
lean_inc(v_ref_1206_);
lean_dec(v_a_1204_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1234_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_items_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_items_1210_ = lean_ctor_get(v_xs_1205_, 0);
lean_inc_ref(v_items_1210_);
lean_dec_ref(v_xs_1205_);
v___x_1211_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_array_get_size(v_items_1210_);
v___x_1214_ = lean_nat_dec_lt(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v_items_1210_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v___x_1211_);
v___x_1216_ = v___x_1208_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_ref_1206_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = lean_nat_dec_le(v___x_1213_, v___x_1213_);
if (v___x_1218_ == 0)
{
if (v___x_1214_ == 0)
{
lean_object* v___x_1220_; 
lean_dec_ref(v_items_1210_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v___x_1211_);
v___x_1220_ = v___x_1208_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_ref_1206_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1211_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
else
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1222_ = ((size_t)0ULL);
v___x_1223_ = lean_usize_of_nat(v___x_1213_);
lean_inc(v_ref_1206_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1206_, v_items_1210_, v___x_1222_, v___x_1223_, v___x_1211_);
lean_dec_ref(v_items_1210_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v___x_1224_);
v___x_1226_ = v___x_1208_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_ref_1206_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
else
{
size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1228_ = ((size_t)0ULL);
v___x_1229_ = lean_usize_of_nat(v___x_1213_);
lean_inc(v_ref_1206_);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1206_, v_items_1210_, v___x_1228_, v___x_1229_, v___x_1211_);
lean_dec_ref(v_items_1210_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v___x_1230_);
v___x_1232_ = v___x_1208_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_ref_1206_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
case 5:
{
lean_object* v_ref_1235_; lean_object* v_xs_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1246_; 
v_ref_1235_ = lean_ctor_get(v_a_1204_, 0);
v_xs_1236_ = lean_ctor_get(v_a_1204_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_a_1204_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1238_ = v_a_1204_;
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_xs_1236_);
lean_inc(v_ref_1235_);
lean_dec(v_a_1204_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
size_t v_sz_1240_; size_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v_sz_1240_ = lean_array_size(v_xs_1236_);
v___x_1241_ = ((size_t)0ULL);
v___x_1242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1240_, v___x_1241_, v_xs_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1242_);
v___x_1244_ = v___x_1238_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_ref_1235_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
default: 
{
return v_a_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1247_, lean_object* v___x_1248_, lean_object* v_v_x3f_1249_){
_start:
{
if (lean_obj_tag(v_v_x3f_1249_) == 1)
{
lean_object* v_val_1250_; 
v_val_1250_ = lean_ctor_get(v_v_x3f_1249_, 0);
lean_inc(v_val_1250_);
lean_dec_ref_known(v_v_x3f_1249_, 1);
switch(lean_obj_tag(v_val_1250_))
{
case 6:
{
lean_object* v_ref_1251_; lean_object* v_xs_1252_; lean_object* v___x_1253_; 
v_ref_1251_ = lean_ctor_get(v_val_1250_, 0);
lean_inc(v_ref_1251_);
v_xs_1252_ = lean_ctor_get(v_val_1250_, 1);
lean_inc_ref(v_xs_1252_);
lean_dec_ref_known(v_val_1250_, 2);
v___x_1253_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1247_);
if (lean_obj_tag(v___x_1253_) == 6)
{
lean_object* v_xs_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1263_; 
v_xs_1254_ = lean_ctor_get(v___x_1253_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v___x_1253_, 0);
lean_dec(v_unused_1264_);
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_xs_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_items_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v_items_1258_ = lean_ctor_get(v_xs_1254_, 0);
lean_inc_ref(v_items_1258_);
lean_dec_ref(v_xs_1254_);
v___x_1259_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1248_, v_xs_1252_, v_items_1258_);
lean_dec_ref(v_items_1258_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1259_);
lean_ctor_set(v___x_1256_, 0, v_ref_1251_);
v___x_1261_ = v___x_1256_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_ref_1251_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
else
{
lean_dec_ref(v_xs_1252_);
lean_dec(v_ref_1251_);
lean_dec_ref(v___x_1248_);
return v___x_1253_;
}
}
case 5:
{
lean_object* v_ref_1265_; lean_object* v_xs_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v___x_1248_);
v_ref_1265_ = lean_ctor_get(v_val_1250_, 0);
v_xs_1266_ = lean_ctor_get(v_val_1250_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_val_1250_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1268_ = v_val_1250_;
v_isShared_1269_ = v_isSharedCheck_1285_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_xs_1266_);
lean_inc(v_ref_1265_);
lean_dec(v_val_1250_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1285_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1247_);
if (lean_obj_tag(v___x_1270_) == 5)
{
lean_object* v_xs_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1279_; 
lean_del_object(v___x_1268_);
v_xs_1271_ = lean_ctor_get(v___x_1270_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1270_, 0);
lean_dec(v_unused_1280_);
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_xs_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = l_Array_append___redArg(v_xs_1266_, v_xs_1271_);
lean_dec_ref(v_xs_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___x_1275_);
lean_ctor_set(v___x_1273_, 0, v_ref_1265_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_ref_1265_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_array_push(v_xs_1266_, v___x_1270_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v___x_1281_);
v___x_1283_ = v___x_1268_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_ref_1265_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
default: 
{
lean_object* v___x_1286_; 
lean_dec(v_val_1250_);
lean_dec_ref(v___x_1248_);
v___x_1286_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1247_);
return v___x_1286_;
}
}
}
else
{
lean_object* v___x_1287_; 
lean_dec(v_v_x3f_1249_);
lean_dec_ref(v___x_1248_);
v___x_1287_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1247_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1288_, lean_object* v_k_1289_, lean_object* v_t_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1290_);
lean_inc(v_k_1289_);
v___x_1292_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1291_, v_k_1289_, v_t_1290_);
if (lean_obj_tag(v___x_1292_) == 1)
{
lean_object* v_val_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_k_1289_);
v_val_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1328_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_val_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1328_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_items_1297_; lean_object* v_indices_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1327_; 
v_items_1297_ = lean_ctor_get(v_t_1290_, 0);
v_indices_1298_ = lean_ctor_get(v_t_1290_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_t_1290_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1300_ = v_t_1290_;
v_isShared_1301_ = v_isSharedCheck_1327_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_indices_1298_);
lean_inc(v_items_1297_);
lean_dec(v_t_1290_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1327_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = lean_array_get_size(v_items_1297_);
v___x_1303_ = lean_nat_dec_lt(v_val_1293_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1305_; 
lean_del_object(v___x_1295_);
lean_dec(v_val_1293_);
lean_dec_ref(v_newV_1288_);
if (v_isShared_1301_ == 0)
{
v___x_1305_ = v___x_1300_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_items_1297_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_indices_1298_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
else
{
lean_object* v_v_1307_; lean_object* v_fst_1308_; lean_object* v_snd_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1326_; 
v_v_1307_ = lean_array_fget(v_items_1297_, v_val_1293_);
v_fst_1308_ = lean_ctor_get(v_v_1307_, 0);
v_snd_1309_ = lean_ctor_get(v_v_1307_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_v_1307_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1311_ = v_v_1307_;
v_isShared_1312_ = v_isSharedCheck_1326_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_snd_1309_);
lean_inc(v_fst_1308_);
lean_dec(v_v_1307_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1326_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v_xs_x27_1314_; lean_object* v___x_1316_; 
v___x_1313_ = lean_box(0);
v_xs_x27_1314_ = lean_array_fset(v_items_1297_, v_val_1293_, v___x_1313_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v_snd_1309_);
v___x_1316_ = v___x_1295_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_snd_1309_);
v___x_1316_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1288_, v___x_1291_, v___x_1316_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v___x_1317_);
v___x_1319_ = v___x_1311_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_fst_1308_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_array_fset(v_xs_x27_1314_, v_val_1293_, v___x_1319_);
lean_dec(v_val_1293_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1320_);
v___x_1322_ = v___x_1300_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_indices_1298_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
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
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v___x_1292_);
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1288_, v___x_1291_, v___x_1329_);
v___x_1331_ = l_Lake_Toml_RBDict_push___redArg(v___x_1291_, v_k_1289_, v___x_1330_, v_t_1290_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1332_, lean_object* v_head_1333_, lean_object* v_tail_1334_, lean_object* v_newV_1335_, lean_object* v___x_1336_, lean_object* v_v_x3f_1337_){
_start:
{
if (lean_obj_tag(v_v_x3f_1337_) == 1)
{
lean_object* v_val_1338_; 
v_val_1338_ = lean_ctor_get(v_v_x3f_1337_, 0);
lean_inc(v_val_1338_);
lean_dec_ref_known(v_v_x3f_1337_, 1);
switch(lean_obj_tag(v_val_1338_))
{
case 5:
{
lean_object* v_ref_1339_; lean_object* v_xs_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_ref_1339_ = lean_ctor_get(v_val_1338_, 0);
v_xs_1340_ = lean_ctor_get(v_val_1338_, 1);
v___x_1341_ = lean_array_get_size(v_xs_1340_);
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = lean_nat_sub(v___x_1341_, v___x_1342_);
v___x_1344_ = lean_nat_dec_lt(v___x_1343_, v___x_1341_);
if (v___x_1344_ == 0)
{
lean_dec(v___x_1343_);
lean_dec_ref(v_newV_1335_);
lean_dec(v_tail_1334_);
lean_dec(v_head_1333_);
lean_dec(v_kRef_1332_);
return v_val_1338_;
}
else
{
lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1369_; 
lean_inc_ref(v_xs_1340_);
lean_inc(v_ref_1339_);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_val_1338_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; lean_object* v_unused_1371_; 
v_unused_1370_ = lean_ctor_get(v_val_1338_, 1);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_val_1338_, 0);
lean_dec(v_unused_1371_);
v___x_1346_ = v_val_1338_;
v_isShared_1347_ = v_isSharedCheck_1369_;
goto v_resetjp_1345_;
}
else
{
lean_dec(v_val_1338_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1369_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_v_1348_; lean_object* v___x_1349_; lean_object* v_xs_x27_1350_; lean_object* v___y_1352_; 
v_v_1348_ = lean_array_fget(v_xs_1340_, v___x_1343_);
v___x_1349_ = lean_box(0);
v_xs_x27_1350_ = lean_array_fset(v_xs_1340_, v___x_1343_, v___x_1349_);
if (lean_obj_tag(v_v_1348_) == 6)
{
lean_object* v_ref_1357_; lean_object* v_xs_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
v_ref_1357_ = lean_ctor_get(v_v_1348_, 0);
v_xs_1358_ = lean_ctor_get(v_v_1348_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_v_1348_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1360_ = v_v_1348_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_xs_1358_);
lean_inc(v_ref_1357_);
lean_dec(v_v_1348_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1358_, v_kRef_1332_, v_head_1333_, v_tail_1334_, v_newV_1335_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_ref_1357_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
v___y_1352_ = v___x_1364_;
goto v___jp_1351_;
}
}
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec(v_v_1348_);
lean_dec_ref(v_newV_1335_);
lean_dec(v_tail_1334_);
lean_dec(v_head_1333_);
v___x_1367_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1336_);
v___x_1368_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_kRef_1332_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___y_1352_ = v___x_1368_;
goto v___jp_1351_;
}
v___jp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = lean_array_fset(v_xs_x27_1350_, v___x_1343_, v___y_1352_);
lean_dec(v___x_1343_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1353_);
v___x_1355_ = v___x_1346_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_ref_1339_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1372_; lean_object* v_xs_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1381_; 
v_ref_1372_ = lean_ctor_get(v_val_1338_, 0);
v_xs_1373_ = lean_ctor_get(v_val_1338_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_val_1338_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1375_ = v_val_1338_;
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_xs_1373_);
lean_inc(v_ref_1372_);
lean_dec(v_val_1338_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1373_, v_kRef_1332_, v_head_1333_, v_tail_1334_, v_newV_1335_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1377_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_ref_1372_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
default: 
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v_val_1338_);
v___x_1382_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1336_);
lean_inc(v_kRef_1332_);
v___x_1383_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1382_, v_kRef_1332_, v_head_1333_, v_tail_1334_, v_newV_1335_);
v___x_1384_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_kRef_1332_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
return v___x_1384_;
}
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec(v_v_x3f_1337_);
v___x_1385_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1336_);
lean_inc(v_kRef_1332_);
v___x_1386_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1385_, v_kRef_1332_, v_head_1333_, v_tail_1334_, v_newV_1335_);
v___x_1387_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_kRef_1332_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1388_, lean_object* v_head_1389_, lean_object* v_tail_1390_, lean_object* v_newV_1391_, lean_object* v_k_1392_, lean_object* v_t_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1393_);
lean_inc(v_k_1392_);
v___x_1395_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1394_, v_k_1392_, v_t_1393_);
if (lean_obj_tag(v___x_1395_) == 1)
{
lean_object* v_val_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_k_1392_);
v_val_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1431_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_val_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1431_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_items_1400_; lean_object* v_indices_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1430_; 
v_items_1400_ = lean_ctor_get(v_t_1393_, 0);
v_indices_1401_ = lean_ctor_get(v_t_1393_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_t_1393_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1403_ = v_t_1393_;
v_isShared_1404_ = v_isSharedCheck_1430_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_indices_1401_);
lean_inc(v_items_1400_);
lean_dec(v_t_1393_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1430_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = lean_array_get_size(v_items_1400_);
v___x_1406_ = lean_nat_dec_lt(v_val_1396_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1408_; 
lean_del_object(v___x_1398_);
lean_dec(v_val_1396_);
lean_dec_ref(v_newV_1391_);
lean_dec(v_tail_1390_);
lean_dec(v_head_1389_);
lean_dec(v_kRef_1388_);
if (v_isShared_1404_ == 0)
{
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_items_1400_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_indices_1401_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
else
{
lean_object* v_v_1410_; lean_object* v_fst_1411_; lean_object* v_snd_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1429_; 
v_v_1410_ = lean_array_fget(v_items_1400_, v_val_1396_);
v_fst_1411_ = lean_ctor_get(v_v_1410_, 0);
v_snd_1412_ = lean_ctor_get(v_v_1410_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_v_1410_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1414_ = v_v_1410_;
v_isShared_1415_ = v_isSharedCheck_1429_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_snd_1412_);
lean_inc(v_fst_1411_);
lean_dec(v_v_1410_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1429_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v_xs_x27_1417_; lean_object* v___x_1419_; 
v___x_1416_ = lean_box(0);
v_xs_x27_1417_ = lean_array_fset(v_items_1400_, v_val_1396_, v___x_1416_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_snd_1412_);
v___x_1419_ = v___x_1398_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_snd_1412_);
v___x_1419_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1388_, v_head_1389_, v_tail_1390_, v_newV_1391_, v___x_1394_, v___x_1419_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v___x_1420_);
v___x_1422_ = v___x_1414_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_fst_1411_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_array_fset(v_xs_x27_1417_, v_val_1396_, v___x_1422_);
lean_dec(v_val_1396_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1423_);
v___x_1425_ = v___x_1403_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_indices_1401_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
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
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v___x_1395_);
v___x_1432_ = lean_box(0);
v___x_1433_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1388_, v_head_1389_, v_tail_1390_, v_newV_1391_, v___x_1394_, v___x_1432_);
v___x_1434_ = l_Lake_Toml_RBDict_push___redArg(v___x_1394_, v_k_1392_, v___x_1433_, v_t_1393_);
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1435_, lean_object* v_kRef_1436_, lean_object* v_k_1437_, lean_object* v_ks_1438_, lean_object* v_newV_1439_){
_start:
{
if (lean_obj_tag(v_ks_1438_) == 0)
{
lean_object* v___x_1440_; 
lean_dec(v_kRef_1436_);
v___x_1440_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1439_, v_k_1437_, v_t_1435_);
return v___x_1440_;
}
else
{
lean_object* v_head_1441_; lean_object* v_tail_1442_; lean_object* v___x_1443_; 
v_head_1441_ = lean_ctor_get(v_ks_1438_, 0);
lean_inc(v_head_1441_);
v_tail_1442_ = lean_ctor_get(v_ks_1438_, 1);
lean_inc(v_tail_1442_);
lean_dec_ref_known(v_ks_1438_, 2);
v___x_1443_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1436_, v_head_1441_, v_tail_1442_, v_newV_1439_, v_k_1437_, v_t_1435_);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1444_, lean_object* v_i_1445_, lean_object* v_bs_1446_){
_start:
{
size_t v_sz_boxed_1447_; size_t v_i_boxed_1448_; lean_object* v_res_1449_; 
v_sz_boxed_1447_ = lean_unbox_usize(v_sz_1444_);
lean_dec(v_sz_1444_);
v_i_boxed_1448_ = lean_unbox_usize(v_i_1445_);
lean_dec(v_i_1445_);
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1447_, v_i_boxed_1448_, v_bs_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1450_, lean_object* v_as_1451_, lean_object* v_i_1452_, lean_object* v_stop_1453_, lean_object* v_b_1454_){
_start:
{
size_t v_i_boxed_1455_; size_t v_stop_boxed_1456_; lean_object* v_res_1457_; 
v_i_boxed_1455_ = lean_unbox_usize(v_i_1452_);
lean_dec(v_i_1452_);
v_stop_boxed_1456_ = lean_unbox_usize(v_stop_1453_);
lean_dec(v_stop_1453_);
v_res_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1450_, v_as_1451_, v_i_boxed_1455_, v_stop_boxed_1456_, v_b_1454_);
lean_dec_ref(v_as_1451_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0___boxed(lean_object* v_kRef_1458_, lean_object* v_head_1459_, lean_object* v_tail_1460_, lean_object* v_newV_1461_, lean_object* v___x_1462_, lean_object* v_v_x3f_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1458_, v_head_1459_, v_tail_1460_, v_newV_1461_, v___x_1462_, v_v_x3f_1463_);
lean_dec_ref(v___x_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1465_, size_t v_i_1466_, size_t v_stop_1467_, lean_object* v_b_1468_){
_start:
{
lean_object* v___y_1470_; uint8_t v___x_1474_; 
v___x_1474_ = lean_usize_dec_eq(v_i_1466_, v_stop_1467_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v_ref_1476_; lean_object* v_key_1477_; lean_object* v_val_1478_; lean_object* v___x_1479_; 
v___x_1475_ = lean_array_uget_borrowed(v_as_1465_, v_i_1466_);
v_ref_1476_ = lean_ctor_get(v___x_1475_, 0);
v_key_1477_ = lean_ctor_get(v___x_1475_, 1);
v_val_1478_ = lean_ctor_get(v___x_1475_, 2);
lean_inc(v_key_1477_);
v___x_1479_ = l_Lean_Name_components(v_key_1477_);
if (lean_obj_tag(v___x_1479_) == 0)
{
v___y_1470_ = v_b_1468_;
goto v___jp_1469_;
}
else
{
lean_object* v_head_1480_; lean_object* v_tail_1481_; lean_object* v___x_1482_; 
v_head_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_head_1480_);
v_tail_1481_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_tail_1481_);
lean_dec_ref_known(v___x_1479_, 2);
lean_inc_ref(v_val_1478_);
lean_inc(v_ref_1476_);
v___x_1482_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1468_, v_ref_1476_, v_head_1480_, v_tail_1481_, v_val_1478_);
v___y_1470_ = v___x_1482_;
goto v___jp_1469_;
}
}
else
{
return v_b_1468_;
}
v___jp_1469_:
{
size_t v___x_1471_; size_t v___x_1472_; 
v___x_1471_ = ((size_t)1ULL);
v___x_1472_ = lean_usize_add(v_i_1466_, v___x_1471_);
v_i_1466_ = v___x_1472_;
v_b_1468_ = v___y_1470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1483_, lean_object* v_i_1484_, lean_object* v_stop_1485_, lean_object* v_b_1486_){
_start:
{
size_t v_i_boxed_1487_; size_t v_stop_boxed_1488_; lean_object* v_res_1489_; 
v_i_boxed_1487_ = lean_unbox_usize(v_i_1484_);
lean_dec(v_i_1484_);
v_stop_boxed_1488_ = lean_unbox_usize(v_stop_1485_);
lean_dec(v_stop_1485_);
v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1483_, v_i_boxed_1487_, v_stop_boxed_1488_, v_b_1486_);
lean_dec_ref(v_as_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1491_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_array_get_size(v_items_1490_);
v___x_1494_ = lean_nat_dec_lt(v___x_1492_, v___x_1493_);
if (v___x_1494_ == 0)
{
return v___x_1491_;
}
else
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_nat_dec_le(v___x_1493_, v___x_1493_);
if (v___x_1495_ == 0)
{
if (v___x_1494_ == 0)
{
return v___x_1491_;
}
else
{
size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = ((size_t)0ULL);
v___x_1497_ = lean_usize_of_nat(v___x_1493_);
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1490_, v___x_1496_, v___x_1497_, v___x_1491_);
return v___x_1498_;
}
}
else
{
size_t v___x_1499_; size_t v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = ((size_t)0ULL);
v___x_1500_ = lean_usize_of_nat(v___x_1493_);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1490_, v___x_1499_, v___x_1500_, v___x_1491_);
return v___x_1501_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1502_);
lean_dec_ref(v_items_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1506_);
lean_inc_ref(v_a_1505_);
v___x_1509_ = lean_apply_4(v_x_1504_, v___x_1508_, v_a_1505_, v_a_1506_, lean_box(0));
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1520_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1520_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1520_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_snd_1514_; lean_object* v_items_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v_snd_1514_ = lean_ctor_get(v_a_1510_, 1);
lean_inc(v_snd_1514_);
lean_dec(v_a_1510_);
v_items_1515_ = lean_ctor_get(v_snd_1514_, 5);
lean_inc_ref(v_items_1515_);
lean_dec(v_snd_1514_);
v___x_1516_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1515_);
lean_dec_ref(v_items_1515_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1516_);
v___x_1518_ = v___x_1512_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
v_a_1521_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1509_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1509_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1529_, v_a_1530_, v_a_1531_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1542_, uint8_t v___y_1543_, lean_object* v_x_1544_){
_start:
{
if (lean_obj_tag(v_x_1544_) == 1)
{
lean_object* v_pre_1545_; 
v_pre_1545_ = lean_ctor_get(v_x_1544_, 0);
switch(lean_obj_tag(v_pre_1545_))
{
case 1:
{
lean_object* v_pre_1546_; 
v_pre_1546_ = lean_ctor_get(v_pre_1545_, 0);
switch(lean_obj_tag(v_pre_1546_))
{
case 0:
{
lean_object* v_str_1547_; lean_object* v_str_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_str_1547_ = lean_ctor_get(v_x_1544_, 1);
v_str_1548_ = lean_ctor_get(v_pre_1545_, 1);
v___x_1549_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1550_ = lean_string_dec_eq(v_str_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1552_ = lean_string_dec_eq(v_str_1548_, v___x_1551_);
if (v___x_1552_ == 0)
{
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1554_ = lean_string_dec_eq(v_str_1547_, v___x_1553_);
if (v___x_1554_ == 0)
{
return v___x_1554_;
}
else
{
return v_suppressElabErrors_1542_;
}
}
}
else
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1556_ = lean_string_dec_eq(v_str_1547_, v___x_1555_);
if (v___x_1556_ == 0)
{
return v___x_1556_;
}
else
{
return v_suppressElabErrors_1542_;
}
}
}
case 1:
{
lean_object* v_pre_1557_; 
v_pre_1557_ = lean_ctor_get(v_pre_1546_, 0);
if (lean_obj_tag(v_pre_1557_) == 0)
{
lean_object* v_str_1558_; lean_object* v_str_1559_; lean_object* v_str_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v_str_1558_ = lean_ctor_get(v_x_1544_, 1);
v_str_1559_ = lean_ctor_get(v_pre_1545_, 1);
v_str_1560_ = lean_ctor_get(v_pre_1546_, 1);
v___x_1561_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1562_ = lean_string_dec_eq(v_str_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
return v___x_1562_;
}
else
{
lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1564_ = lean_string_dec_eq(v_str_1559_, v___x_1563_);
if (v___x_1564_ == 0)
{
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1566_ = lean_string_dec_eq(v_str_1558_, v___x_1565_);
if (v___x_1566_ == 0)
{
return v___x_1566_;
}
else
{
return v_suppressElabErrors_1542_;
}
}
}
}
else
{
return v___y_1543_;
}
}
default: 
{
return v___y_1543_;
}
}
}
case 0:
{
lean_object* v_str_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_str_1567_ = lean_ctor_get(v_x_1544_, 1);
v___x_1568_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1569_ = lean_string_dec_eq(v_str_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
return v___x_1569_;
}
else
{
return v_suppressElabErrors_1542_;
}
}
default: 
{
return v___y_1543_;
}
}
}
else
{
return v___y_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1570_, lean_object* v___y_1571_, lean_object* v_x_1572_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1573_; uint8_t v___y_10623__boxed_1574_; uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_suppressElabErrors_boxed_1573_ = lean_unbox(v_suppressElabErrors_1570_);
v___y_10623__boxed_1574_ = lean_unbox(v___y_1571_);
v_res_1575_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1573_, v___y_10623__boxed_1574_, v_x_1572_);
lean_dec(v_x_1572_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1577_, lean_object* v_opt_1578_){
_start:
{
lean_object* v_name_1579_; lean_object* v_defValue_1580_; lean_object* v_map_1581_; lean_object* v___x_1582_; 
v_name_1579_ = lean_ctor_get(v_opt_1578_, 0);
v_defValue_1580_ = lean_ctor_get(v_opt_1578_, 1);
v_map_1581_ = lean_ctor_get(v_opts_1577_, 0);
v___x_1582_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1581_, v_name_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_unbox(v_defValue_1580_);
return v___x_1583_;
}
else
{
lean_object* v_val_1584_; 
v_val_1584_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_val_1584_);
lean_dec_ref_known(v___x_1582_, 1);
if (lean_obj_tag(v_val_1584_) == 1)
{
uint8_t v_v_1585_; 
v_v_1585_ = lean_ctor_get_uint8(v_val_1584_, 0);
lean_dec_ref_known(v_val_1584_, 0);
return v_v_1585_;
}
else
{
uint8_t v___x_1586_; 
lean_dec(v_val_1584_);
v___x_1586_ = lean_unbox(v_defValue_1580_);
return v___x_1586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1587_, lean_object* v_opt_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1587_, v_opt_1588_);
lean_dec_ref(v_opt_1588_);
lean_dec_ref(v_opts_1587_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1592_, lean_object* v_msgData_1593_, uint8_t v_severity_1594_, uint8_t v_isSilent_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_a_1601_; lean_object* v___y_1605_; uint8_t v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1640_; uint8_t v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; uint8_t v___y_1645_; uint8_t v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1664_; lean_object* v___y_1665_; uint8_t v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; uint8_t v___y_1669_; uint8_t v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1675_; uint8_t v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; uint8_t v___y_1680_; uint8_t v___y_1681_; uint8_t v___x_1686_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; uint8_t v___y_1692_; uint8_t v___y_1693_; uint8_t v___y_1694_; uint8_t v___y_1696_; uint8_t v___x_1712_; 
v___x_1686_ = 2;
v___x_1712_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1594_, v___x_1686_);
if (v___x_1712_ == 0)
{
v___y_1696_ = v___x_1712_;
goto v___jp_1695_;
}
else
{
uint8_t v___x_1713_; 
lean_inc_ref(v_msgData_1593_);
v___x_1713_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1593_);
v___y_1696_ = v___x_1713_;
goto v___jp_1695_;
}
v___jp_1600_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_a_1601_);
lean_ctor_set(v___x_1602_, 1, v___y_1596_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
v___jp_1604_:
{
lean_object* v___x_1614_; lean_object* v_currNamespace_1615_; lean_object* v_openDecls_1616_; lean_object* v_env_1617_; lean_object* v_nextMacroScope_1618_; lean_object* v_ngen_1619_; lean_object* v_auxDeclNGen_1620_; lean_object* v_traceState_1621_; lean_object* v_cache_1622_; lean_object* v_messages_1623_; lean_object* v_infoState_1624_; lean_object* v_snapshotTasks_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1638_; 
v___x_1614_ = lean_st_ref_take(v___y_1613_);
v_currNamespace_1615_ = lean_ctor_get(v___y_1612_, 6);
v_openDecls_1616_ = lean_ctor_get(v___y_1612_, 7);
v_env_1617_ = lean_ctor_get(v___x_1614_, 0);
v_nextMacroScope_1618_ = lean_ctor_get(v___x_1614_, 1);
v_ngen_1619_ = lean_ctor_get(v___x_1614_, 2);
v_auxDeclNGen_1620_ = lean_ctor_get(v___x_1614_, 3);
v_traceState_1621_ = lean_ctor_get(v___x_1614_, 4);
v_cache_1622_ = lean_ctor_get(v___x_1614_, 5);
v_messages_1623_ = lean_ctor_get(v___x_1614_, 6);
v_infoState_1624_ = lean_ctor_get(v___x_1614_, 7);
v_snapshotTasks_1625_ = lean_ctor_get(v___x_1614_, 8);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1627_ = v___x_1614_;
v_isShared_1628_ = v_isSharedCheck_1638_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_snapshotTasks_1625_);
lean_inc(v_infoState_1624_);
lean_inc(v_messages_1623_);
lean_inc(v_cache_1622_);
lean_inc(v_traceState_1621_);
lean_inc(v_auxDeclNGen_1620_);
lean_inc(v_ngen_1619_);
lean_inc(v_nextMacroScope_1618_);
lean_inc(v_env_1617_);
lean_dec(v___x_1614_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1638_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
lean_inc(v_openDecls_1616_);
lean_inc(v_currNamespace_1615_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v_currNamespace_1615_);
lean_ctor_set(v___x_1629_, 1, v_openDecls_1616_);
v___x_1630_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___y_1611_);
lean_inc_ref(v___y_1609_);
lean_inc_ref(v___y_1607_);
v___x_1631_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1631_, 0, v___y_1607_);
lean_ctor_set(v___x_1631_, 1, v___y_1605_);
lean_ctor_set(v___x_1631_, 2, v___y_1610_);
lean_ctor_set(v___x_1631_, 3, v___y_1609_);
lean_ctor_set(v___x_1631_, 4, v___x_1630_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*5, v___y_1606_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*5 + 1, v___y_1608_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*5 + 2, v_isSilent_1595_);
v___x_1632_ = l_Lean_MessageLog_add(v___x_1631_, v_messages_1623_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 6, v___x_1632_);
v___x_1634_ = v___x_1627_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_env_1617_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_nextMacroScope_1618_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_ngen_1619_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_auxDeclNGen_1620_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_traceState_1621_);
lean_ctor_set(v_reuseFailAlloc_1637_, 5, v_cache_1622_);
lean_ctor_set(v_reuseFailAlloc_1637_, 6, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1637_, 7, v_infoState_1624_);
lean_ctor_set(v_reuseFailAlloc_1637_, 8, v_snapshotTasks_1625_);
v___x_1634_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_st_ref_put(v___y_1613_, v___x_1634_);
v___x_1636_ = lean_box(0);
v_a_1601_ = v___x_1636_;
goto v___jp_1600_;
}
}
}
v___jp_1639_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1662_; 
v___x_1648_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1593_);
v___x_1649_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1648_, v___y_1597_, v___y_1598_);
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1662_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1662_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_inc_ref_n(v___y_1642_, 2);
v___x_1654_ = l_Lean_FileMap_toPosition(v___y_1642_, v___y_1644_);
lean_dec(v___y_1644_);
v___x_1655_ = l_Lean_FileMap_toPosition(v___y_1642_, v___y_1647_);
lean_dec(v___y_1647_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 1);
lean_ctor_set(v___x_1652_, 0, v___x_1655_);
v___x_1657_ = v___x_1652_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1646_ == 0)
{
lean_dec_ref(v___y_1640_);
v___y_1605_ = v___x_1654_;
v___y_1606_ = v___y_1641_;
v___y_1607_ = v___y_1643_;
v___y_1608_ = v___y_1645_;
v___y_1609_ = v___x_1658_;
v___y_1610_ = v___x_1657_;
v___y_1611_ = v_a_1650_;
v___y_1612_ = v___y_1597_;
v___y_1613_ = v___y_1598_;
goto v___jp_1604_;
}
else
{
uint8_t v___x_1659_; 
lean_inc(v_a_1650_);
v___x_1659_ = l_Lean_MessageData_hasTag(v___y_1640_, v_a_1650_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref(v___x_1657_);
lean_dec_ref(v___x_1654_);
lean_dec(v_a_1650_);
v___x_1660_ = lean_box(0);
v_a_1601_ = v___x_1660_;
goto v___jp_1600_;
}
else
{
v___y_1605_ = v___x_1654_;
v___y_1606_ = v___y_1641_;
v___y_1607_ = v___y_1643_;
v___y_1608_ = v___y_1645_;
v___y_1609_ = v___x_1658_;
v___y_1610_ = v___x_1657_;
v___y_1611_ = v_a_1650_;
v___y_1612_ = v___y_1597_;
v___y_1613_ = v___y_1598_;
goto v___jp_1604_;
}
}
}
}
}
v___jp_1663_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Syntax_getTailPos_x3f(v___y_1665_, v___y_1666_);
lean_dec(v___y_1665_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_inc(v___y_1671_);
v___y_1640_ = v___y_1664_;
v___y_1641_ = v___y_1666_;
v___y_1642_ = v___y_1667_;
v___y_1643_ = v___y_1668_;
v___y_1644_ = v___y_1671_;
v___y_1645_ = v___y_1669_;
v___y_1646_ = v___y_1670_;
v___y_1647_ = v___y_1671_;
goto v___jp_1639_;
}
else
{
lean_object* v_val_1673_; 
v_val_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_val_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___y_1640_ = v___y_1664_;
v___y_1641_ = v___y_1666_;
v___y_1642_ = v___y_1667_;
v___y_1643_ = v___y_1668_;
v___y_1644_ = v___y_1671_;
v___y_1645_ = v___y_1669_;
v___y_1646_ = v___y_1670_;
v___y_1647_ = v_val_1673_;
goto v___jp_1639_;
}
}
v___jp_1674_:
{
lean_object* v_ref_1682_; lean_object* v___x_1683_; 
v_ref_1682_ = l_Lean_replaceRef(v_ref_1592_, v___y_1679_);
v___x_1683_ = l_Lean_Syntax_getPos_x3f(v_ref_1682_, v___y_1676_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_unsigned_to_nat(0u);
v___y_1664_ = v___y_1675_;
v___y_1665_ = v_ref_1682_;
v___y_1666_ = v___y_1676_;
v___y_1667_ = v___y_1677_;
v___y_1668_ = v___y_1678_;
v___y_1669_ = v___y_1681_;
v___y_1670_ = v___y_1680_;
v___y_1671_ = v___x_1684_;
goto v___jp_1663_;
}
else
{
lean_object* v_val_1685_; 
v_val_1685_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_val_1685_);
lean_dec_ref_known(v___x_1683_, 1);
v___y_1664_ = v___y_1675_;
v___y_1665_ = v_ref_1682_;
v___y_1666_ = v___y_1676_;
v___y_1667_ = v___y_1677_;
v___y_1668_ = v___y_1678_;
v___y_1669_ = v___y_1681_;
v___y_1670_ = v___y_1680_;
v___y_1671_ = v_val_1685_;
goto v___jp_1663_;
}
}
v___jp_1687_:
{
if (v___y_1694_ == 0)
{
v___y_1675_ = v___y_1689_;
v___y_1676_ = v___y_1693_;
v___y_1677_ = v___y_1688_;
v___y_1678_ = v___y_1690_;
v___y_1679_ = v___y_1691_;
v___y_1680_ = v___y_1692_;
v___y_1681_ = v_severity_1594_;
goto v___jp_1674_;
}
else
{
v___y_1675_ = v___y_1689_;
v___y_1676_ = v___y_1693_;
v___y_1677_ = v___y_1688_;
v___y_1678_ = v___y_1690_;
v___y_1679_ = v___y_1691_;
v___y_1680_ = v___y_1692_;
v___y_1681_ = v___x_1686_;
goto v___jp_1674_;
}
}
v___jp_1695_:
{
if (v___y_1696_ == 0)
{
lean_object* v_fileName_1697_; lean_object* v_fileMap_1698_; lean_object* v_options_1699_; lean_object* v_ref_1700_; uint8_t v_suppressElabErrors_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___f_1704_; uint8_t v___x_1705_; uint8_t v___x_1706_; 
v_fileName_1697_ = lean_ctor_get(v___y_1597_, 0);
v_fileMap_1698_ = lean_ctor_get(v___y_1597_, 1);
v_options_1699_ = lean_ctor_get(v___y_1597_, 2);
v_ref_1700_ = lean_ctor_get(v___y_1597_, 5);
v_suppressElabErrors_1701_ = lean_ctor_get_uint8(v___y_1597_, sizeof(void*)*14 + 1);
v___x_1702_ = lean_box(v_suppressElabErrors_1701_);
v___x_1703_ = lean_box(v___y_1696_);
v___f_1704_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1704_, 0, v___x_1702_);
lean_closure_set(v___f_1704_, 1, v___x_1703_);
v___x_1705_ = 1;
v___x_1706_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1594_, v___x_1705_);
if (v___x_1706_ == 0)
{
v___y_1688_ = v_fileMap_1698_;
v___y_1689_ = v___f_1704_;
v___y_1690_ = v_fileName_1697_;
v___y_1691_ = v_ref_1700_;
v___y_1692_ = v_suppressElabErrors_1701_;
v___y_1693_ = v___y_1696_;
v___y_1694_ = v___x_1706_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = l_Lean_warningAsError;
v___x_1708_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_options_1699_, v___x_1707_);
v___y_1688_ = v_fileMap_1698_;
v___y_1689_ = v___f_1704_;
v___y_1690_ = v_fileName_1697_;
v___y_1691_ = v_ref_1700_;
v___y_1692_ = v_suppressElabErrors_1701_;
v___y_1693_ = v___y_1696_;
v___y_1694_ = v___x_1708_;
goto v___jp_1687_;
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec_ref(v_msgData_1593_);
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v___y_1596_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1714_, lean_object* v_msgData_1715_, lean_object* v_severity_1716_, lean_object* v_isSilent_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v_severity_boxed_1722_; uint8_t v_isSilent_boxed_1723_; lean_object* v_res_1724_; 
v_severity_boxed_1722_ = lean_unbox(v_severity_1716_);
v_isSilent_boxed_1723_ = lean_unbox(v_isSilent_1717_);
v_res_1724_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1714_, v_msgData_1715_, v_severity_boxed_1722_, v_isSilent_boxed_1723_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v_ref_1714_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1725_, lean_object* v_msgData_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v___x_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = 2;
v___x_1732_ = 0;
v___x_1733_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1725_, v_msgData_1726_, v___x_1731_, v___x_1732_, v___y_1727_, v___y_1728_, v___y_1729_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1734_, lean_object* v_msgData_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1734_, v_msgData_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_ref_1734_);
return v_res_1740_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1744_ = l_Lean_MessageData_ofFormat(v___x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1745_, lean_object* v_as_1746_, size_t v_sz_1747_, size_t v_i_1748_, uint8_t v_b_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_snd_1755_; lean_object* v_snd_1756_; lean_object* v___y_1762_; uint8_t v___y_1763_; lean_object* v_a_1780_; uint8_t v___x_1783_; 
v___x_1783_ = lean_usize_dec_lt(v_i_1748_, v_sz_1747_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_box(v_b_1749_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___y_1750_);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
return v___x_1786_;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1788_; uint8_t v_recovering_1789_; 
v_a_1787_ = lean_array_uget_borrowed(v_as_1746_, v_i_1748_);
v___x_1788_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1787_);
v_recovering_1789_ = l_Lean_Syntax_isOfKind(v_a_1787_, v___x_1788_);
if (v_recovering_1789_ == 0)
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_a_1787_);
v___x_1791_ = l_Lean_Syntax_isOfKind(v_a_1787_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1787_);
v___x_1793_ = l_Lean_Syntax_isOfKind(v_a_1787_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1750_);
v___x_1795_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1787_, v___x_1794_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v_snd_1797_; lean_object* v___x_1798_; 
lean_dec_ref(v___y_1750_);
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v_snd_1797_ = lean_ctor_get(v_a_1796_, 1);
lean_inc(v_snd_1797_);
lean_dec(v_a_1796_);
v___x_1798_ = lean_box(v_b_1749_);
v_snd_1755_ = v___x_1798_;
v_snd_1756_ = v_snd_1797_;
goto v___jp_1754_;
}
else
{
lean_object* v_a_1799_; 
v_a_1799_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1795_, 1);
v_a_1780_ = v_a_1799_;
goto v___jp_1779_;
}
}
else
{
lean_object* v___x_1800_; 
lean_inc_ref(v___y_1750_);
lean_inc(v_a_1787_);
v___x_1800_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1787_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v_snd_1802_; lean_object* v___x_1803_; 
lean_dec_ref(v___y_1750_);
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v_snd_1802_ = lean_ctor_get(v_a_1801_, 1);
lean_inc(v_snd_1802_);
lean_dec(v_a_1801_);
v___x_1803_ = lean_box(v_recovering_1789_);
v_snd_1755_ = v___x_1803_;
v_snd_1756_ = v_snd_1802_;
goto v___jp_1754_;
}
else
{
lean_object* v_a_1804_; 
v_a_1804_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1800_, 1);
v_a_1780_ = v_a_1804_;
goto v___jp_1779_;
}
}
}
else
{
lean_object* v___x_1805_; 
lean_inc_ref(v___y_1750_);
lean_inc(v_a_1787_);
v___x_1805_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1787_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v_snd_1807_; lean_object* v___x_1808_; 
lean_dec_ref(v___y_1750_);
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v_snd_1807_ = lean_ctor_get(v_a_1806_, 1);
lean_inc(v_snd_1807_);
lean_dec(v_a_1806_);
v___x_1808_ = lean_box(v_recovering_1789_);
v_snd_1755_ = v___x_1808_;
v_snd_1756_ = v_snd_1807_;
goto v___jp_1754_;
}
else
{
lean_object* v_a_1809_; 
v_a_1809_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1805_, 1);
v_a_1780_ = v_a_1809_;
goto v___jp_1779_;
}
}
}
else
{
if (v_b_1749_ == 0)
{
lean_object* v___x_1810_; 
lean_inc_ref(v___y_1750_);
lean_inc(v_a_1787_);
v___x_1810_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1787_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v_snd_1812_; lean_object* v___x_1813_; 
lean_dec_ref(v___y_1750_);
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v_snd_1812_ = lean_ctor_get(v_a_1811_, 1);
lean_inc(v_snd_1812_);
lean_dec(v_a_1811_);
v___x_1813_ = lean_box(v_b_1749_);
v_snd_1755_ = v___x_1813_;
v_snd_1756_ = v_snd_1812_;
goto v___jp_1754_;
}
else
{
lean_object* v_a_1814_; 
v_a_1814_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1810_, 1);
v_a_1780_ = v_a_1814_;
goto v___jp_1779_;
}
}
else
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_box(v_b_1749_);
v_snd_1755_ = v___x_1815_;
v_snd_1756_ = v___y_1750_;
goto v___jp_1754_;
}
}
}
v___jp_1754_:
{
size_t v___x_1757_; size_t v___x_1758_; uint8_t v___x_1759_; 
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1748_, v___x_1757_);
v___x_1759_ = lean_unbox(v_snd_1755_);
lean_dec(v_snd_1755_);
v_i_1748_ = v___x_1758_;
v_b_1749_ = v___x_1759_;
v___y_1750_ = v_snd_1756_;
goto _start;
}
v___jp_1761_:
{
if (v___y_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = l_Lean_Exception_getRef(v___y_1762_);
v___x_1765_ = l_Lean_Exception_toMessageData(v___y_1762_);
v___x_1766_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1764_, v___x_1765_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___x_1764_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v_snd_1768_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v_snd_1768_ = lean_ctor_get(v_a_1767_, 1);
lean_inc(v_snd_1768_);
lean_dec(v_a_1767_);
v___x_1769_ = lean_box(v_recovering_1745_);
v_snd_1755_ = v___x_1769_;
v_snd_1756_ = v_snd_1768_;
goto v___jp_1754_;
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1766_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v___x_1778_; 
lean_dec_ref(v___y_1750_);
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___y_1762_);
return v___x_1778_;
}
}
v___jp_1779_:
{
uint8_t v___x_1781_; 
v___x_1781_ = l_Lean_Exception_isInterrupt(v_a_1780_);
if (v___x_1781_ == 0)
{
uint8_t v___x_1782_; 
lean_inc_ref(v_a_1780_);
v___x_1782_ = l_Lean_Exception_isRuntime(v_a_1780_);
v___y_1762_ = v_a_1780_;
v___y_1763_ = v___x_1782_;
goto v___jp_1761_;
}
else
{
v___y_1762_ = v_a_1780_;
v___y_1763_ = v___x_1781_;
goto v___jp_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1816_, lean_object* v_as_1817_, lean_object* v_sz_1818_, lean_object* v_i_1819_, lean_object* v_b_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v_recovering_boxed_1825_; size_t v_sz_boxed_1826_; size_t v_i_boxed_1827_; uint8_t v_b_boxed_1828_; lean_object* v_res_1829_; 
v_recovering_boxed_1825_ = lean_unbox(v_recovering_1816_);
v_sz_boxed_1826_ = lean_unbox_usize(v_sz_1818_);
lean_dec(v_sz_1818_);
v_i_boxed_1827_ = lean_unbox_usize(v_i_1819_);
lean_dec(v_i_1819_);
v_b_boxed_1828_ = lean_unbox(v_b_1820_);
v_res_1829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1825_, v_as_1817_, v_sz_boxed_1826_, v_i_boxed_1827_, v_b_boxed_1828_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_as_1817_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_ref_1834_; lean_object* v___x_1835_; lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1844_; 
v_ref_1834_ = lean_ctor_get(v___y_1831_, 5);
v___x_1835_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1830_, v___y_1831_, v___y_1832_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_inc(v_ref_1834_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_ref_1834_);
lean_ctor_set(v___x_1840_, 1, v_a_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 1);
lean_ctor_set(v___x_1838_, 0, v___x_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1850_, lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_fileName_1855_; lean_object* v_fileMap_1856_; lean_object* v_options_1857_; lean_object* v_currRecDepth_1858_; lean_object* v_maxRecDepth_1859_; lean_object* v_ref_1860_; lean_object* v_currNamespace_1861_; lean_object* v_openDecls_1862_; lean_object* v_initHeartbeats_1863_; lean_object* v_maxHeartbeats_1864_; lean_object* v_quotContext_1865_; lean_object* v_currMacroScope_1866_; uint8_t v_diag_1867_; lean_object* v_cancelTk_x3f_1868_; uint8_t v_suppressElabErrors_1869_; lean_object* v_inheritedTraceOptions_1870_; lean_object* v_ref_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_fileName_1855_ = lean_ctor_get(v___y_1852_, 0);
v_fileMap_1856_ = lean_ctor_get(v___y_1852_, 1);
v_options_1857_ = lean_ctor_get(v___y_1852_, 2);
v_currRecDepth_1858_ = lean_ctor_get(v___y_1852_, 3);
v_maxRecDepth_1859_ = lean_ctor_get(v___y_1852_, 4);
v_ref_1860_ = lean_ctor_get(v___y_1852_, 5);
v_currNamespace_1861_ = lean_ctor_get(v___y_1852_, 6);
v_openDecls_1862_ = lean_ctor_get(v___y_1852_, 7);
v_initHeartbeats_1863_ = lean_ctor_get(v___y_1852_, 8);
v_maxHeartbeats_1864_ = lean_ctor_get(v___y_1852_, 9);
v_quotContext_1865_ = lean_ctor_get(v___y_1852_, 10);
v_currMacroScope_1866_ = lean_ctor_get(v___y_1852_, 11);
v_diag_1867_ = lean_ctor_get_uint8(v___y_1852_, sizeof(void*)*14);
v_cancelTk_x3f_1868_ = lean_ctor_get(v___y_1852_, 12);
v_suppressElabErrors_1869_ = lean_ctor_get_uint8(v___y_1852_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1870_ = lean_ctor_get(v___y_1852_, 13);
v_ref_1871_ = l_Lean_replaceRef(v_ref_1850_, v_ref_1860_);
lean_inc_ref(v_inheritedTraceOptions_1870_);
lean_inc(v_cancelTk_x3f_1868_);
lean_inc(v_currMacroScope_1866_);
lean_inc(v_quotContext_1865_);
lean_inc(v_maxHeartbeats_1864_);
lean_inc(v_initHeartbeats_1863_);
lean_inc(v_openDecls_1862_);
lean_inc(v_currNamespace_1861_);
lean_inc(v_maxRecDepth_1859_);
lean_inc(v_currRecDepth_1858_);
lean_inc_ref(v_options_1857_);
lean_inc_ref(v_fileMap_1856_);
lean_inc_ref(v_fileName_1855_);
v___x_1872_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1872_, 0, v_fileName_1855_);
lean_ctor_set(v___x_1872_, 1, v_fileMap_1856_);
lean_ctor_set(v___x_1872_, 2, v_options_1857_);
lean_ctor_set(v___x_1872_, 3, v_currRecDepth_1858_);
lean_ctor_set(v___x_1872_, 4, v_maxRecDepth_1859_);
lean_ctor_set(v___x_1872_, 5, v_ref_1871_);
lean_ctor_set(v___x_1872_, 6, v_currNamespace_1861_);
lean_ctor_set(v___x_1872_, 7, v_openDecls_1862_);
lean_ctor_set(v___x_1872_, 8, v_initHeartbeats_1863_);
lean_ctor_set(v___x_1872_, 9, v_maxHeartbeats_1864_);
lean_ctor_set(v___x_1872_, 10, v_quotContext_1865_);
lean_ctor_set(v___x_1872_, 11, v_currMacroScope_1866_);
lean_ctor_set(v___x_1872_, 12, v_cancelTk_x3f_1868_);
lean_ctor_set(v___x_1872_, 13, v_inheritedTraceOptions_1870_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*14, v_diag_1867_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*14 + 1, v_suppressElabErrors_1869_);
v___x_1873_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1851_, v___x_1872_, v___y_1853_);
lean_dec_ref_known(v___x_1872_, 14);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1874_, lean_object* v_msg_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1874_, v_msg_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v_ref_1874_);
return v_res_1879_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1887_ = l_Lean_stringToMessageData(v___x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1892_);
v___x_1897_ = l_Lean_Syntax_isOfKind(v_x_1892_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1899_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1892_, v___x_1898_, v_a_1893_, v_a_1894_);
lean_dec(v_x_1892_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v_recovering_1903_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = l_Lean_Syntax_getArg(v_x_1892_, v___x_1900_);
v___x_1902_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1903_ = l_Lean_Syntax_isOfKind(v___x_1901_, v___x_1902_);
if (v_recovering_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1905_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1892_, v___x_1904_, v_a_1893_, v_a_1894_);
lean_dec(v_x_1892_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_xs_1908_; uint8_t v_recovering_1909_; lean_object* v___x_1910_; size_t v_sz_1911_; size_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1906_ = lean_unsigned_to_nat(1u);
v___x_1907_ = l_Lean_Syntax_getArg(v_x_1892_, v___x_1906_);
lean_dec(v_x_1892_);
v_xs_1908_ = l_Lean_Syntax_getArgs(v___x_1907_);
lean_dec(v___x_1907_);
v_recovering_1909_ = 0;
v___x_1910_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1908_);
lean_dec_ref(v_xs_1908_);
v_sz_1911_ = lean_array_size(v___x_1910_);
v___x_1912_ = ((size_t)0ULL);
v___x_1913_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1903_, v___x_1910_, v_sz_1911_, v___x_1912_, v_recovering_1909_, v___x_1913_, v_a_1893_, v_a_1894_);
lean_dec_ref(v___x_1910_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1925_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1925_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1925_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_snd_1919_; lean_object* v_items_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v_snd_1919_ = lean_ctor_get(v_a_1915_, 1);
lean_inc(v_snd_1919_);
lean_dec(v_a_1915_);
v_items_1920_ = lean_ctor_get(v_snd_1919_, 5);
lean_inc_ref(v_items_1920_);
lean_dec(v_snd_1919_);
v___x_1921_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1920_);
lean_dec_ref(v_items_1920_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1921_);
v___x_1923_ = v___x_1917_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_a_1926_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1914_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1914_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lake_Toml_elabToml(v_x_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1939_, lean_object* v_ref_1940_, lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1940_, v_msg_1941_, v___y_1942_, v___y_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_ref_1947_, lean_object* v_msg_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1946_, v_ref_1947_, v_msg_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v_ref_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1953_, lean_object* v_msg_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1954_, v___y_1955_, v___y_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_msg_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1959_, v_msg_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1964_;
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
