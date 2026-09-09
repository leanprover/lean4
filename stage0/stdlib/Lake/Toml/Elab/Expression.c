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
lean_object* v_toCold_188_; lean_object* v_currRecDepth_189_; lean_object* v_ref_190_; uint8_t v_diag_191_; uint8_t v_suppressElabErrors_192_; lean_object* v_ref_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_toCold_188_ = lean_ctor_get(v___y_185_, 0);
v_currRecDepth_189_ = lean_ctor_get(v___y_185_, 1);
v_ref_190_ = lean_ctor_get(v___y_185_, 2);
v_diag_191_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3);
v_suppressElabErrors_192_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 1);
v_ref_193_ = l_Lean_replaceRef(v_ref_182_, v_ref_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_toCold_188_);
v___x_194_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_194_, 0, v_toCold_188_);
lean_ctor_set(v___x_194_, 1, v_currRecDepth_189_);
lean_ctor_set(v___x_194_, 2, v_ref_193_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*3, v_diag_191_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*3 + 1, v_suppressElabErrors_192_);
v___x_195_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_183_, v___x_194_, v___y_186_);
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
uint8_t v___x_2932__boxed_402_; size_t v_i_boxed_403_; size_t v_stop_boxed_404_; lean_object* v_res_405_; 
v___x_2932__boxed_402_ = lean_unbox(v___x_397_);
v_i_boxed_403_ = lean_unbox_usize(v_i_399_);
lean_dec(v_i_399_);
v_stop_boxed_404_ = lean_unbox_usize(v_stop_400_);
lean_dec(v_stop_400_);
v_res_405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2932__boxed_402_, v_as_398_, v_i_boxed_403_, v_stop_boxed_404_, v_b_401_);
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
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
v___x_790_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4));
v___x_798_ = l_Lean_stringToMessageData(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___y_805_; lean_object* v_keyTys_806_; lean_object* v_arrKeyTys_807_; lean_object* v_arrParents_808_; lean_object* v_currArrKey_809_; lean_object* v_items_810_; lean_object* v_toCold_822_; lean_object* v_currRecDepth_823_; lean_object* v_ref_824_; uint8_t v_diag_825_; uint8_t v_suppressElabErrors_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v_ref_829_; lean_object* v___x_830_; 
v_toCold_822_ = lean_ctor_get(v_a_801_, 0);
v_currRecDepth_823_ = lean_ctor_get(v_a_801_, 1);
v_ref_824_ = lean_ctor_get(v_a_801_, 2);
v_diag_825_ = lean_ctor_get_uint8(v_a_801_, sizeof(void*)*3);
v_suppressElabErrors_826_ = lean_ctor_get_uint8(v_a_801_, sizeof(void*)*3 + 1);
v___x_827_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_799_);
v___x_828_ = l_Lean_Syntax_isOfKind(v_x_799_, v___x_827_);
v_ref_829_ = l_Lean_replaceRef(v_x_799_, v_ref_824_);
lean_inc(v_currRecDepth_823_);
lean_inc_ref(v_toCold_822_);
v___x_830_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_830_, 0, v_toCold_822_);
lean_ctor_set(v___x_830_, 1, v_currRecDepth_823_);
lean_ctor_set(v___x_830_, 2, v_ref_829_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*3, v_diag_825_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*3 + 1, v_suppressElabErrors_826_);
if (v___x_828_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5);
v___x_832_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_799_, v___x_831_, v_a_800_, v___x_830_, v_a_802_);
lean_dec_ref_known(v___x_830_, 3);
lean_dec_ref(v_a_800_);
lean_dec(v_x_799_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___y_836_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = l_Lean_Syntax_getArg(v_x_799_, v___x_833_);
v___x_904_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_834_);
v___x_905_ = l_Lean_Syntax_isOfKind(v___x_834_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec(v_x_799_);
v___x_906_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_907_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_834_, v___x_906_, v_a_800_, v___x_830_, v_a_802_);
lean_dec_ref_known(v___x_830_, 3);
lean_dec_ref(v_a_800_);
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
lean_dec(v_x_799_);
v___x_840_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_841_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_834_, v___x_840_, v_a_800_, v___x_830_, v_a_802_);
lean_dec_ref_known(v___x_830_, 3);
lean_dec_ref(v_a_800_);
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
v___x_848_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_847_, v_a_800_, v___x_830_, v_a_802_);
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
v___x_855_ = l_Lake_Toml_elabSimpleKey(v_tailKey_846_, v___x_830_, v_a_802_);
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
v___y_805_ = v___x_862_;
v_keyTys_806_ = v_keyTys_857_;
v_arrKeyTys_807_ = v_arrKeyTys_858_;
v_arrParents_808_ = v_arrParents_859_;
v_currArrKey_809_ = v_currArrKey_860_;
v_items_810_ = v_items_861_;
goto v___jp_804_;
}
else
{
lean_object* v___x_869_; uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
lean_dec(v_x_799_);
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
v___x_883_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_846_, v___x_882_, v_snd_851_, v___x_830_, v_a_802_);
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
v___y_805_ = v___x_862_;
v_keyTys_806_ = v_keyTys_857_;
v_arrKeyTys_807_ = v_arrKeyTys_858_;
v_arrParents_808_ = v_arrParents_859_;
v_currArrKey_809_ = v_currArrKey_860_;
v_items_810_ = v_items_861_;
goto v___jp_804_;
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
lean_dec(v_x_799_);
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
lean_dec(v_x_799_);
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
v___jp_804_:
{
lean_object* v___x_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_811_ = lean_box(0);
v___x_812_ = 1;
v___x_813_ = lean_box(v___x_812_);
lean_inc_n(v___y_805_, 2);
v___x_814_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_805_, v___x_813_, v_keyTys_806_);
v___x_815_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc(v_x_799_);
v___x_816_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_816_, 0, v_x_799_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_817_, 0, v_x_799_);
lean_ctor_set(v___x_817_, 1, v___y_805_);
lean_ctor_set(v___x_817_, 2, v___x_816_);
v___x_818_ = lean_array_push(v_items_810_, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_819_, 0, v___x_814_);
lean_ctor_set(v___x_819_, 1, v_arrKeyTys_807_);
lean_ctor_set(v___x_819_, 2, v_arrParents_808_);
lean_ctor_set(v___x_819_, 3, v_currArrKey_809_);
lean_ctor_set(v___x_819_, 4, v___y_805_);
lean_ctor_set(v___x_819_, 5, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_811_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
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
lean_object* v_toCold_939_; lean_object* v_currRecDepth_940_; lean_object* v_ref_941_; uint8_t v_diag_942_; uint8_t v_suppressElabErrors_943_; lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v_ref_946_; lean_object* v___x_947_; lean_object* v___y_949_; 
v_toCold_939_ = lean_ctor_get(v_a_936_, 0);
v_currRecDepth_940_ = lean_ctor_get(v_a_936_, 1);
v_ref_941_ = lean_ctor_get(v_a_936_, 2);
v_diag_942_ = lean_ctor_get_uint8(v_a_936_, sizeof(void*)*3);
v_suppressElabErrors_943_ = lean_ctor_get_uint8(v_a_936_, sizeof(void*)*3 + 1);
v___x_944_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_934_);
v___x_945_ = l_Lean_Syntax_isOfKind(v_x_934_, v___x_944_);
v_ref_946_ = l_Lean_replaceRef(v_x_934_, v_ref_941_);
lean_inc(v_currRecDepth_940_);
lean_inc_ref(v_toCold_939_);
v___x_947_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_947_, 0, v_toCold_939_);
lean_ctor_set(v___x_947_, 1, v_currRecDepth_940_);
lean_ctor_set(v___x_947_, 2, v_ref_946_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*3, v_diag_942_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*3 + 1, v_suppressElabErrors_943_);
if (v___x_945_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_957_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_934_, v___x_956_, v_a_935_, v___x_947_, v_a_937_);
lean_dec_ref_known(v___x_947_, 3);
lean_dec_ref(v_a_935_);
lean_dec(v_x_934_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___y_963_; 
v___x_958_ = lean_unsigned_to_nat(2u);
v___x_959_ = l_Lean_Syntax_getArg(v_x_934_, v___x_958_);
v___x_960_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_959_);
v___x_961_ = l_Lean_Syntax_isOfKind(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v___x_959_);
v___x_1097_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1098_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_934_, v___x_1097_, v_a_935_, v___x_947_, v_a_937_);
lean_dec_ref_known(v___x_947_, 3);
lean_dec_ref(v_a_935_);
lean_dec(v_x_934_);
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
v___x_968_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_934_, v___x_967_, v_a_935_, v___x_947_, v_a_937_);
lean_dec_ref_known(v___x_947_, 3);
lean_dec_ref(v_a_935_);
lean_dec(v_x_934_);
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
v___x_976_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_975_, v_a_935_, v___x_947_, v_a_937_);
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
v___x_983_ = l_Lake_Toml_elabSimpleKey(v_tailKey_974_, v___x_947_, v_a_937_);
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
lean_dec(v_x_934_);
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
v___x_1008_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_934_, 2);
v___x_1009_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_x_934_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_mk_empty_array_with_capacity(v___x_972_);
v___x_1011_ = lean_array_push(v___x_1010_, v___x_1009_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_x_934_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
lean_inc_n(v___x_993_, 2);
v___x_1013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1013_, 0, v_x_934_);
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
lean_dec(v_x_934_);
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
lean_dec(v_x_934_);
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
v___x_1044_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_974_, v___x_1043_, v_snd_979_, v___x_947_, v_a_937_);
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
v___x_1056_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_934_, 2);
v___x_1057_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_x_934_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_mk_empty_array_with_capacity(v___x_972_);
v___x_1059_ = lean_array_push(v___x_1058_, v___x_1057_);
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_x_934_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1061_, 0, v_x_934_);
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
lean_dec(v_x_934_);
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
lean_dec(v_x_934_);
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
v___x_955_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_954_, v___x_947_, v_a_937_);
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
v___x_1127_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1142_, lean_object* v_as_1143_, size_t v_i_1144_, size_t v_stop_1145_, lean_object* v_b_1146_){
_start:
{
lean_object* v___y_1148_; uint8_t v___x_1152_; 
v___x_1152_ = lean_usize_dec_eq(v_i_1144_, v_stop_1145_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1156_; 
v___x_1153_ = lean_array_uget_borrowed(v_as_1143_, v_i_1144_);
v_fst_1154_ = lean_ctor_get(v___x_1153_, 0);
v_snd_1155_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_fst_1154_);
v___x_1156_ = l_Lean_Name_components(v_fst_1154_);
if (lean_obj_tag(v___x_1156_) == 0)
{
v___y_1148_ = v_b_1146_;
goto v___jp_1147_;
}
else
{
lean_object* v_head_1157_; lean_object* v_tail_1158_; lean_object* v___x_1159_; 
v_head_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_head_1157_);
v_tail_1158_ = lean_ctor_get(v___x_1156_, 1);
lean_inc(v_tail_1158_);
lean_dec_ref_known(v___x_1156_, 2);
lean_inc(v_snd_1155_);
lean_inc(v_ref_1142_);
v___x_1159_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1146_, v_ref_1142_, v_head_1157_, v_tail_1158_, v_snd_1155_);
v___y_1148_ = v___x_1159_;
goto v___jp_1147_;
}
}
else
{
lean_dec(v_ref_1142_);
return v_b_1146_;
}
v___jp_1147_:
{
size_t v___x_1149_; size_t v___x_1150_; 
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1144_, v___x_1149_);
v_i_1144_ = v___x_1150_;
v_b_1146_ = v___y_1148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1160_, size_t v_i_1161_, lean_object* v_bs_1162_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1161_, v_sz_1160_);
if (v___x_1163_ == 0)
{
return v_bs_1162_;
}
else
{
lean_object* v_v_1164_; lean_object* v___x_1165_; lean_object* v_bs_x27_1166_; lean_object* v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
v_v_1164_ = lean_array_uget(v_bs_1162_, v_i_1161_);
v___x_1165_ = lean_unsigned_to_nat(0u);
v_bs_x27_1166_ = lean_array_uset(v_bs_1162_, v_i_1161_, v___x_1165_);
v___x_1167_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1164_);
v___x_1168_ = ((size_t)1ULL);
v___x_1169_ = lean_usize_add(v_i_1161_, v___x_1168_);
v___x_1170_ = lean_array_uset(v_bs_x27_1166_, v_i_1161_, v___x_1167_);
v_i_1161_ = v___x_1169_;
v_bs_1162_ = v___x_1170_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1172_){
_start:
{
switch(lean_obj_tag(v_a_1172_))
{
case 6:
{
lean_object* v_xs_1173_; lean_object* v_ref_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1202_; 
v_xs_1173_ = lean_ctor_get(v_a_1172_, 1);
v_ref_1174_ = lean_ctor_get(v_a_1172_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_a_1172_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1176_ = v_a_1172_;
v_isShared_1177_ = v_isSharedCheck_1202_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_xs_1173_);
lean_inc(v_ref_1174_);
lean_dec(v_a_1172_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1202_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v_items_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v_items_1178_ = lean_ctor_get(v_xs_1173_, 0);
lean_inc_ref(v_items_1178_);
lean_dec_ref(v_xs_1173_);
v___x_1179_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = lean_array_get_size(v_items_1178_);
v___x_1182_ = lean_nat_dec_lt(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref(v_items_1178_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1179_);
v___x_1184_ = v___x_1176_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_ref_1174_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___x_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
else
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_nat_dec_le(v___x_1181_, v___x_1181_);
if (v___x_1186_ == 0)
{
if (v___x_1182_ == 0)
{
lean_object* v___x_1188_; 
lean_dec_ref(v_items_1178_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1179_);
v___x_1188_ = v___x_1176_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_ref_1174_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1179_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
else
{
size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1190_ = ((size_t)0ULL);
v___x_1191_ = lean_usize_of_nat(v___x_1181_);
lean_inc(v_ref_1174_);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1174_, v_items_1178_, v___x_1190_, v___x_1191_, v___x_1179_);
lean_dec_ref(v_items_1178_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1192_);
v___x_1194_ = v___x_1176_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_ref_1174_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = lean_usize_of_nat(v___x_1181_);
lean_inc(v_ref_1174_);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1174_, v_items_1178_, v___x_1196_, v___x_1197_, v___x_1179_);
lean_dec_ref(v_items_1178_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1198_);
v___x_1200_ = v___x_1176_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_ref_1174_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
case 5:
{
lean_object* v_ref_1203_; lean_object* v_xs_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1214_; 
v_ref_1203_ = lean_ctor_get(v_a_1172_, 0);
v_xs_1204_ = lean_ctor_get(v_a_1172_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_a_1172_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1206_ = v_a_1172_;
v_isShared_1207_ = v_isSharedCheck_1214_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_xs_1204_);
lean_inc(v_ref_1203_);
lean_dec(v_a_1172_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1214_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
size_t v_sz_1208_; size_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v_sz_1208_ = lean_array_size(v_xs_1204_);
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1208_, v___x_1209_, v_xs_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1210_);
v___x_1212_ = v___x_1206_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_ref_1203_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
default: 
{
return v_a_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1215_, lean_object* v___x_1216_, lean_object* v_v_x3f_1217_){
_start:
{
if (lean_obj_tag(v_v_x3f_1217_) == 1)
{
lean_object* v_val_1218_; 
v_val_1218_ = lean_ctor_get(v_v_x3f_1217_, 0);
lean_inc(v_val_1218_);
lean_dec_ref_known(v_v_x3f_1217_, 1);
switch(lean_obj_tag(v_val_1218_))
{
case 6:
{
lean_object* v_ref_1219_; lean_object* v_xs_1220_; lean_object* v___x_1221_; 
v_ref_1219_ = lean_ctor_get(v_val_1218_, 0);
lean_inc(v_ref_1219_);
v_xs_1220_ = lean_ctor_get(v_val_1218_, 1);
lean_inc_ref(v_xs_1220_);
lean_dec_ref_known(v_val_1218_, 2);
v___x_1221_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1215_);
if (lean_obj_tag(v___x_1221_) == 6)
{
lean_object* v_xs_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1231_; 
v_xs_1222_ = lean_ctor_get(v___x_1221_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1221_, 0);
lean_dec(v_unused_1232_);
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_xs_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_items_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; 
v_items_1226_ = lean_ctor_get(v_xs_1222_, 0);
lean_inc_ref(v_items_1226_);
lean_dec_ref(v_xs_1222_);
v___x_1227_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1216_, v_xs_1220_, v_items_1226_);
lean_dec_ref(v_items_1226_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___x_1227_);
lean_ctor_set(v___x_1224_, 0, v_ref_1219_);
v___x_1229_ = v___x_1224_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_ref_1219_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
else
{
lean_dec_ref(v_xs_1220_);
lean_dec(v_ref_1219_);
lean_dec_ref(v___x_1216_);
return v___x_1221_;
}
}
case 5:
{
lean_object* v_ref_1233_; lean_object* v_xs_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v___x_1216_);
v_ref_1233_ = lean_ctor_get(v_val_1218_, 0);
v_xs_1234_ = lean_ctor_get(v_val_1218_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_val_1218_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1236_ = v_val_1218_;
v_isShared_1237_ = v_isSharedCheck_1253_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_xs_1234_);
lean_inc(v_ref_1233_);
lean_dec(v_val_1218_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1253_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; 
v___x_1238_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1215_);
if (lean_obj_tag(v___x_1238_) == 5)
{
lean_object* v_xs_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1247_; 
lean_del_object(v___x_1236_);
v_xs_1239_ = lean_ctor_get(v___x_1238_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1238_, 0);
lean_dec(v_unused_1248_);
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_xs_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = l_Array_append___redArg(v_xs_1234_, v_xs_1239_);
lean_dec_ref(v_xs_1239_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v___x_1243_);
lean_ctor_set(v___x_1241_, 0, v_ref_1233_);
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_ref_1233_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_array_push(v_xs_1234_, v___x_1238_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v___x_1249_);
v___x_1251_ = v___x_1236_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_ref_1233_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
default: 
{
lean_object* v___x_1254_; 
lean_dec(v_val_1218_);
lean_dec_ref(v___x_1216_);
v___x_1254_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1215_);
return v___x_1254_;
}
}
}
else
{
lean_object* v___x_1255_; 
lean_dec(v_v_x3f_1217_);
lean_dec_ref(v___x_1216_);
v___x_1255_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1215_);
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1256_, lean_object* v_k_1257_, lean_object* v_t_1258_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1258_);
lean_inc(v_k_1257_);
v___x_1260_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1259_, v_k_1257_, v_t_1258_);
if (lean_obj_tag(v___x_1260_) == 1)
{
lean_object* v_val_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_k_1257_);
v_val_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1296_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_val_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1296_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_items_1265_; lean_object* v_indices_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1295_; 
v_items_1265_ = lean_ctor_get(v_t_1258_, 0);
v_indices_1266_ = lean_ctor_get(v_t_1258_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_t_1258_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1268_ = v_t_1258_;
v_isShared_1269_ = v_isSharedCheck_1295_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_indices_1266_);
lean_inc(v_items_1265_);
lean_dec(v_t_1258_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1295_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = lean_array_get_size(v_items_1265_);
v___x_1271_ = lean_nat_dec_lt(v_val_1261_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1273_; 
lean_del_object(v___x_1263_);
lean_dec(v_val_1261_);
lean_dec_ref(v_newV_1256_);
if (v_isShared_1269_ == 0)
{
v___x_1273_ = v___x_1268_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_items_1265_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_indices_1266_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
else
{
lean_object* v_v_1275_; lean_object* v_fst_1276_; lean_object* v_snd_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1294_; 
v_v_1275_ = lean_array_fget(v_items_1265_, v_val_1261_);
v_fst_1276_ = lean_ctor_get(v_v_1275_, 0);
v_snd_1277_ = lean_ctor_get(v_v_1275_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_v_1275_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1279_ = v_v_1275_;
v_isShared_1280_ = v_isSharedCheck_1294_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_snd_1277_);
lean_inc(v_fst_1276_);
lean_dec(v_v_1275_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1294_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v_xs_x27_1282_; lean_object* v___x_1284_; 
v___x_1281_ = lean_box(0);
v_xs_x27_1282_ = lean_array_fset(v_items_1265_, v_val_1261_, v___x_1281_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v_snd_1277_);
v___x_1284_ = v___x_1263_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_snd_1277_);
v___x_1284_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1256_, v___x_1259_, v___x_1284_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v___x_1285_);
v___x_1287_ = v___x_1279_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_fst_1276_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = lean_array_fset(v_xs_x27_1282_, v_val_1261_, v___x_1287_);
lean_dec(v_val_1261_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1288_);
v___x_1290_ = v___x_1268_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_indices_1266_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
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
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec(v___x_1260_);
v___x_1297_ = lean_box(0);
v___x_1298_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1256_, v___x_1259_, v___x_1297_);
v___x_1299_ = l_Lake_Toml_RBDict_push___redArg(v___x_1259_, v_k_1257_, v___x_1298_, v_t_1258_);
return v___x_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1300_, lean_object* v_head_1301_, lean_object* v_tail_1302_, lean_object* v_newV_1303_, lean_object* v___x_1304_, lean_object* v_v_x3f_1305_){
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
lean_dec_ref(v_newV_1303_);
lean_dec(v_tail_1302_);
lean_dec(v_head_1301_);
lean_dec(v_kRef_1300_);
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
v___x_1330_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1326_, v_kRef_1300_, v_head_1301_, v_tail_1302_, v_newV_1303_);
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
lean_dec_ref(v_newV_1303_);
lean_dec(v_tail_1302_);
lean_dec(v_head_1301_);
v___x_1335_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1304_);
v___x_1336_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_kRef_1300_);
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
v___x_1345_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1341_, v_kRef_1300_, v_head_1301_, v_tail_1302_, v_newV_1303_);
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
v___x_1350_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1304_);
lean_inc(v_kRef_1300_);
v___x_1351_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1350_, v_kRef_1300_, v_head_1301_, v_tail_1302_, v_newV_1303_);
v___x_1352_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_kRef_1300_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
return v___x_1352_;
}
}
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_v_x3f_1305_);
v___x_1353_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1304_);
lean_inc(v_kRef_1300_);
v___x_1354_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1353_, v_kRef_1300_, v_head_1301_, v_tail_1302_, v_newV_1303_);
v___x_1355_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_kRef_1300_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1356_, lean_object* v_head_1357_, lean_object* v_tail_1358_, lean_object* v_newV_1359_, lean_object* v_k_1360_, lean_object* v_t_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
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
v___x_1388_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1356_, v_head_1357_, v_tail_1358_, v_newV_1359_, v___x_1362_, v___x_1387_);
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
v___x_1401_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1356_, v_head_1357_, v_tail_1358_, v_newV_1359_, v___x_1362_, v___x_1400_);
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
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0___boxed(lean_object* v_kRef_1426_, lean_object* v_head_1427_, lean_object* v_tail_1428_, lean_object* v_newV_1429_, lean_object* v___x_1430_, lean_object* v_v_x3f_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1426_, v_head_1427_, v_tail_1428_, v_newV_1429_, v___x_1430_, v_v_x3f_1431_);
lean_dec_ref(v___x_1430_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1433_, size_t v_i_1434_, size_t v_stop_1435_, lean_object* v_b_1436_){
_start:
{
lean_object* v___y_1438_; uint8_t v___x_1442_; 
v___x_1442_ = lean_usize_dec_eq(v_i_1434_, v_stop_1435_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v_ref_1444_; lean_object* v_key_1445_; lean_object* v_val_1446_; lean_object* v___x_1447_; 
v___x_1443_ = lean_array_uget_borrowed(v_as_1433_, v_i_1434_);
v_ref_1444_ = lean_ctor_get(v___x_1443_, 0);
v_key_1445_ = lean_ctor_get(v___x_1443_, 1);
v_val_1446_ = lean_ctor_get(v___x_1443_, 2);
lean_inc(v_key_1445_);
v___x_1447_ = l_Lean_Name_components(v_key_1445_);
if (lean_obj_tag(v___x_1447_) == 0)
{
v___y_1438_ = v_b_1436_;
goto v___jp_1437_;
}
else
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v___x_1450_; 
v_head_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_head_1448_);
v_tail_1449_ = lean_ctor_get(v___x_1447_, 1);
lean_inc(v_tail_1449_);
lean_dec_ref_known(v___x_1447_, 2);
lean_inc_ref(v_val_1446_);
lean_inc(v_ref_1444_);
v___x_1450_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1436_, v_ref_1444_, v_head_1448_, v_tail_1449_, v_val_1446_);
v___y_1438_ = v___x_1450_;
goto v___jp_1437_;
}
}
else
{
return v_b_1436_;
}
v___jp_1437_:
{
size_t v___x_1439_; size_t v___x_1440_; 
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_add(v_i_1434_, v___x_1439_);
v_i_1434_ = v___x_1440_;
v_b_1436_ = v___y_1438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1451_, lean_object* v_i_1452_, lean_object* v_stop_1453_, lean_object* v_b_1454_){
_start:
{
size_t v_i_boxed_1455_; size_t v_stop_boxed_1456_; lean_object* v_res_1457_; 
v_i_boxed_1455_ = lean_unbox_usize(v_i_1452_);
lean_dec(v_i_1452_);
v_stop_boxed_1456_ = lean_unbox_usize(v_stop_1453_);
lean_dec(v_stop_1453_);
v_res_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1451_, v_i_boxed_1455_, v_stop_boxed_1456_, v_b_1454_);
lean_dec_ref(v_as_1451_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1458_){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1459_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_array_get_size(v_items_1458_);
v___x_1462_ = lean_nat_dec_lt(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
return v___x_1459_;
}
else
{
uint8_t v___x_1463_; 
v___x_1463_ = lean_nat_dec_le(v___x_1461_, v___x_1461_);
if (v___x_1463_ == 0)
{
if (v___x_1462_ == 0)
{
return v___x_1459_;
}
else
{
size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = lean_usize_of_nat(v___x_1461_);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1458_, v___x_1464_, v___x_1465_, v___x_1459_);
return v___x_1466_;
}
}
else
{
size_t v___x_1467_; size_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = lean_usize_of_nat(v___x_1461_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1458_, v___x_1467_, v___x_1468_, v___x_1459_);
return v___x_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1470_);
lean_dec_ref(v_items_1470_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1474_);
lean_inc_ref(v_a_1473_);
v___x_1477_ = lean_apply_4(v_x_1472_, v___x_1476_, v_a_1473_, v_a_1474_, lean_box(0));
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1488_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_snd_1482_; lean_object* v_items_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v_snd_1482_ = lean_ctor_get(v_a_1478_, 1);
lean_inc(v_snd_1482_);
lean_dec(v_a_1478_);
v_items_1483_ = lean_ctor_get(v_snd_1482_, 5);
lean_inc_ref(v_items_1483_);
lean_dec(v_snd_1482_);
v___x_1484_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1483_);
lean_dec_ref(v_items_1483_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1484_);
v___x_1486_ = v___x_1480_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_a_1489_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1477_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1477_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1497_, v_a_1498_, v_a_1499_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1510_, uint8_t v___y_1511_, lean_object* v_x_1512_){
_start:
{
if (lean_obj_tag(v_x_1512_) == 1)
{
lean_object* v_pre_1513_; 
v_pre_1513_ = lean_ctor_get(v_x_1512_, 0);
switch(lean_obj_tag(v_pre_1513_))
{
case 1:
{
lean_object* v_pre_1514_; 
v_pre_1514_ = lean_ctor_get(v_pre_1513_, 0);
switch(lean_obj_tag(v_pre_1514_))
{
case 0:
{
lean_object* v_str_1515_; lean_object* v_str_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_str_1515_ = lean_ctor_get(v_x_1512_, 1);
v_str_1516_ = lean_ctor_get(v_pre_1513_, 1);
v___x_1517_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1518_ = lean_string_dec_eq(v_str_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1520_ = lean_string_dec_eq(v_str_1516_, v___x_1519_);
if (v___x_1520_ == 0)
{
return v___x_1520_;
}
else
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1522_ = lean_string_dec_eq(v_str_1515_, v___x_1521_);
if (v___x_1522_ == 0)
{
return v___x_1522_;
}
else
{
return v_suppressElabErrors_1510_;
}
}
}
else
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1524_ = lean_string_dec_eq(v_str_1515_, v___x_1523_);
if (v___x_1524_ == 0)
{
return v___x_1524_;
}
else
{
return v_suppressElabErrors_1510_;
}
}
}
case 1:
{
lean_object* v_pre_1525_; 
v_pre_1525_ = lean_ctor_get(v_pre_1514_, 0);
if (lean_obj_tag(v_pre_1525_) == 0)
{
lean_object* v_str_1526_; lean_object* v_str_1527_; lean_object* v_str_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_str_1526_ = lean_ctor_get(v_x_1512_, 1);
v_str_1527_ = lean_ctor_get(v_pre_1513_, 1);
v_str_1528_ = lean_ctor_get(v_pre_1514_, 1);
v___x_1529_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1530_ = lean_string_dec_eq(v_str_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
return v___x_1530_;
}
else
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1532_ = lean_string_dec_eq(v_str_1527_, v___x_1531_);
if (v___x_1532_ == 0)
{
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1534_ = lean_string_dec_eq(v_str_1526_, v___x_1533_);
if (v___x_1534_ == 0)
{
return v___x_1534_;
}
else
{
return v_suppressElabErrors_1510_;
}
}
}
}
else
{
return v___y_1511_;
}
}
default: 
{
return v___y_1511_;
}
}
}
case 0:
{
lean_object* v_str_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_str_1535_ = lean_ctor_get(v_x_1512_, 1);
v___x_1536_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1537_ = lean_string_dec_eq(v_str_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
return v___x_1537_;
}
else
{
return v_suppressElabErrors_1510_;
}
}
default: 
{
return v___y_1511_;
}
}
}
else
{
return v___y_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1538_, lean_object* v___y_1539_, lean_object* v_x_1540_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1541_; uint8_t v___y_10617__boxed_1542_; uint8_t v_res_1543_; lean_object* v_r_1544_; 
v_suppressElabErrors_boxed_1541_ = lean_unbox(v_suppressElabErrors_1538_);
v___y_10617__boxed_1542_ = lean_unbox(v___y_1539_);
v_res_1543_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1541_, v___y_10617__boxed_1542_, v_x_1540_);
lean_dec(v_x_1540_);
v_r_1544_ = lean_box(v_res_1543_);
return v_r_1544_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1545_, lean_object* v_opt_1546_){
_start:
{
lean_object* v_name_1547_; lean_object* v_defValue_1548_; lean_object* v_map_1549_; lean_object* v___x_1550_; 
v_name_1547_ = lean_ctor_get(v_opt_1546_, 0);
v_defValue_1548_ = lean_ctor_get(v_opt_1546_, 1);
v_map_1549_ = lean_ctor_get(v_opts_1545_, 0);
v___x_1550_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1549_, v_name_1547_);
if (lean_obj_tag(v___x_1550_) == 0)
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_unbox(v_defValue_1548_);
return v___x_1551_;
}
else
{
lean_object* v_val_1552_; 
v_val_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1550_, 1);
if (lean_obj_tag(v_val_1552_) == 1)
{
uint8_t v_v_1553_; 
v_v_1553_ = lean_ctor_get_uint8(v_val_1552_, 0);
lean_dec_ref_known(v_val_1552_, 0);
return v_v_1553_;
}
else
{
uint8_t v___x_1554_; 
lean_dec(v_val_1552_);
v___x_1554_ = lean_unbox(v_defValue_1548_);
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1555_, lean_object* v_opt_1556_){
_start:
{
uint8_t v_res_1557_; lean_object* v_r_1558_; 
v_res_1557_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1555_, v_opt_1556_);
lean_dec_ref(v_opt_1556_);
lean_dec_ref(v_opts_1555_);
v_r_1558_ = lean_box(v_res_1557_);
return v_r_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1560_, lean_object* v_msgData_1561_, uint8_t v_severity_1562_, uint8_t v_isSilent_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_a_1569_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; uint8_t v___y_1576_; uint8_t v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1609_; uint8_t v___y_1610_; lean_object* v___y_1611_; uint8_t v___y_1612_; uint8_t v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1633_; lean_object* v___y_1634_; uint8_t v___y_1635_; uint8_t v___y_1636_; uint8_t v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1644_; lean_object* v___y_1645_; uint8_t v___y_1646_; uint8_t v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; uint8_t v___y_1650_; uint8_t v___x_1655_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; uint8_t v___y_1661_; uint8_t v___y_1662_; uint8_t v___y_1663_; uint8_t v___y_1665_; uint8_t v___x_1682_; 
v___x_1655_ = 2;
v___x_1682_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1562_, v___x_1655_);
if (v___x_1682_ == 0)
{
v___y_1665_ = v___x_1682_;
goto v___jp_1664_;
}
else
{
uint8_t v___x_1683_; 
lean_inc_ref(v_msgData_1561_);
v___x_1683_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1561_);
v___y_1665_ = v___x_1683_;
goto v___jp_1664_;
}
v___jp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_a_1569_);
lean_ctor_set(v___x_1570_, 1, v___y_1564_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
v___jp_1572_:
{
lean_object* v___x_1582_; lean_object* v_toCold_1583_; lean_object* v_currNamespace_1584_; lean_object* v_openDecls_1585_; lean_object* v_env_1586_; lean_object* v_nextMacroScope_1587_; lean_object* v_ngen_1588_; lean_object* v_auxDeclNGen_1589_; lean_object* v_traceState_1590_; lean_object* v_cache_1591_; lean_object* v_messages_1592_; lean_object* v_infoState_1593_; lean_object* v_snapshotTasks_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1607_; 
v___x_1582_ = lean_st_ref_take(v___y_1581_);
v_toCold_1583_ = lean_ctor_get(v___y_1580_, 0);
v_currNamespace_1584_ = lean_ctor_get(v_toCold_1583_, 4);
v_openDecls_1585_ = lean_ctor_get(v_toCold_1583_, 5);
v_env_1586_ = lean_ctor_get(v___x_1582_, 0);
v_nextMacroScope_1587_ = lean_ctor_get(v___x_1582_, 1);
v_ngen_1588_ = lean_ctor_get(v___x_1582_, 2);
v_auxDeclNGen_1589_ = lean_ctor_get(v___x_1582_, 3);
v_traceState_1590_ = lean_ctor_get(v___x_1582_, 4);
v_cache_1591_ = lean_ctor_get(v___x_1582_, 5);
v_messages_1592_ = lean_ctor_get(v___x_1582_, 6);
v_infoState_1593_ = lean_ctor_get(v___x_1582_, 7);
v_snapshotTasks_1594_ = lean_ctor_get(v___x_1582_, 8);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1596_ = v___x_1582_;
v_isShared_1597_ = v_isSharedCheck_1607_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_snapshotTasks_1594_);
lean_inc(v_infoState_1593_);
lean_inc(v_messages_1592_);
lean_inc(v_cache_1591_);
lean_inc(v_traceState_1590_);
lean_inc(v_auxDeclNGen_1589_);
lean_inc(v_ngen_1588_);
lean_inc(v_nextMacroScope_1587_);
lean_inc(v_env_1586_);
lean_dec(v___x_1582_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1607_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_inc(v_openDecls_1585_);
lean_inc(v_currNamespace_1584_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_currNamespace_1584_);
lean_ctor_set(v___x_1598_, 1, v_openDecls_1585_);
v___x_1599_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___y_1573_);
lean_inc_ref(v___y_1578_);
lean_inc_ref(v___y_1579_);
v___x_1600_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1600_, 0, v___y_1579_);
lean_ctor_set(v___x_1600_, 1, v___y_1574_);
lean_ctor_set(v___x_1600_, 2, v___y_1575_);
lean_ctor_set(v___x_1600_, 3, v___y_1578_);
lean_ctor_set(v___x_1600_, 4, v___x_1599_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*5, v___y_1577_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*5 + 1, v___y_1576_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*5 + 2, v_isSilent_1563_);
v___x_1601_ = l_Lean_MessageLog_add(v___x_1600_, v_messages_1592_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 6, v___x_1601_);
v___x_1603_ = v___x_1596_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_env_1586_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_nextMacroScope_1587_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_ngen_1588_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_auxDeclNGen_1589_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_traceState_1590_);
lean_ctor_set(v_reuseFailAlloc_1606_, 5, v_cache_1591_);
lean_ctor_set(v_reuseFailAlloc_1606_, 6, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1606_, 7, v_infoState_1593_);
lean_ctor_set(v_reuseFailAlloc_1606_, 8, v_snapshotTasks_1594_);
v___x_1603_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_st_ref_put(v___y_1581_, v___x_1603_);
v___x_1605_ = lean_box(0);
v_a_1569_ = v___x_1605_;
goto v___jp_1568_;
}
}
}
v___jp_1608_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1631_; 
v___x_1617_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1561_);
v___x_1618_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1617_, v___y_1565_, v___y_1566_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1631_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1631_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
lean_inc_ref_n(v___y_1614_, 2);
v___x_1623_ = l_Lean_FileMap_toPosition(v___y_1614_, v___y_1611_);
lean_dec(v___y_1611_);
v___x_1624_ = l_Lean_FileMap_toPosition(v___y_1614_, v___y_1616_);
lean_dec(v___y_1616_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 1);
lean_ctor_set(v___x_1621_, 0, v___x_1624_);
v___x_1626_ = v___x_1621_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; 
v___x_1627_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1610_ == 0)
{
lean_dec_ref(v___y_1609_);
v___y_1573_ = v_a_1619_;
v___y_1574_ = v___x_1623_;
v___y_1575_ = v___x_1626_;
v___y_1576_ = v___y_1613_;
v___y_1577_ = v___y_1612_;
v___y_1578_ = v___x_1627_;
v___y_1579_ = v___y_1615_;
v___y_1580_ = v___y_1565_;
v___y_1581_ = v___y_1566_;
goto v___jp_1572_;
}
else
{
uint8_t v___x_1628_; 
lean_inc(v_a_1619_);
v___x_1628_ = l_Lean_MessageData_hasTag(v___y_1609_, v_a_1619_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
lean_dec_ref(v___x_1626_);
lean_dec_ref(v___x_1623_);
lean_dec(v_a_1619_);
v___x_1629_ = lean_box(0);
v_a_1569_ = v___x_1629_;
goto v___jp_1568_;
}
else
{
v___y_1573_ = v_a_1619_;
v___y_1574_ = v___x_1623_;
v___y_1575_ = v___x_1626_;
v___y_1576_ = v___y_1613_;
v___y_1577_ = v___y_1612_;
v___y_1578_ = v___x_1627_;
v___y_1579_ = v___y_1615_;
v___y_1580_ = v___y_1565_;
v___y_1581_ = v___y_1566_;
goto v___jp_1572_;
}
}
}
}
}
v___jp_1632_:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Syntax_getTailPos_x3f(v___y_1634_, v___y_1637_);
lean_dec(v___y_1634_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_inc(v___y_1640_);
v___y_1609_ = v___y_1633_;
v___y_1610_ = v___y_1635_;
v___y_1611_ = v___y_1640_;
v___y_1612_ = v___y_1637_;
v___y_1613_ = v___y_1636_;
v___y_1614_ = v___y_1638_;
v___y_1615_ = v___y_1639_;
v___y_1616_ = v___y_1640_;
goto v___jp_1608_;
}
else
{
lean_object* v_val_1642_; 
v_val_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_val_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v___y_1609_ = v___y_1633_;
v___y_1610_ = v___y_1635_;
v___y_1611_ = v___y_1640_;
v___y_1612_ = v___y_1637_;
v___y_1613_ = v___y_1636_;
v___y_1614_ = v___y_1638_;
v___y_1615_ = v___y_1639_;
v___y_1616_ = v_val_1642_;
goto v___jp_1608_;
}
}
v___jp_1643_:
{
lean_object* v_ref_1651_; lean_object* v___x_1652_; 
v_ref_1651_ = l_Lean_replaceRef(v_ref_1560_, v___y_1645_);
v___x_1652_ = l_Lean_Syntax_getPos_x3f(v_ref_1651_, v___y_1647_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_unsigned_to_nat(0u);
v___y_1633_ = v___y_1644_;
v___y_1634_ = v_ref_1651_;
v___y_1635_ = v___y_1646_;
v___y_1636_ = v___y_1650_;
v___y_1637_ = v___y_1647_;
v___y_1638_ = v___y_1648_;
v___y_1639_ = v___y_1649_;
v___y_1640_ = v___x_1653_;
goto v___jp_1632_;
}
else
{
lean_object* v_val_1654_; 
v_val_1654_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v___x_1652_, 1);
v___y_1633_ = v___y_1644_;
v___y_1634_ = v_ref_1651_;
v___y_1635_ = v___y_1646_;
v___y_1636_ = v___y_1650_;
v___y_1637_ = v___y_1647_;
v___y_1638_ = v___y_1648_;
v___y_1639_ = v___y_1649_;
v___y_1640_ = v_val_1654_;
goto v___jp_1632_;
}
}
v___jp_1656_:
{
if (v___y_1663_ == 0)
{
v___y_1644_ = v___y_1657_;
v___y_1645_ = v___y_1660_;
v___y_1646_ = v___y_1661_;
v___y_1647_ = v___y_1662_;
v___y_1648_ = v___y_1658_;
v___y_1649_ = v___y_1659_;
v___y_1650_ = v_severity_1562_;
goto v___jp_1643_;
}
else
{
v___y_1644_ = v___y_1657_;
v___y_1645_ = v___y_1660_;
v___y_1646_ = v___y_1661_;
v___y_1647_ = v___y_1662_;
v___y_1648_ = v___y_1658_;
v___y_1649_ = v___y_1659_;
v___y_1650_ = v___x_1655_;
goto v___jp_1643_;
}
}
v___jp_1664_:
{
if (v___y_1665_ == 0)
{
lean_object* v_toCold_1666_; lean_object* v_ref_1667_; uint8_t v_suppressElabErrors_1668_; lean_object* v_fileName_1669_; lean_object* v_fileMap_1670_; lean_object* v_options_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___f_1674_; uint8_t v___x_1675_; uint8_t v___x_1676_; 
v_toCold_1666_ = lean_ctor_get(v___y_1565_, 0);
v_ref_1667_ = lean_ctor_get(v___y_1565_, 2);
v_suppressElabErrors_1668_ = lean_ctor_get_uint8(v___y_1565_, sizeof(void*)*3 + 1);
v_fileName_1669_ = lean_ctor_get(v_toCold_1666_, 0);
v_fileMap_1670_ = lean_ctor_get(v_toCold_1666_, 1);
v_options_1671_ = lean_ctor_get(v_toCold_1666_, 2);
v___x_1672_ = lean_box(v_suppressElabErrors_1668_);
v___x_1673_ = lean_box(v___y_1665_);
v___f_1674_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1674_, 0, v___x_1672_);
lean_closure_set(v___f_1674_, 1, v___x_1673_);
v___x_1675_ = 1;
v___x_1676_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1562_, v___x_1675_);
if (v___x_1676_ == 0)
{
v___y_1657_ = v___f_1674_;
v___y_1658_ = v_fileMap_1670_;
v___y_1659_ = v_fileName_1669_;
v___y_1660_ = v_ref_1667_;
v___y_1661_ = v_suppressElabErrors_1668_;
v___y_1662_ = v___y_1665_;
v___y_1663_ = v___x_1676_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = l_Lean_warningAsError;
v___x_1678_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_options_1671_, v___x_1677_);
v___y_1657_ = v___f_1674_;
v___y_1658_ = v_fileMap_1670_;
v___y_1659_ = v_fileName_1669_;
v___y_1660_ = v_ref_1667_;
v___y_1661_ = v_suppressElabErrors_1668_;
v___y_1662_ = v___y_1665_;
v___y_1663_ = v___x_1678_;
goto v___jp_1656_;
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref(v_msgData_1561_);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___y_1564_);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1684_, lean_object* v_msgData_1685_, lean_object* v_severity_1686_, lean_object* v_isSilent_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
uint8_t v_severity_boxed_1692_; uint8_t v_isSilent_boxed_1693_; lean_object* v_res_1694_; 
v_severity_boxed_1692_ = lean_unbox(v_severity_1686_);
v_isSilent_boxed_1693_ = lean_unbox(v_isSilent_1687_);
v_res_1694_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1684_, v_msgData_1685_, v_severity_boxed_1692_, v_isSilent_boxed_1693_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_ref_1684_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1695_, lean_object* v_msgData_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = 2;
v___x_1702_ = 0;
v___x_1703_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1695_, v_msgData_1696_, v___x_1701_, v___x_1702_, v___y_1697_, v___y_1698_, v___y_1699_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1704_, lean_object* v_msgData_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1704_, v_msgData_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v_ref_1704_);
return v_res_1710_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1714_ = l_Lean_MessageData_ofFormat(v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1715_, lean_object* v_as_1716_, size_t v_sz_1717_, size_t v_i_1718_, uint8_t v_b_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_snd_1725_; lean_object* v_snd_1726_; lean_object* v___y_1732_; uint8_t v___y_1733_; lean_object* v_a_1750_; uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_lt(v_i_1718_, v_sz_1717_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_box(v_b_1719_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___y_1720_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1758_; uint8_t v_recovering_1759_; 
v_a_1757_ = lean_array_uget_borrowed(v_as_1716_, v_i_1718_);
v___x_1758_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1757_);
v_recovering_1759_ = l_Lean_Syntax_isOfKind(v_a_1757_, v___x_1758_);
if (v_recovering_1759_ == 0)
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_a_1757_);
v___x_1761_ = l_Lean_Syntax_isOfKind(v_a_1757_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1757_);
v___x_1763_ = l_Lean_Syntax_isOfKind(v_a_1757_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1720_);
v___x_1765_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1757_, v___x_1764_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v_snd_1767_; lean_object* v___x_1768_; 
lean_dec_ref(v___y_1720_);
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v_snd_1767_ = lean_ctor_get(v_a_1766_, 1);
lean_inc(v_snd_1767_);
lean_dec(v_a_1766_);
v___x_1768_ = lean_box(v_b_1719_);
v_snd_1725_ = v___x_1768_;
v_snd_1726_ = v_snd_1767_;
goto v___jp_1724_;
}
else
{
lean_object* v_a_1769_; 
v_a_1769_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1765_, 1);
v_a_1750_ = v_a_1769_;
goto v___jp_1749_;
}
}
else
{
lean_object* v___x_1770_; 
lean_inc_ref(v___y_1720_);
lean_inc(v_a_1757_);
v___x_1770_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1757_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_snd_1772_; lean_object* v___x_1773_; 
lean_dec_ref(v___y_1720_);
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v_snd_1772_ = lean_ctor_get(v_a_1771_, 1);
lean_inc(v_snd_1772_);
lean_dec(v_a_1771_);
v___x_1773_ = lean_box(v_recovering_1759_);
v_snd_1725_ = v___x_1773_;
v_snd_1726_ = v_snd_1772_;
goto v___jp_1724_;
}
else
{
lean_object* v_a_1774_; 
v_a_1774_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1770_, 1);
v_a_1750_ = v_a_1774_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v___x_1775_; 
lean_inc_ref(v___y_1720_);
lean_inc(v_a_1757_);
v___x_1775_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1757_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v_snd_1777_; lean_object* v___x_1778_; 
lean_dec_ref(v___y_1720_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v_snd_1777_ = lean_ctor_get(v_a_1776_, 1);
lean_inc(v_snd_1777_);
lean_dec(v_a_1776_);
v___x_1778_ = lean_box(v_recovering_1759_);
v_snd_1725_ = v___x_1778_;
v_snd_1726_ = v_snd_1777_;
goto v___jp_1724_;
}
else
{
lean_object* v_a_1779_; 
v_a_1779_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1775_, 1);
v_a_1750_ = v_a_1779_;
goto v___jp_1749_;
}
}
}
else
{
if (v_b_1719_ == 0)
{
lean_object* v___x_1780_; 
lean_inc_ref(v___y_1720_);
lean_inc(v_a_1757_);
v___x_1780_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1757_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v_snd_1782_; lean_object* v___x_1783_; 
lean_dec_ref(v___y_1720_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v_snd_1782_ = lean_ctor_get(v_a_1781_, 1);
lean_inc(v_snd_1782_);
lean_dec(v_a_1781_);
v___x_1783_ = lean_box(v_b_1719_);
v_snd_1725_ = v___x_1783_;
v_snd_1726_ = v_snd_1782_;
goto v___jp_1724_;
}
else
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1780_, 1);
v_a_1750_ = v_a_1784_;
goto v___jp_1749_;
}
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_box(v_b_1719_);
v_snd_1725_ = v___x_1785_;
v_snd_1726_ = v___y_1720_;
goto v___jp_1724_;
}
}
}
v___jp_1724_:
{
size_t v___x_1727_; size_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = ((size_t)1ULL);
v___x_1728_ = lean_usize_add(v_i_1718_, v___x_1727_);
v___x_1729_ = lean_unbox(v_snd_1725_);
lean_dec(v_snd_1725_);
v_i_1718_ = v___x_1728_;
v_b_1719_ = v___x_1729_;
v___y_1720_ = v_snd_1726_;
goto _start;
}
v___jp_1731_:
{
if (v___y_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = l_Lean_Exception_getRef(v___y_1732_);
v___x_1735_ = l_Lean_Exception_toMessageData(v___y_1732_);
v___x_1736_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1734_, v___x_1735_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___x_1734_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v_snd_1738_; lean_object* v___x_1739_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v_snd_1738_ = lean_ctor_get(v_a_1737_, 1);
lean_inc(v_snd_1738_);
lean_dec(v_a_1737_);
v___x_1739_ = lean_box(v_recovering_1715_);
v_snd_1725_ = v___x_1739_;
v_snd_1726_ = v_snd_1738_;
goto v___jp_1724_;
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
v_a_1740_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1736_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1736_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v___x_1748_; 
lean_dec_ref(v___y_1720_);
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___y_1732_);
return v___x_1748_;
}
}
v___jp_1749_:
{
uint8_t v___x_1751_; 
v___x_1751_ = l_Lean_Exception_isInterrupt(v_a_1750_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; 
lean_inc_ref(v_a_1750_);
v___x_1752_ = l_Lean_Exception_isRuntime(v_a_1750_);
v___y_1732_ = v_a_1750_;
v___y_1733_ = v___x_1752_;
goto v___jp_1731_;
}
else
{
v___y_1732_ = v_a_1750_;
v___y_1733_ = v___x_1751_;
goto v___jp_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1786_, lean_object* v_as_1787_, lean_object* v_sz_1788_, lean_object* v_i_1789_, lean_object* v_b_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v_recovering_boxed_1795_; size_t v_sz_boxed_1796_; size_t v_i_boxed_1797_; uint8_t v_b_boxed_1798_; lean_object* v_res_1799_; 
v_recovering_boxed_1795_ = lean_unbox(v_recovering_1786_);
v_sz_boxed_1796_ = lean_unbox_usize(v_sz_1788_);
lean_dec(v_sz_1788_);
v_i_boxed_1797_ = lean_unbox_usize(v_i_1789_);
lean_dec(v_i_1789_);
v_b_boxed_1798_ = lean_unbox(v_b_1790_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1795_, v_as_1787_, v_sz_boxed_1796_, v_i_boxed_1797_, v_b_boxed_1798_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_as_1787_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_ref_1804_; lean_object* v___x_1805_; lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1814_; 
v_ref_1804_ = lean_ctor_get(v___y_1801_, 2);
v___x_1805_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1800_, v___y_1801_, v___y_1802_);
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
lean_inc(v_ref_1804_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_ref_1804_);
lean_ctor_set(v___x_1810_, 1, v_a_1806_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 1);
lean_ctor_set(v___x_1808_, 0, v___x_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1820_, lean_object* v_msg_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_toCold_1825_; lean_object* v_currRecDepth_1826_; lean_object* v_ref_1827_; uint8_t v_diag_1828_; uint8_t v_suppressElabErrors_1829_; lean_object* v_ref_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_toCold_1825_ = lean_ctor_get(v___y_1822_, 0);
v_currRecDepth_1826_ = lean_ctor_get(v___y_1822_, 1);
v_ref_1827_ = lean_ctor_get(v___y_1822_, 2);
v_diag_1828_ = lean_ctor_get_uint8(v___y_1822_, sizeof(void*)*3);
v_suppressElabErrors_1829_ = lean_ctor_get_uint8(v___y_1822_, sizeof(void*)*3 + 1);
v_ref_1830_ = l_Lean_replaceRef(v_ref_1820_, v_ref_1827_);
lean_inc(v_currRecDepth_1826_);
lean_inc_ref(v_toCold_1825_);
v___x_1831_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1831_, 0, v_toCold_1825_);
lean_ctor_set(v___x_1831_, 1, v_currRecDepth_1826_);
lean_ctor_set(v___x_1831_, 2, v_ref_1830_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3, v_diag_1828_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 1, v_suppressElabErrors_1829_);
v___x_1832_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1821_, v___x_1831_, v___y_1823_);
lean_dec_ref_known(v___x_1831_, 3);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1833_, lean_object* v_msg_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1833_, v_msg_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v_ref_1833_);
return v_res_1838_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1855_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1851_);
v___x_1856_ = l_Lean_Syntax_isOfKind(v_x_1851_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1858_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1851_, v___x_1857_, v_a_1852_, v_a_1853_);
lean_dec(v_x_1851_);
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v_recovering_1862_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = l_Lean_Syntax_getArg(v_x_1851_, v___x_1859_);
v___x_1861_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1862_ = l_Lean_Syntax_isOfKind(v___x_1860_, v___x_1861_);
if (v_recovering_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1864_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1851_, v___x_1863_, v_a_1852_, v_a_1853_);
lean_dec(v_x_1851_);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v_xs_1867_; uint8_t v_recovering_1868_; lean_object* v___x_1869_; size_t v_sz_1870_; size_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1865_ = lean_unsigned_to_nat(1u);
v___x_1866_ = l_Lean_Syntax_getArg(v_x_1851_, v___x_1865_);
lean_dec(v_x_1851_);
v_xs_1867_ = l_Lean_Syntax_getArgs(v___x_1866_);
lean_dec(v___x_1866_);
v_recovering_1868_ = 0;
v___x_1869_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1867_);
lean_dec_ref(v_xs_1867_);
v_sz_1870_ = lean_array_size(v___x_1869_);
v___x_1871_ = ((size_t)0ULL);
v___x_1872_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1862_, v___x_1869_, v_sz_1870_, v___x_1871_, v_recovering_1868_, v___x_1872_, v_a_1852_, v_a_1853_);
lean_dec_ref(v___x_1869_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1884_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_snd_1878_; lean_object* v_items_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v_snd_1878_ = lean_ctor_get(v_a_1874_, 1);
lean_inc(v_snd_1878_);
lean_dec(v_a_1874_);
v_items_1879_ = lean_ctor_get(v_snd_1878_, 5);
lean_inc_ref(v_items_1879_);
lean_dec(v_snd_1878_);
v___x_1880_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1879_);
lean_dec_ref(v_items_1879_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1880_);
v___x_1882_ = v___x_1876_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
v_a_1885_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1873_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1873_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lake_Toml_elabToml(v_x_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1898_, lean_object* v_ref_1899_, lean_object* v_msg_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1899_, v_msg_1900_, v___y_1901_, v___y_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1905_, lean_object* v_ref_1906_, lean_object* v_msg_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1905_, v_ref_1906_, v_msg_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v_ref_1906_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1912_, lean_object* v_msg_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1913_, v___y_1914_, v___y_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_msg_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1918_, v_msg_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1923_;
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
