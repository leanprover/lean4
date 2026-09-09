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
v_options_150_ = lean_ctor_get(v___y_145_, 1);
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
v_ref_165_ = lean_ctor_get(v___y_162_, 4);
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
lean_object* v_toCold_187_; lean_object* v_options_188_; lean_object* v_currRecDepth_189_; lean_object* v_maxRecDepth_190_; lean_object* v_ref_191_; lean_object* v_currNamespace_192_; lean_object* v_openDecls_193_; lean_object* v_initHeartbeats_194_; lean_object* v_maxHeartbeats_195_; lean_object* v_currMacroScope_196_; uint8_t v_diag_197_; uint8_t v_suppressElabErrors_198_; lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_toCold_187_ = lean_ctor_get(v___y_184_, 0);
v_options_188_ = lean_ctor_get(v___y_184_, 1);
v_currRecDepth_189_ = lean_ctor_get(v___y_184_, 2);
v_maxRecDepth_190_ = lean_ctor_get(v___y_184_, 3);
v_ref_191_ = lean_ctor_get(v___y_184_, 4);
v_currNamespace_192_ = lean_ctor_get(v___y_184_, 5);
v_openDecls_193_ = lean_ctor_get(v___y_184_, 6);
v_initHeartbeats_194_ = lean_ctor_get(v___y_184_, 7);
v_maxHeartbeats_195_ = lean_ctor_get(v___y_184_, 8);
v_currMacroScope_196_ = lean_ctor_get(v___y_184_, 9);
v_diag_197_ = lean_ctor_get_uint8(v___y_184_, sizeof(void*)*10);
v_suppressElabErrors_198_ = lean_ctor_get_uint8(v___y_184_, sizeof(void*)*10 + 1);
v_ref_199_ = l_Lean_replaceRef(v_ref_181_, v_ref_191_);
lean_inc(v_currMacroScope_196_);
lean_inc(v_maxHeartbeats_195_);
lean_inc(v_initHeartbeats_194_);
lean_inc(v_openDecls_193_);
lean_inc(v_currNamespace_192_);
lean_inc(v_maxRecDepth_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_options_188_);
lean_inc_ref(v_toCold_187_);
v___x_200_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_200_, 0, v_toCold_187_);
lean_ctor_set(v___x_200_, 1, v_options_188_);
lean_ctor_set(v___x_200_, 2, v_currRecDepth_189_);
lean_ctor_set(v___x_200_, 3, v_maxRecDepth_190_);
lean_ctor_set(v___x_200_, 4, v_ref_199_);
lean_ctor_set(v___x_200_, 5, v_currNamespace_192_);
lean_ctor_set(v___x_200_, 6, v_openDecls_193_);
lean_ctor_set(v___x_200_, 7, v_initHeartbeats_194_);
lean_ctor_set(v___x_200_, 8, v_maxHeartbeats_195_);
lean_ctor_set(v___x_200_, 9, v_currMacroScope_196_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*10, v_diag_197_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*10 + 1, v_suppressElabErrors_198_);
v___x_201_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_182_, v___x_200_, v___y_185_);
lean_dec_ref_known(v___x_200_, 10);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object* v_ref_202_, lean_object* v_msg_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_202_, v_msg_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v_ref_202_);
return v_res_208_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object* v_as_218_, size_t v_i_219_, size_t v_stop_220_, lean_object* v_b_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_fst_227_; lean_object* v_snd_228_; uint8_t v___x_232_; 
v___x_232_ = lean_usize_dec_eq(v_i_219_, v_stop_220_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_array_uget_borrowed(v_as_218_, v_i_219_);
lean_inc(v___x_233_);
v___x_234_ = l_Lake_Toml_elabSimpleKey(v___x_233_, v___y_223_, v___y_224_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v_keyTys_236_; lean_object* v_arrKeyTys_237_; lean_object* v_arrParents_238_; lean_object* v_currArrKey_239_; lean_object* v_currKey_240_; lean_object* v_items_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v_keyTys_236_ = lean_ctor_get(v___y_222_, 0);
v_arrKeyTys_237_ = lean_ctor_get(v___y_222_, 1);
v_arrParents_238_ = lean_ctor_get(v___y_222_, 2);
v_currArrKey_239_ = lean_ctor_get(v___y_222_, 3);
v_currKey_240_ = lean_ctor_get(v___y_222_, 4);
v_items_241_ = lean_ctor_get(v___y_222_, 5);
v___x_242_ = l_Lean_Name_str___override(v_b_221_, v_a_235_);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_236_, v___x_242_);
if (lean_obj_tag(v___x_243_) == 1)
{
lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_274_; 
v_val_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_274_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_274_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_274_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___x_248_; 
v___x_248_ = lean_unbox(v_val_244_);
if (v___x_248_ == 3)
{
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
v_fst_227_ = v___x_242_;
v_snd_228_ = v___y_222_;
goto v___jp_226_;
}
else
{
lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_249_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_250_ = lean_unbox(v_val_244_);
lean_dec(v_val_244_);
v___x_251_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_250_);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 3);
lean_ctor_set(v___x_246_, 0, v___x_251_);
v___x_253_ = v___x_246_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_273_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_254_ = l_Lean_MessageData_ofFormat(v___x_253_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_249_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
lean_inc(v___x_242_);
v___x_258_ = l_Lean_MessageData_ofName(v___x_242_);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_233_, v___x_261_, v___y_222_, v___y_223_, v___y_224_);
lean_dec_ref(v___y_222_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v_snd_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
v_snd_264_ = lean_ctor_get(v_a_263_, 1);
lean_inc(v_snd_264_);
lean_dec(v_a_263_);
v_fst_227_ = v___x_242_;
v_snd_228_ = v_snd_264_;
goto v___jp_226_;
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v___x_242_);
v_a_265_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_262_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_262_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_284_; 
lean_inc_ref(v_items_241_);
lean_inc(v_currKey_240_);
lean_inc(v_currArrKey_239_);
lean_inc(v_arrParents_238_);
lean_inc(v_arrKeyTys_237_);
lean_inc(v_keyTys_236_);
lean_dec(v___x_243_);
v_isSharedCheck_284_ = !lean_is_exclusive(v___y_222_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; 
v_unused_285_ = lean_ctor_get(v___y_222_, 5);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v___y_222_, 4);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v___y_222_, 3);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v___y_222_, 2);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v___y_222_, 1);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v___y_222_, 0);
lean_dec(v_unused_290_);
v___x_276_ = v___y_222_;
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
else
{
lean_dec(v___y_222_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_278_ = 3;
v___x_279_ = lean_box(v___x_278_);
lean_inc(v___x_242_);
v___x_280_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_242_, v___x_279_, v_keyTys_236_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_280_);
v___x_282_ = v___x_276_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_arrKeyTys_237_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_arrParents_238_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_currArrKey_239_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_currKey_240_);
lean_ctor_set(v_reuseFailAlloc_283_, 5, v_items_241_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
v_fst_227_ = v___x_242_;
v_snd_228_ = v___x_282_;
goto v___jp_226_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v___y_222_);
lean_dec(v_b_221_);
v_a_291_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_234_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_234_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_b_221_);
lean_ctor_set(v___x_299_, 1, v___y_222_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
v___jp_226_:
{
size_t v___x_229_; size_t v___x_230_; 
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_i_219_, v___x_229_);
v_i_219_ = v___x_230_;
v_b_221_ = v_fst_227_;
v___y_222_ = v_snd_228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object* v_as_301_, lean_object* v_i_302_, lean_object* v_stop_303_, lean_object* v_b_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
size_t v_i_boxed_309_; size_t v_stop_boxed_310_; lean_object* v_res_311_; 
v_i_boxed_309_ = lean_unbox_usize(v_i_302_);
lean_dec(v_i_302_);
v_stop_boxed_310_ = lean_unbox_usize(v_stop_303_);
lean_dec(v_stop_303_);
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_301_, v_i_boxed_309_, v_stop_boxed_310_, v_b_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec_ref(v_as_301_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object* v_ks_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_currKey_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_currKey_317_ = lean_ctor_get(v_a_313_, 4);
lean_inc(v_currKey_317_);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_array_get_size(v_ks_312_);
v___x_320_ = lean_nat_dec_lt(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_currKey_317_);
lean_ctor_set(v___x_321_, 1, v_a_313_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_le(v___x_319_, v___x_319_);
if (v___x_323_ == 0)
{
if (v___x_320_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_currKey_317_);
lean_ctor_set(v___x_324_, 1, v_a_313_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
else
{
size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_319_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_312_, v___x_326_, v___x_327_, v_currKey_317_, v_a_313_, v_a_314_, v_a_315_);
return v___x_328_;
}
}
else
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_319_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_312_, v___x_329_, v___x_330_, v_currKey_317_, v_a_313_, v_a_314_, v_a_315_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object* v_ks_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec_ref(v_ks_332_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_338_, lean_object* v_ref_339_, lean_object* v_msg_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_339_, v_msg_340_, v___y_341_, v___y_342_, v___y_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_346_, lean_object* v_ref_347_, lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_346_, v_ref_347_, v_msg_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v_ref_347_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_354_, lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_355_, v___y_357_, v___y_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_361_, lean_object* v_msg_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_361_, v_msg_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_368_, lean_object* v_as_369_, size_t v_i_370_, size_t v_stop_371_, lean_object* v_b_372_){
_start:
{
lean_object* v___y_374_; uint8_t v___x_378_; 
v___x_378_ = lean_usize_dec_eq(v_i_370_, v_stop_371_);
if (v___x_378_ == 0)
{
lean_object* v_fst_379_; uint8_t v___x_380_; 
v_fst_379_ = lean_ctor_get(v_b_372_, 0);
v___x_380_ = lean_unbox(v_fst_379_);
if (v___x_380_ == 0)
{
lean_object* v_snd_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_389_; 
v_snd_381_ = lean_ctor_get(v_b_372_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v_b_372_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v_b_372_, 0);
lean_dec(v_unused_390_);
v___x_383_ = v_b_372_;
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snd_381_);
lean_dec(v_b_372_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = lean_box(v___x_368_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_snd_381_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
v___y_374_ = v___x_387_;
goto v___jp_373_;
}
}
}
else
{
lean_object* v_snd_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_401_; 
v_snd_391_ = lean_ctor_get(v_b_372_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_b_372_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v_b_372_, 0);
lean_dec(v_unused_402_);
v___x_393_ = v_b_372_;
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_snd_391_);
lean_dec(v_b_372_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_395_ = lean_array_uget_borrowed(v_as_369_, v_i_370_);
lean_inc(v___x_395_);
v___x_396_ = lean_array_push(v_snd_391_, v___x_395_);
v___x_397_ = lean_box(v___x_378_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v___x_396_);
lean_ctor_set(v___x_393_, 0, v___x_397_);
v___x_399_ = v___x_393_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_396_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
v___y_374_ = v___x_399_;
goto v___jp_373_;
}
}
}
}
else
{
return v_b_372_;
}
v___jp_373_:
{
size_t v___x_375_; size_t v___x_376_; 
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_add(v_i_370_, v___x_375_);
v_i_370_ = v___x_376_;
v_b_372_ = v___y_374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_403_, lean_object* v_as_404_, lean_object* v_i_405_, lean_object* v_stop_406_, lean_object* v_b_407_){
_start:
{
uint8_t v___x_2932__boxed_408_; size_t v_i_boxed_409_; size_t v_stop_boxed_410_; lean_object* v_res_411_; 
v___x_2932__boxed_408_ = lean_unbox(v___x_403_);
v_i_boxed_409_ = lean_unbox_usize(v_i_405_);
lean_dec(v_i_405_);
v_stop_boxed_410_ = lean_unbox_usize(v_stop_406_);
lean_dec(v_stop_406_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2932__boxed_408_, v_as_404_, v_i_boxed_409_, v_stop_boxed_410_, v_b_407_);
lean_dec_ref(v_as_404_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_419_, size_t v_i_420_, lean_object* v_bs_421_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_lt(v_i_420_, v_sz_419_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v_bs_421_);
return v___x_423_;
}
else
{
lean_object* v_v_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_v_424_ = lean_array_uget(v_bs_421_, v_i_420_);
v___x_425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_424_);
v___x_426_ = l_Lean_Syntax_isOfKind(v_v_424_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
lean_dec(v_v_424_);
lean_dec_ref(v_bs_421_);
v___x_427_ = lean_box(0);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v_bs_x27_429_; size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_428_ = lean_unsigned_to_nat(0u);
v_bs_x27_429_ = lean_array_uset(v_bs_421_, v_i_420_, v___x_428_);
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_420_, v___x_430_);
v___x_432_ = lean_array_uset(v_bs_x27_429_, v_i_420_, v_v_424_);
v_i_420_ = v___x_431_;
v_bs_421_ = v___x_432_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_434_, lean_object* v_i_435_, lean_object* v_bs_436_){
_start:
{
size_t v_sz_boxed_437_; size_t v_i_boxed_438_; lean_object* v_res_439_; 
v_sz_boxed_437_ = lean_unbox_usize(v_sz_434_);
lean_dec(v_sz_434_);
v_i_boxed_438_ = lean_unbox_usize(v_i_435_);
lean_dec(v_i_435_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_437_, v_i_boxed_438_, v_bs_436_);
return v_res_439_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_447_ = l_Lean_stringToMessageData(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_455_ = l_Lean_stringToMessageData(v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_458_);
v___x_464_ = l_Lean_Syntax_isOfKind(v_kv_458_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_466_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_458_, v___x_465_, v_a_459_, v_a_460_, v_a_461_);
lean_dec_ref(v_a_459_);
lean_dec(v_kv_458_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = l_Lean_Syntax_getArg(v_kv_458_, v___x_467_);
v___x_469_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_468_);
v___x_470_ = l_Lean_Syntax_isOfKind(v___x_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_kv_458_);
v___x_471_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_472_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_468_, v___x_471_, v_a_459_, v_a_460_, v_a_461_);
lean_dec_ref(v_a_459_);
lean_dec(v___x_468_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; lean_object* v_v_474_; lean_object* v___y_476_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_473_ = lean_unsigned_to_nat(2u);
v_v_474_ = l_Lean_Syntax_getArg(v_kv_458_, v___x_473_);
lean_dec(v_kv_458_);
v___x_582_ = l_Lean_Syntax_getArg(v___x_468_, v___x_467_);
v___x_583_ = l_Lean_Syntax_getArgs(v___x_582_);
lean_dec(v___x_582_);
v___x_584_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_585_ = lean_array_get_size(v___x_583_);
v___x_586_ = lean_nat_dec_lt(v___x_467_, v___x_585_);
if (v___x_586_ == 0)
{
lean_dec_ref(v___x_583_);
v___y_476_ = v___x_584_;
goto v___jp_475_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; lean_object* v_snd_592_; 
v___x_587_ = lean_box(v___x_586_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_584_);
v___x_589_ = ((size_t)0ULL);
v___x_590_ = lean_usize_of_nat(v___x_585_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_470_, v___x_583_, v___x_589_, v___x_590_, v___x_588_);
lean_dec_ref(v___x_583_);
v_snd_592_ = lean_ctor_get(v___x_591_, 1);
lean_inc(v_snd_592_);
lean_dec_ref(v___x_591_);
v___y_476_ = v_snd_592_;
goto v___jp_475_;
}
v___jp_475_:
{
size_t v_sz_477_; size_t v___x_478_; lean_object* v___x_479_; 
v_sz_477_ = lean_array_size(v___y_476_);
v___x_478_ = ((size_t)0ULL);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_477_, v___x_478_, v___y_476_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_v_474_);
v___x_480_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_481_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_468_, v___x_480_, v_a_459_, v_a_460_, v_a_461_);
lean_dec_ref(v_a_459_);
lean_dec(v___x_468_);
return v___x_481_;
}
else
{
lean_object* v_val_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_tailKeyStx_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_val_482_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v___x_479_, 1);
v___x_483_ = lean_box(0);
v___x_484_ = lean_array_get_size(v_val_482_);
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_sub(v___x_484_, v___x_485_);
v_tailKeyStx_487_ = lean_array_get(v___x_483_, v_val_482_, v___x_486_);
lean_dec(v___x_486_);
v___x_488_ = lean_array_pop(v_val_482_);
v___x_489_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_488_, v_a_459_, v_a_460_, v_a_461_);
lean_dec_ref(v___x_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v_fst_491_; lean_object* v_snd_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_573_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v_fst_491_ = lean_ctor_get(v_a_490_, 0);
v_snd_492_ = lean_ctor_get(v_a_490_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_a_490_);
if (v_isSharedCheck_573_ == 0)
{
v___x_494_ = v_a_490_;
v_isShared_495_ = v_isSharedCheck_573_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_snd_492_);
lean_inc(v_fst_491_);
lean_dec(v_a_490_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_573_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; 
lean_inc(v_tailKeyStx_487_);
v___x_496_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_487_, v_a_460_, v_a_461_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v_keyTys_498_; lean_object* v_arrKeyTys_499_; lean_object* v_arrParents_500_; lean_object* v_currArrKey_501_; lean_object* v_currKey_502_; lean_object* v_items_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v_keyTys_498_ = lean_ctor_get(v_snd_492_, 0);
v_arrKeyTys_499_ = lean_ctor_get(v_snd_492_, 1);
v_arrParents_500_ = lean_ctor_get(v_snd_492_, 2);
v_currArrKey_501_ = lean_ctor_get(v_snd_492_, 3);
v_currKey_502_ = lean_ctor_get(v_snd_492_, 4);
v_items_503_ = lean_ctor_get(v_snd_492_, 5);
v___x_504_ = l_Lean_Name_str___override(v_fst_491_, v_a_497_);
v___x_505_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_498_, v___x_504_);
if (lean_obj_tag(v___x_505_) == 1)
{
lean_object* v_val_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_525_; 
lean_del_object(v___x_494_);
lean_dec(v_v_474_);
lean_dec(v___x_468_);
v_val_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_525_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_525_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_val_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_525_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_511_ = lean_unbox(v_val_506_);
lean_dec(v_val_506_);
v___x_512_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_511_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 3);
lean_ctor_set(v___x_508_, 0, v___x_512_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_524_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_515_ = l_Lean_MessageData_ofFormat(v___x_514_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_510_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l_Lean_MessageData_ofName(v___x_504_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_487_, v___x_522_, v_snd_492_, v_a_460_, v_a_461_);
lean_dec(v_snd_492_);
lean_dec(v_tailKeyStx_487_);
return v___x_523_;
}
}
}
else
{
lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_558_; 
lean_inc_ref(v_items_503_);
lean_inc(v_currKey_502_);
lean_inc(v_currArrKey_501_);
lean_inc(v_arrParents_500_);
lean_inc(v_arrKeyTys_499_);
lean_inc(v_keyTys_498_);
lean_dec(v___x_505_);
lean_dec(v_tailKeyStx_487_);
v_isSharedCheck_558_ = !lean_is_exclusive(v_snd_492_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; lean_object* v_unused_560_; lean_object* v_unused_561_; lean_object* v_unused_562_; lean_object* v_unused_563_; lean_object* v_unused_564_; 
v_unused_559_ = lean_ctor_get(v_snd_492_, 5);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_snd_492_, 4);
lean_dec(v_unused_560_);
v_unused_561_ = lean_ctor_get(v_snd_492_, 3);
lean_dec(v_unused_561_);
v_unused_562_ = lean_ctor_get(v_snd_492_, 2);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_snd_492_, 1);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_snd_492_, 0);
lean_dec(v_unused_564_);
v___x_527_ = v_snd_492_;
v_isShared_528_ = v_isSharedCheck_558_;
goto v_resetjp_526_;
}
else
{
lean_dec(v_snd_492_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_558_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lake_Toml_elabVal(v_v_474_, v_a_460_, v_a_461_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_549_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_549_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_549_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_549_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_534_ = lean_box(0);
v___x_535_ = 0;
v___x_536_ = lean_box(v___x_535_);
lean_inc(v___x_504_);
v___x_537_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_504_, v___x_536_, v_keyTys_498_);
v___x_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_538_, 0, v___x_468_);
lean_ctor_set(v___x_538_, 1, v___x_504_);
lean_ctor_set(v___x_538_, 2, v_a_530_);
v___x_539_ = lean_array_push(v_items_503_, v___x_538_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 5, v___x_539_);
lean_ctor_set(v___x_527_, 0, v___x_537_);
v___x_541_ = v___x_527_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_arrKeyTys_499_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_arrParents_500_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_currArrKey_501_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v_currKey_502_);
lean_ctor_set(v_reuseFailAlloc_548_, 5, v___x_539_);
v___x_541_ = v_reuseFailAlloc_548_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v___x_541_);
lean_ctor_set(v___x_494_, 0, v___x_534_);
v___x_543_ = v___x_494_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_543_);
v___x_545_ = v___x_532_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_del_object(v___x_527_);
lean_dec(v___x_504_);
lean_dec_ref(v_items_503_);
lean_dec(v_currKey_502_);
lean_dec(v_currArrKey_501_);
lean_dec(v_arrParents_500_);
lean_dec(v_arrKeyTys_499_);
lean_dec(v_keyTys_498_);
lean_del_object(v___x_494_);
lean_dec(v___x_468_);
v_a_550_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_529_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_529_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_del_object(v___x_494_);
lean_dec(v_snd_492_);
lean_dec(v_fst_491_);
lean_dec(v_tailKeyStx_487_);
lean_dec(v_v_474_);
lean_dec(v___x_468_);
v_a_565_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_496_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_496_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec(v_tailKeyStx_487_);
lean_dec(v_v_474_);
lean_dec(v___x_468_);
v_a_574_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_489_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_489_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_593_, v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
return v_res_598_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_601_ = l_Lean_stringToMessageData(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_602_, size_t v_i_603_, size_t v_stop_604_, lean_object* v_b_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_fst_611_; lean_object* v_snd_612_; uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_eq(v_i_603_, v_stop_604_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_array_uget_borrowed(v_as_602_, v_i_603_);
lean_inc(v___x_617_);
v___x_618_ = l_Lake_Toml_elabSimpleKey(v___x_617_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v_keyTys_620_; lean_object* v_arrKeyTys_621_; lean_object* v_arrParents_622_; lean_object* v_currArrKey_623_; lean_object* v_currKey_624_; lean_object* v_items_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v_keyTys_620_ = lean_ctor_get(v___y_606_, 0);
v_arrKeyTys_621_ = lean_ctor_get(v___y_606_, 1);
v_arrParents_622_ = lean_ctor_get(v___y_606_, 2);
v_currArrKey_623_ = lean_ctor_get(v___y_606_, 3);
v_currKey_624_ = lean_ctor_get(v___y_606_, 4);
v_items_625_ = lean_ctor_get(v___y_606_, 5);
v___x_626_ = l_Lean_Name_str___override(v_b_605_, v_a_619_);
v___x_627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_620_, v___x_626_);
if (lean_obj_tag(v___x_627_) == 1)
{
lean_object* v_val_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_689_; 
v_val_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_689_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_689_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_val_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_689_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
uint8_t v___x_632_; 
v___x_632_ = lean_unbox(v_val_628_);
switch(v___x_632_)
{
case 2:
{
lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_657_; 
lean_inc_ref(v_items_625_);
lean_inc(v_currKey_624_);
lean_inc(v_arrParents_622_);
lean_inc(v_arrKeyTys_621_);
lean_del_object(v___x_630_);
lean_dec(v_val_628_);
v_isSharedCheck_657_ = !lean_is_exclusive(v___y_606_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; lean_object* v_unused_659_; lean_object* v_unused_660_; lean_object* v_unused_661_; lean_object* v_unused_662_; lean_object* v_unused_663_; 
v_unused_658_ = lean_ctor_get(v___y_606_, 5);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v___y_606_, 4);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v___y_606_, 3);
lean_dec(v_unused_660_);
v_unused_661_ = lean_ctor_get(v___y_606_, 2);
lean_dec(v_unused_661_);
v_unused_662_ = lean_ctor_get(v___y_606_, 1);
lean_dec(v_unused_662_);
v_unused_663_ = lean_ctor_get(v___y_606_, 0);
lean_dec(v_unused_663_);
v___x_634_ = v___y_606_;
v_isShared_635_ = v_isSharedCheck_657_;
goto v_resetjp_633_;
}
else
{
lean_dec(v___y_606_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_657_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_621_, v___x_626_);
if (lean_obj_tag(v___x_636_) == 1)
{
lean_object* v_val_637_; lean_object* v___x_639_; 
v_val_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v___x_636_, 1);
lean_inc(v___x_626_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 3, v___x_626_);
lean_ctor_set(v___x_634_, 0, v_val_637_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_val_637_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_arrKeyTys_621_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_arrParents_622_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v_currKey_624_);
lean_ctor_set(v_reuseFailAlloc_640_, 5, v_items_625_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
v_fst_611_ = v___x_626_;
v_snd_612_ = v___x_639_;
goto v___jp_610_;
}
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v___x_636_);
lean_del_object(v___x_634_);
lean_dec_ref(v_items_625_);
lean_dec(v_currKey_624_);
lean_dec(v_arrParents_622_);
lean_dec(v_arrKeyTys_621_);
v___x_641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_626_);
v___x_642_ = l_Lean_MessageData_ofName(v___x_626_);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_645_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v_snd_648_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v_snd_648_ = lean_ctor_get(v_a_647_, 1);
lean_inc(v_snd_648_);
lean_dec(v_a_647_);
v_fst_611_ = v___x_626_;
v_snd_612_ = v_snd_648_;
goto v___jp_610_;
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v___x_626_);
v_a_649_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_646_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_646_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
}
case 1:
{
lean_del_object(v___x_630_);
lean_dec(v_val_628_);
v_fst_611_ = v___x_626_;
v_snd_612_ = v___y_606_;
goto v___jp_610_;
}
case 4:
{
lean_del_object(v___x_630_);
lean_dec(v_val_628_);
v_fst_611_ = v___x_626_;
v_snd_612_ = v___y_606_;
goto v___jp_610_;
}
case 3:
{
lean_del_object(v___x_630_);
lean_dec(v_val_628_);
v_fst_611_ = v___x_626_;
v_snd_612_ = v___y_606_;
goto v___jp_610_;
}
default: 
{
lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_665_ = lean_unbox(v_val_628_);
lean_dec(v_val_628_);
v___x_666_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_665_);
if (v_isShared_631_ == 0)
{
lean_ctor_set_tag(v___x_630_, 3);
lean_ctor_set(v___x_630_, 0, v___x_666_);
v___x_668_ = v___x_630_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_688_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_669_ = l_Lean_MessageData_ofFormat(v___x_668_);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_664_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
lean_inc(v___x_626_);
v___x_673_ = l_Lean_MessageData_ofName(v___x_626_);
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_617_, v___x_676_, v___y_606_, v___y_607_, v___y_608_);
lean_dec_ref(v___y_606_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v_snd_679_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v_snd_679_ = lean_ctor_get(v_a_678_, 1);
lean_inc(v_snd_679_);
lean_dec(v_a_678_);
v_fst_611_ = v___x_626_;
v_snd_612_ = v_snd_679_;
goto v___jp_610_;
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v___x_626_);
v_a_680_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_677_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_677_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
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
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_699_; 
lean_inc_ref(v_items_625_);
lean_inc(v_currKey_624_);
lean_inc(v_currArrKey_623_);
lean_inc(v_arrParents_622_);
lean_inc(v_arrKeyTys_621_);
lean_inc(v_keyTys_620_);
lean_dec(v___x_627_);
v_isSharedCheck_699_ = !lean_is_exclusive(v___y_606_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; lean_object* v_unused_701_; lean_object* v_unused_702_; lean_object* v_unused_703_; lean_object* v_unused_704_; lean_object* v_unused_705_; 
v_unused_700_ = lean_ctor_get(v___y_606_, 5);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v___y_606_, 4);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v___y_606_, 3);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v___y_606_, 2);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v___y_606_, 1);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v___y_606_, 0);
lean_dec(v_unused_705_);
v___x_691_ = v___y_606_;
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
else
{
lean_dec(v___y_606_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_693_ = 4;
v___x_694_ = lean_box(v___x_693_);
lean_inc(v___x_626_);
v___x_695_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_626_, v___x_694_, v_keyTys_620_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_695_);
v___x_697_ = v___x_691_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_arrKeyTys_621_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_arrParents_622_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_currArrKey_623_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_currKey_624_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v_items_625_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v_fst_611_ = v___x_626_;
v_snd_612_ = v___x_697_;
goto v___jp_610_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v___y_606_);
lean_dec(v_b_605_);
v_a_706_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_618_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_618_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v_b_605_);
lean_ctor_set(v___x_714_, 1, v___y_606_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
v___jp_610_:
{
size_t v___x_613_; size_t v___x_614_; 
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_603_, v___x_613_);
v_i_603_ = v___x_614_;
v_b_605_ = v_fst_611_;
v___y_606_ = v_snd_612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_716_, lean_object* v_i_717_, lean_object* v_stop_718_, lean_object* v_b_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
size_t v_i_boxed_724_; size_t v_stop_boxed_725_; lean_object* v_res_726_; 
v_i_boxed_724_ = lean_unbox_usize(v_i_717_);
lean_dec(v_i_717_);
v_stop_boxed_725_ = lean_unbox_usize(v_stop_718_);
lean_dec(v_stop_718_);
v_res_726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_716_, v_i_boxed_724_, v_stop_boxed_725_, v_b_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_as_716_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_727_, lean_object* v_k_728_){
_start:
{
if (lean_obj_tag(v_t_727_) == 0)
{
lean_object* v_k_729_; lean_object* v_v_730_; lean_object* v_l_731_; lean_object* v_r_732_; uint8_t v___x_733_; 
v_k_729_ = lean_ctor_get(v_t_727_, 1);
v_v_730_ = lean_ctor_get(v_t_727_, 2);
v_l_731_ = lean_ctor_get(v_t_727_, 3);
v_r_732_ = lean_ctor_get(v_t_727_, 4);
v___x_733_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_728_, v_k_729_);
switch(v___x_733_)
{
case 0:
{
v_t_727_ = v_l_731_;
goto _start;
}
case 1:
{
lean_object* v___x_735_; 
lean_inc(v_v_730_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v_v_730_);
return v___x_735_;
}
default: 
{
v_t_727_ = v_r_732_;
goto _start;
}
}
}
else
{
lean_object* v___x_737_; 
v___x_737_ = lean_box(0);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_738_, lean_object* v_k_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_738_, v_k_739_);
lean_dec(v_k_739_);
lean_dec(v_t_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_keyTys_746_; lean_object* v_arrKeyTys_747_; lean_object* v_arrParents_748_; lean_object* v_currArrKey_749_; lean_object* v_currKey_750_; lean_object* v_items_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_779_; 
v_keyTys_746_ = lean_ctor_get(v_a_742_, 0);
v_arrKeyTys_747_ = lean_ctor_get(v_a_742_, 1);
v_arrParents_748_ = lean_ctor_get(v_a_742_, 2);
v_currArrKey_749_ = lean_ctor_get(v_a_742_, 3);
v_currKey_750_ = lean_ctor_get(v_a_742_, 4);
v_items_751_ = lean_ctor_get(v_a_742_, 5);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_742_);
if (v_isSharedCheck_779_ == 0)
{
v___x_753_ = v_a_742_;
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_items_751_);
lean_inc(v_currKey_750_);
lean_inc(v_currArrKey_749_);
lean_inc(v_arrParents_748_);
lean_inc(v_arrKeyTys_747_);
lean_inc(v_keyTys_746_);
lean_dec(v_a_742_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_arrKeyTys_755_; lean_object* v___x_756_; lean_object* v___y_758_; lean_object* v___x_776_; 
v_arrKeyTys_755_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_749_, v_keyTys_746_, v_arrKeyTys_747_);
v___x_756_ = lean_box(0);
v___x_776_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_755_, v___x_756_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_box(1);
v___y_758_ = v___x_777_;
goto v___jp_757_;
}
else
{
lean_object* v_val_778_; 
v_val_778_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v___x_776_, 1);
v___y_758_ = v_val_778_;
goto v___jp_757_;
}
v___jp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 3, v___x_756_);
lean_ctor_set(v___x_753_, 1, v_arrKeyTys_755_);
lean_ctor_set(v___x_753_, 0, v___y_758_);
v___x_760_ = v___x_753_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___y_758_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_arrKeyTys_755_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_arrParents_748_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_currKey_750_);
lean_ctor_set(v_reuseFailAlloc_775_, 5, v_items_751_);
v___x_760_ = v_reuseFailAlloc_775_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_array_get_size(v_ks_741_);
v___x_763_ = lean_nat_dec_lt(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_756_);
lean_ctor_set(v___x_764_, 1, v___x_760_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
else
{
uint8_t v___x_766_; 
v___x_766_ = lean_nat_dec_le(v___x_762_, v___x_762_);
if (v___x_766_ == 0)
{
if (v___x_763_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_756_);
lean_ctor_set(v___x_767_, 1, v___x_760_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
else
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)0ULL);
v___x_770_ = lean_usize_of_nat(v___x_762_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_741_, v___x_769_, v___x_770_, v___x_756_, v___x_760_, v_a_743_, v_a_744_);
return v___x_771_;
}
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_of_nat(v___x_762_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_741_, v___x_772_, v___x_773_, v___x_756_, v___x_760_, v_a_743_, v_a_744_);
return v___x_774_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec_ref(v_ks_780_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_786_, lean_object* v_t_787_, lean_object* v_k_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_787_, v_k_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_790_, lean_object* v_t_791_, lean_object* v_k_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_790_, v_t_791_, v_k_792_);
lean_dec(v_k_792_);
lean_dec(v_t_791_);
return v_res_793_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
v___x_796_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___y_811_; lean_object* v_keyTys_812_; lean_object* v_arrKeyTys_813_; lean_object* v_arrParents_814_; lean_object* v_currArrKey_815_; lean_object* v_items_816_; lean_object* v_toCold_828_; lean_object* v_options_829_; lean_object* v_currRecDepth_830_; lean_object* v_maxRecDepth_831_; lean_object* v_ref_832_; lean_object* v_currNamespace_833_; lean_object* v_openDecls_834_; lean_object* v_initHeartbeats_835_; lean_object* v_maxHeartbeats_836_; lean_object* v_currMacroScope_837_; uint8_t v_diag_838_; uint8_t v_suppressElabErrors_839_; lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v_ref_842_; lean_object* v___x_843_; 
v_toCold_828_ = lean_ctor_get(v_a_807_, 0);
v_options_829_ = lean_ctor_get(v_a_807_, 1);
v_currRecDepth_830_ = lean_ctor_get(v_a_807_, 2);
v_maxRecDepth_831_ = lean_ctor_get(v_a_807_, 3);
v_ref_832_ = lean_ctor_get(v_a_807_, 4);
v_currNamespace_833_ = lean_ctor_get(v_a_807_, 5);
v_openDecls_834_ = lean_ctor_get(v_a_807_, 6);
v_initHeartbeats_835_ = lean_ctor_get(v_a_807_, 7);
v_maxHeartbeats_836_ = lean_ctor_get(v_a_807_, 8);
v_currMacroScope_837_ = lean_ctor_get(v_a_807_, 9);
v_diag_838_ = lean_ctor_get_uint8(v_a_807_, sizeof(void*)*10);
v_suppressElabErrors_839_ = lean_ctor_get_uint8(v_a_807_, sizeof(void*)*10 + 1);
v___x_840_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_805_);
v___x_841_ = l_Lean_Syntax_isOfKind(v_x_805_, v___x_840_);
v_ref_842_ = l_Lean_replaceRef(v_x_805_, v_ref_832_);
lean_inc(v_currMacroScope_837_);
lean_inc(v_maxHeartbeats_836_);
lean_inc(v_initHeartbeats_835_);
lean_inc(v_openDecls_834_);
lean_inc(v_currNamespace_833_);
lean_inc(v_maxRecDepth_831_);
lean_inc(v_currRecDepth_830_);
lean_inc_ref(v_options_829_);
lean_inc_ref(v_toCold_828_);
v___x_843_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_843_, 0, v_toCold_828_);
lean_ctor_set(v___x_843_, 1, v_options_829_);
lean_ctor_set(v___x_843_, 2, v_currRecDepth_830_);
lean_ctor_set(v___x_843_, 3, v_maxRecDepth_831_);
lean_ctor_set(v___x_843_, 4, v_ref_842_);
lean_ctor_set(v___x_843_, 5, v_currNamespace_833_);
lean_ctor_set(v___x_843_, 6, v_openDecls_834_);
lean_ctor_set(v___x_843_, 7, v_initHeartbeats_835_);
lean_ctor_set(v___x_843_, 8, v_maxHeartbeats_836_);
lean_ctor_set(v___x_843_, 9, v_currMacroScope_837_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*10, v_diag_838_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*10 + 1, v_suppressElabErrors_839_);
if (v___x_841_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5);
v___x_845_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_805_, v___x_844_, v_a_806_, v___x_843_, v_a_808_);
lean_dec_ref_known(v___x_843_, 10);
lean_dec_ref(v_a_806_);
lean_dec(v_x_805_);
return v___x_845_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___y_849_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = l_Lean_Syntax_getArg(v_x_805_, v___x_846_);
v___x_917_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_847_);
v___x_918_ = l_Lean_Syntax_isOfKind(v___x_847_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_x_805_);
v___x_919_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_920_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_847_, v___x_919_, v_a_806_, v___x_843_, v_a_808_);
lean_dec_ref_known(v___x_843_, 10);
lean_dec_ref(v_a_806_);
lean_dec(v___x_847_);
return v___x_920_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = l_Lean_Syntax_getArg(v___x_847_, v___x_921_);
v___x_923_ = l_Lean_Syntax_getArgs(v___x_922_);
lean_dec(v___x_922_);
v___x_924_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_925_ = lean_array_get_size(v___x_923_);
v___x_926_ = lean_nat_dec_lt(v___x_921_, v___x_925_);
if (v___x_926_ == 0)
{
lean_dec_ref(v___x_923_);
v___y_849_ = v___x_924_;
goto v___jp_848_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; size_t v___x_929_; size_t v___x_930_; lean_object* v___x_931_; lean_object* v_snd_932_; 
v___x_927_ = lean_box(v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_924_);
v___x_929_ = ((size_t)0ULL);
v___x_930_ = lean_usize_of_nat(v___x_925_);
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_918_, v___x_923_, v___x_929_, v___x_930_, v___x_928_);
lean_dec_ref(v___x_923_);
v_snd_932_ = lean_ctor_get(v___x_931_, 1);
lean_inc(v_snd_932_);
lean_dec_ref(v___x_931_);
v___y_849_ = v_snd_932_;
goto v___jp_848_;
}
}
v___jp_848_:
{
size_t v_sz_850_; size_t v___x_851_; lean_object* v___x_852_; 
v_sz_850_ = lean_array_size(v___y_849_);
v___x_851_ = ((size_t)0ULL);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_850_, v___x_851_, v___y_849_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v_x_805_);
v___x_853_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_854_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_847_, v___x_853_, v_a_806_, v___x_843_, v_a_808_);
lean_dec_ref_known(v___x_843_, 10);
lean_dec_ref(v_a_806_);
lean_dec(v___x_847_);
return v___x_854_;
}
else
{
lean_object* v_val_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_tailKey_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v___x_847_);
v_val_855_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v___x_852_, 1);
v___x_856_ = lean_box(0);
v___x_857_ = lean_array_get_size(v_val_855_);
v___x_858_ = lean_nat_sub(v___x_857_, v___x_846_);
v_tailKey_859_ = lean_array_get(v___x_856_, v_val_855_, v___x_858_);
lean_dec(v___x_858_);
v___x_860_ = lean_array_pop(v_val_855_);
v___x_861_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_860_, v_a_806_, v___x_843_, v_a_808_);
lean_dec_ref(v___x_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v_fst_863_; lean_object* v_snd_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_908_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v_fst_863_ = lean_ctor_get(v_a_862_, 0);
v_snd_864_ = lean_ctor_get(v_a_862_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_908_ == 0)
{
v___x_866_ = v_a_862_;
v_isShared_867_ = v_isSharedCheck_908_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snd_864_);
lean_inc(v_fst_863_);
lean_dec(v_a_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_908_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; 
lean_inc(v_tailKey_859_);
v___x_868_ = l_Lake_Toml_elabSimpleKey(v_tailKey_859_, v___x_843_, v_a_808_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v_keyTys_870_; lean_object* v_arrKeyTys_871_; lean_object* v_arrParents_872_; lean_object* v_currArrKey_873_; lean_object* v_items_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v_keyTys_870_ = lean_ctor_get(v_snd_864_, 0);
v_arrKeyTys_871_ = lean_ctor_get(v_snd_864_, 1);
v_arrParents_872_ = lean_ctor_get(v_snd_864_, 2);
v_currArrKey_873_ = lean_ctor_get(v_snd_864_, 3);
v_items_874_ = lean_ctor_get(v_snd_864_, 5);
v___x_875_ = l_Lean_Name_str___override(v_fst_863_, v_a_869_);
v___x_876_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_870_, v___x_875_);
if (lean_obj_tag(v___x_876_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_899_; 
v_val_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_899_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_899_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_val_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_899_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
uint8_t v___x_881_; 
v___x_881_ = lean_unbox(v_val_877_);
if (v___x_881_ == 4)
{
lean_inc_ref(v_items_874_);
lean_inc(v_currArrKey_873_);
lean_inc(v_arrParents_872_);
lean_inc(v_arrKeyTys_871_);
lean_inc(v_keyTys_870_);
lean_del_object(v___x_879_);
lean_dec(v_val_877_);
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_tailKey_859_);
lean_dec_ref_known(v___x_843_, 10);
v___y_811_ = v___x_875_;
v_keyTys_812_ = v_keyTys_870_;
v_arrKeyTys_813_ = v_arrKeyTys_871_;
v_arrParents_814_ = v_arrParents_872_;
v_currArrKey_815_ = v_currArrKey_873_;
v_items_816_ = v_items_874_;
goto v___jp_810_;
}
else
{
lean_object* v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
lean_dec(v_x_805_);
v___x_882_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_883_ = lean_unbox(v_val_877_);
lean_dec(v_val_877_);
v___x_884_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_883_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 3);
lean_ctor_set(v___x_879_, 0, v___x_884_);
v___x_886_ = v___x_879_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_898_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = l_Lean_MessageData_ofFormat(v___x_886_);
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 7);
lean_ctor_set(v___x_866_, 1, v___x_887_);
lean_ctor_set(v___x_866_, 0, v___x_882_);
v___x_889_ = v___x_866_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_887_);
v___x_889_ = v_reuseFailAlloc_897_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_MessageData_ofName(v___x_875_);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_859_, v___x_895_, v_snd_864_, v___x_843_, v_a_808_);
lean_dec_ref_known(v___x_843_, 10);
lean_dec(v_snd_864_);
lean_dec(v_tailKey_859_);
return v___x_896_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_874_);
lean_inc(v_currArrKey_873_);
lean_inc(v_arrParents_872_);
lean_inc(v_arrKeyTys_871_);
lean_inc(v_keyTys_870_);
lean_dec(v___x_876_);
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_tailKey_859_);
lean_dec_ref_known(v___x_843_, 10);
v___y_811_ = v___x_875_;
v_keyTys_812_ = v_keyTys_870_;
v_arrKeyTys_813_ = v_arrKeyTys_871_;
v_arrParents_814_ = v_arrParents_872_;
v_currArrKey_815_ = v_currArrKey_873_;
v_items_816_ = v_items_874_;
goto v___jp_810_;
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_fst_863_);
lean_dec(v_tailKey_859_);
lean_dec_ref_known(v___x_843_, 10);
lean_dec(v_x_805_);
v_a_900_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_868_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_868_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec(v_tailKey_859_);
lean_dec_ref_known(v___x_843_, 10);
lean_dec(v_x_805_);
v_a_909_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_861_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_861_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
v___jp_810_:
{
lean_object* v___x_817_; uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_817_ = lean_box(0);
v___x_818_ = 1;
v___x_819_ = lean_box(v___x_818_);
lean_inc_n(v___y_811_, 2);
v___x_820_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_811_, v___x_819_, v_keyTys_812_);
v___x_821_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc(v_x_805_);
v___x_822_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_822_, 0, v_x_805_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_823_, 0, v_x_805_);
lean_ctor_set(v___x_823_, 1, v___y_811_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
v___x_824_ = lean_array_push(v_items_816_, v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_825_, 0, v___x_820_);
lean_ctor_set(v___x_825_, 1, v_arrKeyTys_813_);
lean_ctor_set(v___x_825_, 2, v_arrParents_814_);
lean_ctor_set(v___x_825_, 3, v_currArrKey_815_);
lean_ctor_set(v___x_825_, 4, v___y_811_);
lean_ctor_set(v___x_825_, 5, v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_817_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_938_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_toCold_952_; lean_object* v_options_953_; lean_object* v_currRecDepth_954_; lean_object* v_maxRecDepth_955_; lean_object* v_ref_956_; lean_object* v_currNamespace_957_; lean_object* v_openDecls_958_; lean_object* v_initHeartbeats_959_; lean_object* v_maxHeartbeats_960_; lean_object* v_currMacroScope_961_; uint8_t v_diag_962_; uint8_t v_suppressElabErrors_963_; lean_object* v___x_964_; uint8_t v___x_965_; lean_object* v_ref_966_; lean_object* v___x_967_; lean_object* v___y_969_; 
v_toCold_952_ = lean_ctor_get(v_a_949_, 0);
v_options_953_ = lean_ctor_get(v_a_949_, 1);
v_currRecDepth_954_ = lean_ctor_get(v_a_949_, 2);
v_maxRecDepth_955_ = lean_ctor_get(v_a_949_, 3);
v_ref_956_ = lean_ctor_get(v_a_949_, 4);
v_currNamespace_957_ = lean_ctor_get(v_a_949_, 5);
v_openDecls_958_ = lean_ctor_get(v_a_949_, 6);
v_initHeartbeats_959_ = lean_ctor_get(v_a_949_, 7);
v_maxHeartbeats_960_ = lean_ctor_get(v_a_949_, 8);
v_currMacroScope_961_ = lean_ctor_get(v_a_949_, 9);
v_diag_962_ = lean_ctor_get_uint8(v_a_949_, sizeof(void*)*10);
v_suppressElabErrors_963_ = lean_ctor_get_uint8(v_a_949_, sizeof(void*)*10 + 1);
v___x_964_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_947_);
v___x_965_ = l_Lean_Syntax_isOfKind(v_x_947_, v___x_964_);
v_ref_966_ = l_Lean_replaceRef(v_x_947_, v_ref_956_);
lean_inc(v_currMacroScope_961_);
lean_inc(v_maxHeartbeats_960_);
lean_inc(v_initHeartbeats_959_);
lean_inc(v_openDecls_958_);
lean_inc(v_currNamespace_957_);
lean_inc(v_maxRecDepth_955_);
lean_inc(v_currRecDepth_954_);
lean_inc_ref(v_options_953_);
lean_inc_ref(v_toCold_952_);
v___x_967_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_967_, 0, v_toCold_952_);
lean_ctor_set(v___x_967_, 1, v_options_953_);
lean_ctor_set(v___x_967_, 2, v_currRecDepth_954_);
lean_ctor_set(v___x_967_, 3, v_maxRecDepth_955_);
lean_ctor_set(v___x_967_, 4, v_ref_966_);
lean_ctor_set(v___x_967_, 5, v_currNamespace_957_);
lean_ctor_set(v___x_967_, 6, v_openDecls_958_);
lean_ctor_set(v___x_967_, 7, v_initHeartbeats_959_);
lean_ctor_set(v___x_967_, 8, v_maxHeartbeats_960_);
lean_ctor_set(v___x_967_, 9, v_currMacroScope_961_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*10, v_diag_962_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*10 + 1, v_suppressElabErrors_963_);
if (v___x_965_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_977_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_947_, v___x_976_, v_a_948_, v___x_967_, v_a_950_);
lean_dec_ref_known(v___x_967_, 10);
lean_dec_ref(v_a_948_);
lean_dec(v_x_947_);
return v___x_977_;
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___y_983_; 
v___x_978_ = lean_unsigned_to_nat(2u);
v___x_979_ = l_Lean_Syntax_getArg(v_x_947_, v___x_978_);
v___x_980_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_979_);
v___x_981_ = l_Lean_Syntax_isOfKind(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v___x_979_);
v___x_1117_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1118_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_947_, v___x_1117_, v_a_948_, v___x_967_, v_a_950_);
lean_dec_ref_known(v___x_967_, 10);
lean_dec_ref(v_a_948_);
lean_dec(v_x_947_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = l_Lean_Syntax_getArg(v___x_979_, v___x_1119_);
lean_dec(v___x_979_);
v___x_1121_ = l_Lean_Syntax_getArgs(v___x_1120_);
lean_dec(v___x_1120_);
v___x_1122_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1123_ = lean_array_get_size(v___x_1121_);
v___x_1124_ = lean_nat_dec_lt(v___x_1119_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_dec_ref(v___x_1121_);
v___y_983_ = v___x_1122_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; lean_object* v_snd_1130_; 
v___x_1125_ = lean_box(v___x_1124_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1122_);
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = lean_usize_of_nat(v___x_1123_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_981_, v___x_1121_, v___x_1127_, v___x_1128_, v___x_1126_);
lean_dec_ref(v___x_1121_);
v_snd_1130_ = lean_ctor_get(v___x_1129_, 1);
lean_inc(v_snd_1130_);
lean_dec_ref(v___x_1129_);
v___y_983_ = v_snd_1130_;
goto v___jp_982_;
}
}
v___jp_982_:
{
size_t v_sz_984_; size_t v___x_985_; lean_object* v___x_986_; 
v_sz_984_ = lean_array_size(v___y_983_);
v___x_985_ = ((size_t)0ULL);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_984_, v___x_985_, v___y_983_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_988_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_947_, v___x_987_, v_a_948_, v___x_967_, v_a_950_);
lean_dec_ref_known(v___x_967_, 10);
lean_dec_ref(v_a_948_);
lean_dec(v_x_947_);
return v___x_988_;
}
else
{
lean_object* v_val_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_tailKey_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_val_989_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_val_989_);
lean_dec_ref_known(v___x_986_, 1);
v___x_990_ = lean_box(0);
v___x_991_ = lean_array_get_size(v_val_989_);
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_nat_sub(v___x_991_, v___x_992_);
v_tailKey_994_ = lean_array_get(v___x_990_, v_val_989_, v___x_993_);
lean_dec(v___x_993_);
v___x_995_ = lean_array_pop(v_val_989_);
v___x_996_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_995_, v_a_948_, v___x_967_, v_a_950_);
lean_dec_ref(v___x_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1108_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v_fst_998_ = lean_ctor_get(v_a_997_, 0);
v_snd_999_ = lean_ctor_get(v_a_997_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_a_997_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1001_ = v_a_997_;
v_isShared_1002_ = v_isSharedCheck_1108_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snd_999_);
lean_inc(v_fst_998_);
lean_dec(v_a_997_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1108_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; 
lean_inc(v_tailKey_994_);
v___x_1003_ = l_Lake_Toml_elabSimpleKey(v_tailKey_994_, v___x_967_, v_a_950_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1099_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1099_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1099_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_keyTys_1008_; lean_object* v_arrKeyTys_1009_; lean_object* v_arrParents_1010_; lean_object* v_currArrKey_1011_; lean_object* v_items_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_keyTys_1008_ = lean_ctor_get(v_snd_999_, 0);
v_arrKeyTys_1009_ = lean_ctor_get(v_snd_999_, 1);
v_arrParents_1010_ = lean_ctor_get(v_snd_999_, 2);
v_currArrKey_1011_ = lean_ctor_get(v_snd_999_, 3);
v_items_1012_ = lean_ctor_get(v_snd_999_, 5);
v___x_1013_ = l_Lean_Name_str___override(v_fst_998_, v_a_1004_);
v___x_1014_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_1008_, v___x_1013_);
if (lean_obj_tag(v___x_1014_) == 1)
{
lean_object* v_val_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1066_; 
v_val_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1066_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_val_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1066_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_unbox(v_val_1015_);
if (v___x_1019_ == 2)
{
lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1044_; 
lean_inc_ref(v_items_1012_);
lean_inc(v_arrParents_1010_);
lean_inc(v_arrKeyTys_1009_);
lean_del_object(v___x_1017_);
lean_dec(v_val_1015_);
lean_dec(v_tailKey_994_);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_snd_999_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; lean_object* v_unused_1046_; lean_object* v_unused_1047_; lean_object* v_unused_1048_; lean_object* v_unused_1049_; lean_object* v_unused_1050_; 
v_unused_1045_ = lean_ctor_get(v_snd_999_, 5);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v_snd_999_, 4);
lean_dec(v_unused_1046_);
v_unused_1047_ = lean_ctor_get(v_snd_999_, 3);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v_snd_999_, 2);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_snd_999_, 1);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_snd_999_, 0);
lean_dec(v_unused_1050_);
v___x_1021_ = v_snd_999_;
v_isShared_1022_ = v_isSharedCheck_1044_;
goto v_resetjp_1020_;
}
else
{
lean_dec(v_snd_999_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1044_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_1010_, v___x_1013_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_del_object(v___x_1021_);
lean_dec_ref(v_items_1012_);
lean_dec(v_arrParents_1010_);
lean_dec(v_arrKeyTys_1009_);
lean_del_object(v___x_1006_);
lean_del_object(v___x_1001_);
lean_dec(v_x_947_);
v___y_969_ = v___x_1013_;
goto v___jp_968_;
}
else
{
lean_object* v_val_1024_; lean_object* v___x_1025_; 
v_val_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_1009_, v_val_1024_);
lean_dec(v_val_1024_);
if (lean_obj_tag(v___x_1025_) == 1)
{
lean_object* v_val_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_dec_ref_known(v___x_967_, 10);
v_val_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_val_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_947_, 2);
v___x_1029_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_x_947_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_mk_empty_array_with_capacity(v___x_992_);
v___x_1031_ = lean_array_push(v___x_1030_, v___x_1029_);
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_x_947_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
lean_inc_n(v___x_1013_, 2);
v___x_1033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1033_, 0, v_x_947_);
lean_ctor_set(v___x_1033_, 1, v___x_1013_);
lean_ctor_set(v___x_1033_, 2, v___x_1032_);
v___x_1034_ = lean_array_push(v_items_1012_, v___x_1033_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 5, v___x_1034_);
lean_ctor_set(v___x_1021_, 4, v___x_1013_);
lean_ctor_set(v___x_1021_, 3, v___x_1013_);
lean_ctor_set(v___x_1021_, 0, v_val_1026_);
v___x_1036_ = v___x_1021_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_val_1026_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_arrKeyTys_1009_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_arrParents_1010_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1043_, 5, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v___x_1036_);
lean_ctor_set(v___x_1001_, 0, v___x_1027_);
v___x_1038_ = v___x_1001_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1040_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1038_);
v___x_1040_ = v___x_1006_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_dec(v___x_1025_);
lean_del_object(v___x_1021_);
lean_dec_ref(v_items_1012_);
lean_dec(v_arrParents_1010_);
lean_dec(v_arrKeyTys_1009_);
lean_del_object(v___x_1006_);
lean_del_object(v___x_1001_);
lean_dec(v_x_947_);
v___y_969_ = v___x_1013_;
goto v___jp_968_;
}
}
}
}
else
{
lean_object* v___x_1051_; uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_del_object(v___x_1006_);
lean_del_object(v___x_1001_);
lean_dec(v_x_947_);
v___x_1051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1052_ = lean_unbox(v_val_1015_);
lean_dec(v_val_1015_);
v___x_1053_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1052_);
v___x_1054_ = lean_string_append(v___x_1051_, v___x_1053_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
v___x_1057_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1013_, v___x_981_);
v___x_1058_ = lean_string_append(v___x_1056_, v___x_1057_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1060_ = lean_string_append(v___x_1058_, v___x_1059_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 3);
lean_ctor_set(v___x_1017_, 0, v___x_1060_);
v___x_1062_ = v___x_1017_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = l_Lean_MessageData_ofFormat(v___x_1062_);
v___x_1064_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_994_, v___x_1063_, v_snd_999_, v___x_967_, v_a_950_);
lean_dec_ref_known(v___x_967_, 10);
lean_dec(v_snd_999_);
lean_dec(v_tailKey_994_);
return v___x_1064_;
}
}
}
}
else
{
lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1092_; 
lean_inc_ref(v_items_1012_);
lean_inc(v_currArrKey_1011_);
lean_inc(v_arrParents_1010_);
lean_inc(v_arrKeyTys_1009_);
lean_inc(v_keyTys_1008_);
lean_dec(v___x_1014_);
lean_dec(v_tailKey_994_);
lean_dec_ref_known(v___x_967_, 10);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_snd_999_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; lean_object* v_unused_1098_; 
v_unused_1093_ = lean_ctor_get(v_snd_999_, 5);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_snd_999_, 4);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_snd_999_, 3);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_snd_999_, 2);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_snd_999_, 1);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_snd_999_, 0);
lean_dec(v_unused_1098_);
v___x_1068_ = v_snd_999_;
v_isShared_1069_ = v_isSharedCheck_1092_;
goto v_resetjp_1067_;
}
else
{
lean_dec(v_snd_999_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1092_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = 2;
v___x_1072_ = lean_box(v___x_1071_);
lean_inc_n(v___x_1013_, 4);
v___x_1073_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1013_, v___x_1072_, v_keyTys_1008_);
lean_inc(v___x_1073_);
lean_inc(v_currArrKey_1011_);
v___x_1074_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_1011_, v___x_1073_, v_arrKeyTys_1009_);
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1013_, v_currArrKey_1011_, v_arrParents_1010_);
v___x_1076_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_947_, 2);
v___x_1077_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_x_947_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_mk_empty_array_with_capacity(v___x_992_);
v___x_1079_ = lean_array_push(v___x_1078_, v___x_1077_);
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_x_947_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1081_, 0, v_x_947_);
lean_ctor_set(v___x_1081_, 1, v___x_1013_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
v___x_1082_ = lean_array_push(v_items_1012_, v___x_1081_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 5, v___x_1082_);
lean_ctor_set(v___x_1068_, 4, v___x_1013_);
lean_ctor_set(v___x_1068_, 3, v___x_1013_);
lean_ctor_set(v___x_1068_, 2, v___x_1075_);
lean_ctor_set(v___x_1068_, 1, v___x_1074_);
lean_ctor_set(v___x_1068_, 0, v___x_1073_);
v___x_1084_ = v___x_1068_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1091_, 5, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v___x_1084_);
lean_ctor_set(v___x_1001_, 0, v___x_1070_);
v___x_1086_ = v___x_1001_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1086_);
v___x_1088_ = v___x_1006_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_del_object(v___x_1001_);
lean_dec(v_snd_999_);
lean_dec(v_fst_998_);
lean_dec(v_tailKey_994_);
lean_dec_ref_known(v___x_967_, 10);
lean_dec(v_x_947_);
v_a_1100_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1003_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1003_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v_tailKey_994_);
lean_dec_ref_known(v___x_967_, 10);
lean_dec(v_x_947_);
v_a_1109_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_996_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_996_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
v___jp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_970_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_971_ = l_Lean_MessageData_ofName(v___y_969_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_974_, v___x_967_, v_a_950_);
lean_dec_ref_known(v___x_967_, 10);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
return v_res_1136_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1140_);
v___x_1146_ = l_Lean_Syntax_isOfKind(v_x_1140_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_1140_);
v___x_1148_ = l_Lean_Syntax_isOfKind(v_x_1140_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1140_);
v___x_1150_ = l_Lean_Syntax_isOfKind(v_x_1140_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1152_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1140_, v___x_1151_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec_ref(v_a_1141_);
lean_dec(v_x_1140_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1153_;
}
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1154_;
}
}
else
{
lean_object* v___x_1155_; 
v___x_1155_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1162_, lean_object* v_as_1163_, size_t v_i_1164_, size_t v_stop_1165_, lean_object* v_b_1166_){
_start:
{
lean_object* v___y_1168_; uint8_t v___x_1172_; 
v___x_1172_ = lean_usize_dec_eq(v_i_1164_, v_stop_1165_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1176_; 
v___x_1173_ = lean_array_uget_borrowed(v_as_1163_, v_i_1164_);
v_fst_1174_ = lean_ctor_get(v___x_1173_, 0);
v_snd_1175_ = lean_ctor_get(v___x_1173_, 1);
lean_inc(v_fst_1174_);
v___x_1176_ = l_Lean_Name_components(v_fst_1174_);
if (lean_obj_tag(v___x_1176_) == 0)
{
v___y_1168_ = v_b_1166_;
goto v___jp_1167_;
}
else
{
lean_object* v_head_1177_; lean_object* v_tail_1178_; lean_object* v___x_1179_; 
v_head_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_head_1177_);
v_tail_1178_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_tail_1178_);
lean_dec_ref_known(v___x_1176_, 2);
lean_inc(v_snd_1175_);
lean_inc(v_ref_1162_);
v___x_1179_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1166_, v_ref_1162_, v_head_1177_, v_tail_1178_, v_snd_1175_);
v___y_1168_ = v___x_1179_;
goto v___jp_1167_;
}
}
else
{
lean_dec(v_ref_1162_);
return v_b_1166_;
}
v___jp_1167_:
{
size_t v___x_1169_; size_t v___x_1170_; 
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_add(v_i_1164_, v___x_1169_);
v_i_1164_ = v___x_1170_;
v_b_1166_ = v___y_1168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1180_, size_t v_i_1181_, lean_object* v_bs_1182_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_usize_dec_lt(v_i_1181_, v_sz_1180_);
if (v___x_1183_ == 0)
{
return v_bs_1182_;
}
else
{
lean_object* v_v_1184_; lean_object* v___x_1185_; lean_object* v_bs_x27_1186_; lean_object* v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; lean_object* v___x_1190_; 
v_v_1184_ = lean_array_uget(v_bs_1182_, v_i_1181_);
v___x_1185_ = lean_unsigned_to_nat(0u);
v_bs_x27_1186_ = lean_array_uset(v_bs_1182_, v_i_1181_, v___x_1185_);
v___x_1187_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1184_);
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = lean_usize_add(v_i_1181_, v___x_1188_);
v___x_1190_ = lean_array_uset(v_bs_x27_1186_, v_i_1181_, v___x_1187_);
v_i_1181_ = v___x_1189_;
v_bs_1182_ = v___x_1190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1192_){
_start:
{
switch(lean_obj_tag(v_a_1192_))
{
case 6:
{
lean_object* v_xs_1193_; lean_object* v_ref_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1222_; 
v_xs_1193_ = lean_ctor_get(v_a_1192_, 1);
v_ref_1194_ = lean_ctor_get(v_a_1192_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_a_1192_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1196_ = v_a_1192_;
v_isShared_1197_ = v_isSharedCheck_1222_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_xs_1193_);
lean_inc(v_ref_1194_);
lean_dec(v_a_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1222_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_items_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_items_1198_ = lean_ctor_get(v_xs_1193_, 0);
lean_inc_ref(v_items_1198_);
lean_dec_ref(v_xs_1193_);
v___x_1199_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = lean_array_get_size(v_items_1198_);
v___x_1202_ = lean_nat_dec_lt(v___x_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1204_; 
lean_dec_ref(v_items_1198_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v___x_1199_);
v___x_1204_ = v___x_1196_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_ref_1194_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
else
{
uint8_t v___x_1206_; 
v___x_1206_ = lean_nat_dec_le(v___x_1201_, v___x_1201_);
if (v___x_1206_ == 0)
{
if (v___x_1202_ == 0)
{
lean_object* v___x_1208_; 
lean_dec_ref(v_items_1198_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v___x_1199_);
v___x_1208_ = v___x_1196_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_ref_1194_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1199_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
else
{
size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1210_ = ((size_t)0ULL);
v___x_1211_ = lean_usize_of_nat(v___x_1201_);
lean_inc(v_ref_1194_);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1194_, v_items_1198_, v___x_1210_, v___x_1211_, v___x_1199_);
lean_dec_ref(v_items_1198_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v___x_1212_);
v___x_1214_ = v___x_1196_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_ref_1194_);
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
else
{
size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = lean_usize_of_nat(v___x_1201_);
lean_inc(v_ref_1194_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1194_, v_items_1198_, v___x_1216_, v___x_1217_, v___x_1199_);
lean_dec_ref(v_items_1198_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v___x_1218_);
v___x_1220_ = v___x_1196_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_ref_1194_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
case 5:
{
lean_object* v_ref_1223_; lean_object* v_xs_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1234_; 
v_ref_1223_ = lean_ctor_get(v_a_1192_, 0);
v_xs_1224_ = lean_ctor_get(v_a_1192_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_a_1192_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1226_ = v_a_1192_;
v_isShared_1227_ = v_isSharedCheck_1234_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_xs_1224_);
lean_inc(v_ref_1223_);
lean_dec(v_a_1192_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1234_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
size_t v_sz_1228_; size_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v_sz_1228_ = lean_array_size(v_xs_1224_);
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1228_, v___x_1229_, v_xs_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1230_);
v___x_1232_ = v___x_1226_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_ref_1223_);
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
default: 
{
return v_a_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1235_, lean_object* v___x_1236_, lean_object* v_v_x3f_1237_){
_start:
{
if (lean_obj_tag(v_v_x3f_1237_) == 1)
{
lean_object* v_val_1238_; 
v_val_1238_ = lean_ctor_get(v_v_x3f_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v_v_x3f_1237_, 1);
switch(lean_obj_tag(v_val_1238_))
{
case 6:
{
lean_object* v_ref_1239_; lean_object* v_xs_1240_; lean_object* v___x_1241_; 
v_ref_1239_ = lean_ctor_get(v_val_1238_, 0);
lean_inc(v_ref_1239_);
v_xs_1240_ = lean_ctor_get(v_val_1238_, 1);
lean_inc_ref(v_xs_1240_);
lean_dec_ref_known(v_val_1238_, 2);
v___x_1241_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1235_);
if (lean_obj_tag(v___x_1241_) == 6)
{
lean_object* v_xs_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1251_; 
v_xs_1242_ = lean_ctor_get(v___x_1241_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1252_);
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_xs_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_items_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v_items_1246_ = lean_ctor_get(v_xs_1242_, 0);
lean_inc_ref(v_items_1246_);
lean_dec_ref(v_xs_1242_);
v___x_1247_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1236_, v_xs_1240_, v_items_1246_);
lean_dec_ref(v_items_1246_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1247_);
lean_ctor_set(v___x_1244_, 0, v_ref_1239_);
v___x_1249_ = v___x_1244_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_ref_1239_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_dec_ref(v_xs_1240_);
lean_dec(v_ref_1239_);
lean_dec_ref(v___x_1236_);
return v___x_1241_;
}
}
case 5:
{
lean_object* v_ref_1253_; lean_object* v_xs_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v___x_1236_);
v_ref_1253_ = lean_ctor_get(v_val_1238_, 0);
v_xs_1254_ = lean_ctor_get(v_val_1238_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_val_1238_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1256_ = v_val_1238_;
v_isShared_1257_ = v_isSharedCheck_1273_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_xs_1254_);
lean_inc(v_ref_1253_);
lean_dec(v_val_1238_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1273_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; 
v___x_1258_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1235_);
if (lean_obj_tag(v___x_1258_) == 5)
{
lean_object* v_xs_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1267_; 
lean_del_object(v___x_1256_);
v_xs_1259_ = lean_ctor_get(v___x_1258_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v___x_1258_, 0);
lean_dec(v_unused_1268_);
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_xs_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = l_Array_append___redArg(v_xs_1254_, v_xs_1259_);
lean_dec_ref(v_xs_1259_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1263_);
lean_ctor_set(v___x_1261_, 0, v_ref_1253_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_ref_1253_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_array_push(v_xs_1254_, v___x_1258_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1269_);
v___x_1271_ = v___x_1256_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_ref_1253_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
default: 
{
lean_object* v___x_1274_; 
lean_dec(v_val_1238_);
lean_dec_ref(v___x_1236_);
v___x_1274_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1235_);
return v___x_1274_;
}
}
}
else
{
lean_object* v___x_1275_; 
lean_dec(v_v_x3f_1237_);
lean_dec_ref(v___x_1236_);
v___x_1275_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1235_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1276_, lean_object* v_k_1277_, lean_object* v_t_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1278_);
lean_inc(v_k_1277_);
v___x_1280_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1279_, v_k_1277_, v_t_1278_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_val_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_k_1277_);
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1316_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_val_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1316_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_items_1285_; lean_object* v_indices_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1315_; 
v_items_1285_ = lean_ctor_get(v_t_1278_, 0);
v_indices_1286_ = lean_ctor_get(v_t_1278_, 1);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_t_1278_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1288_ = v_t_1278_;
v_isShared_1289_ = v_isSharedCheck_1315_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_indices_1286_);
lean_inc(v_items_1285_);
lean_dec(v_t_1278_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1315_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = lean_array_get_size(v_items_1285_);
v___x_1291_ = lean_nat_dec_lt(v_val_1281_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1293_; 
lean_del_object(v___x_1283_);
lean_dec(v_val_1281_);
lean_dec_ref(v_newV_1276_);
if (v_isShared_1289_ == 0)
{
v___x_1293_ = v___x_1288_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_items_1285_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_indices_1286_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
else
{
lean_object* v_v_1295_; lean_object* v_fst_1296_; lean_object* v_snd_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1314_; 
v_v_1295_ = lean_array_fget(v_items_1285_, v_val_1281_);
v_fst_1296_ = lean_ctor_get(v_v_1295_, 0);
v_snd_1297_ = lean_ctor_get(v_v_1295_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_v_1295_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1299_ = v_v_1295_;
v_isShared_1300_ = v_isSharedCheck_1314_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_snd_1297_);
lean_inc(v_fst_1296_);
lean_dec(v_v_1295_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1314_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v_xs_x27_1302_; lean_object* v___x_1304_; 
v___x_1301_ = lean_box(0);
v_xs_x27_1302_ = lean_array_fset(v_items_1285_, v_val_1281_, v___x_1301_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v_snd_1297_);
v___x_1304_ = v___x_1283_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_snd_1297_);
v___x_1304_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1276_, v___x_1279_, v___x_1304_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v___x_1305_);
v___x_1307_ = v___x_1299_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_fst_1296_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1308_ = lean_array_fset(v_xs_x27_1302_, v_val_1281_, v___x_1307_);
lean_dec(v_val_1281_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1308_);
v___x_1310_ = v___x_1288_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_indices_1286_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
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
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec(v___x_1280_);
v___x_1317_ = lean_box(0);
v___x_1318_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1276_, v___x_1279_, v___x_1317_);
v___x_1319_ = l_Lake_Toml_RBDict_push___redArg(v___x_1279_, v_k_1277_, v___x_1318_, v_t_1278_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1320_, lean_object* v_head_1321_, lean_object* v_tail_1322_, lean_object* v_newV_1323_, lean_object* v___x_1324_, lean_object* v_v_x3f_1325_){
_start:
{
if (lean_obj_tag(v_v_x3f_1325_) == 1)
{
lean_object* v_val_1326_; 
v_val_1326_ = lean_ctor_get(v_v_x3f_1325_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v_v_x3f_1325_, 1);
switch(lean_obj_tag(v_val_1326_))
{
case 5:
{
lean_object* v_ref_1327_; lean_object* v_xs_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_ref_1327_ = lean_ctor_get(v_val_1326_, 0);
v_xs_1328_ = lean_ctor_get(v_val_1326_, 1);
v___x_1329_ = lean_array_get_size(v_xs_1328_);
v___x_1330_ = lean_unsigned_to_nat(1u);
v___x_1331_ = lean_nat_sub(v___x_1329_, v___x_1330_);
v___x_1332_ = lean_nat_dec_lt(v___x_1331_, v___x_1329_);
if (v___x_1332_ == 0)
{
lean_dec(v___x_1331_);
lean_dec_ref(v_newV_1323_);
lean_dec(v_tail_1322_);
lean_dec(v_head_1321_);
lean_dec(v_kRef_1320_);
return v_val_1326_;
}
else
{
lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1357_; 
lean_inc_ref(v_xs_1328_);
lean_inc(v_ref_1327_);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_val_1326_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; lean_object* v_unused_1359_; 
v_unused_1358_ = lean_ctor_get(v_val_1326_, 1);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_val_1326_, 0);
lean_dec(v_unused_1359_);
v___x_1334_ = v_val_1326_;
v_isShared_1335_ = v_isSharedCheck_1357_;
goto v_resetjp_1333_;
}
else
{
lean_dec(v_val_1326_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1357_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v_v_1336_; lean_object* v___x_1337_; lean_object* v_xs_x27_1338_; lean_object* v___y_1340_; 
v_v_1336_ = lean_array_fget(v_xs_1328_, v___x_1331_);
v___x_1337_ = lean_box(0);
v_xs_x27_1338_ = lean_array_fset(v_xs_1328_, v___x_1331_, v___x_1337_);
if (lean_obj_tag(v_v_1336_) == 6)
{
lean_object* v_ref_1345_; lean_object* v_xs_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1354_; 
v_ref_1345_ = lean_ctor_get(v_v_1336_, 0);
v_xs_1346_ = lean_ctor_get(v_v_1336_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_v_1336_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1348_ = v_v_1336_;
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_xs_1346_);
lean_inc(v_ref_1345_);
lean_dec(v_v_1336_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1346_, v_kRef_1320_, v_head_1321_, v_tail_1322_, v_newV_1323_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_ref_1345_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
v___y_1340_ = v___x_1352_;
goto v___jp_1339_;
}
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_v_1336_);
lean_dec_ref(v_newV_1323_);
lean_dec(v_tail_1322_);
lean_dec(v_head_1321_);
v___x_1355_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1324_);
v___x_1356_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_kRef_1320_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___y_1340_ = v___x_1356_;
goto v___jp_1339_;
}
v___jp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = lean_array_fset(v_xs_x27_1338_, v___x_1331_, v___y_1340_);
lean_dec(v___x_1331_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___x_1341_);
v___x_1343_ = v___x_1334_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_ref_1327_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1360_; lean_object* v_xs_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
v_ref_1360_ = lean_ctor_get(v_val_1326_, 0);
v_xs_1361_ = lean_ctor_get(v_val_1326_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_val_1326_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v_val_1326_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_xs_1361_);
lean_inc(v_ref_1360_);
lean_dec(v_val_1326_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1361_, v_kRef_1320_, v_head_1321_, v_tail_1322_, v_newV_1323_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_ref_1360_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
default: 
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v_val_1326_);
v___x_1370_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1324_);
lean_inc(v_kRef_1320_);
v___x_1371_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1370_, v_kRef_1320_, v_head_1321_, v_tail_1322_, v_newV_1323_);
v___x_1372_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_kRef_1320_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
return v___x_1372_;
}
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec(v_v_x3f_1325_);
v___x_1373_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1324_);
lean_inc(v_kRef_1320_);
v___x_1374_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1373_, v_kRef_1320_, v_head_1321_, v_tail_1322_, v_newV_1323_);
v___x_1375_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_kRef_1320_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1376_, lean_object* v_head_1377_, lean_object* v_tail_1378_, lean_object* v_newV_1379_, lean_object* v_k_1380_, lean_object* v_t_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1381_);
lean_inc(v_k_1380_);
v___x_1383_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1382_, v_k_1380_, v_t_1381_);
if (lean_obj_tag(v___x_1383_) == 1)
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_k_1380_);
v_val_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1419_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1419_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_items_1388_; lean_object* v_indices_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1418_; 
v_items_1388_ = lean_ctor_get(v_t_1381_, 0);
v_indices_1389_ = lean_ctor_get(v_t_1381_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_t_1381_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1391_ = v_t_1381_;
v_isShared_1392_ = v_isSharedCheck_1418_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_indices_1389_);
lean_inc(v_items_1388_);
lean_dec(v_t_1381_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1418_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = lean_array_get_size(v_items_1388_);
v___x_1394_ = lean_nat_dec_lt(v_val_1384_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1396_; 
lean_del_object(v___x_1386_);
lean_dec(v_val_1384_);
lean_dec_ref(v_newV_1379_);
lean_dec(v_tail_1378_);
lean_dec(v_head_1377_);
lean_dec(v_kRef_1376_);
if (v_isShared_1392_ == 0)
{
v___x_1396_ = v___x_1391_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_items_1388_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_indices_1389_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
else
{
lean_object* v_v_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1417_; 
v_v_1398_ = lean_array_fget(v_items_1388_, v_val_1384_);
v_fst_1399_ = lean_ctor_get(v_v_1398_, 0);
v_snd_1400_ = lean_ctor_get(v_v_1398_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_v_1398_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1402_ = v_v_1398_;
v_isShared_1403_ = v_isSharedCheck_1417_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_snd_1400_);
lean_inc(v_fst_1399_);
lean_dec(v_v_1398_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1417_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v_xs_x27_1405_; lean_object* v___x_1407_; 
v___x_1404_ = lean_box(0);
v_xs_x27_1405_ = lean_array_fset(v_items_1388_, v_val_1384_, v___x_1404_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v_snd_1400_);
v___x_1407_ = v___x_1386_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_snd_1400_);
v___x_1407_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1376_, v_head_1377_, v_tail_1378_, v_newV_1379_, v___x_1382_, v___x_1407_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1408_);
v___x_1410_ = v___x_1402_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_fst_1399_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_array_fset(v_xs_x27_1405_, v_val_1384_, v___x_1410_);
lean_dec(v_val_1384_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1411_);
v___x_1413_ = v___x_1391_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_indices_1389_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
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
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec(v___x_1383_);
v___x_1420_ = lean_box(0);
v___x_1421_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1376_, v_head_1377_, v_tail_1378_, v_newV_1379_, v___x_1382_, v___x_1420_);
v___x_1422_ = l_Lake_Toml_RBDict_push___redArg(v___x_1382_, v_k_1380_, v___x_1421_, v_t_1381_);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1423_, lean_object* v_kRef_1424_, lean_object* v_k_1425_, lean_object* v_ks_1426_, lean_object* v_newV_1427_){
_start:
{
if (lean_obj_tag(v_ks_1426_) == 0)
{
lean_object* v___x_1428_; 
lean_dec(v_kRef_1424_);
v___x_1428_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1427_, v_k_1425_, v_t_1423_);
return v___x_1428_;
}
else
{
lean_object* v_head_1429_; lean_object* v_tail_1430_; lean_object* v___x_1431_; 
v_head_1429_ = lean_ctor_get(v_ks_1426_, 0);
lean_inc(v_head_1429_);
v_tail_1430_ = lean_ctor_get(v_ks_1426_, 1);
lean_inc(v_tail_1430_);
lean_dec_ref_known(v_ks_1426_, 2);
v___x_1431_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1424_, v_head_1429_, v_tail_1430_, v_newV_1427_, v_k_1425_, v_t_1423_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1432_, lean_object* v_i_1433_, lean_object* v_bs_1434_){
_start:
{
size_t v_sz_boxed_1435_; size_t v_i_boxed_1436_; lean_object* v_res_1437_; 
v_sz_boxed_1435_ = lean_unbox_usize(v_sz_1432_);
lean_dec(v_sz_1432_);
v_i_boxed_1436_ = lean_unbox_usize(v_i_1433_);
lean_dec(v_i_1433_);
v_res_1437_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1435_, v_i_boxed_1436_, v_bs_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1438_, lean_object* v_as_1439_, lean_object* v_i_1440_, lean_object* v_stop_1441_, lean_object* v_b_1442_){
_start:
{
size_t v_i_boxed_1443_; size_t v_stop_boxed_1444_; lean_object* v_res_1445_; 
v_i_boxed_1443_ = lean_unbox_usize(v_i_1440_);
lean_dec(v_i_1440_);
v_stop_boxed_1444_ = lean_unbox_usize(v_stop_1441_);
lean_dec(v_stop_1441_);
v_res_1445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1438_, v_as_1439_, v_i_boxed_1443_, v_stop_boxed_1444_, v_b_1442_);
lean_dec_ref(v_as_1439_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0___boxed(lean_object* v_kRef_1446_, lean_object* v_head_1447_, lean_object* v_tail_1448_, lean_object* v_newV_1449_, lean_object* v___x_1450_, lean_object* v_v_x3f_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1446_, v_head_1447_, v_tail_1448_, v_newV_1449_, v___x_1450_, v_v_x3f_1451_);
lean_dec_ref(v___x_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1453_, size_t v_i_1454_, size_t v_stop_1455_, lean_object* v_b_1456_){
_start:
{
lean_object* v___y_1458_; uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_eq(v_i_1454_, v_stop_1455_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v_ref_1464_; lean_object* v_key_1465_; lean_object* v_val_1466_; lean_object* v___x_1467_; 
v___x_1463_ = lean_array_uget_borrowed(v_as_1453_, v_i_1454_);
v_ref_1464_ = lean_ctor_get(v___x_1463_, 0);
v_key_1465_ = lean_ctor_get(v___x_1463_, 1);
v_val_1466_ = lean_ctor_get(v___x_1463_, 2);
lean_inc(v_key_1465_);
v___x_1467_ = l_Lean_Name_components(v_key_1465_);
if (lean_obj_tag(v___x_1467_) == 0)
{
v___y_1458_ = v_b_1456_;
goto v___jp_1457_;
}
else
{
lean_object* v_head_1468_; lean_object* v_tail_1469_; lean_object* v___x_1470_; 
v_head_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_head_1468_);
v_tail_1469_ = lean_ctor_get(v___x_1467_, 1);
lean_inc(v_tail_1469_);
lean_dec_ref_known(v___x_1467_, 2);
lean_inc_ref(v_val_1466_);
lean_inc(v_ref_1464_);
v___x_1470_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1456_, v_ref_1464_, v_head_1468_, v_tail_1469_, v_val_1466_);
v___y_1458_ = v___x_1470_;
goto v___jp_1457_;
}
}
else
{
return v_b_1456_;
}
v___jp_1457_:
{
size_t v___x_1459_; size_t v___x_1460_; 
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_add(v_i_1454_, v___x_1459_);
v_i_1454_ = v___x_1460_;
v_b_1456_ = v___y_1458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1471_, lean_object* v_i_1472_, lean_object* v_stop_1473_, lean_object* v_b_1474_){
_start:
{
size_t v_i_boxed_1475_; size_t v_stop_boxed_1476_; lean_object* v_res_1477_; 
v_i_boxed_1475_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_stop_boxed_1476_ = lean_unbox_usize(v_stop_1473_);
lean_dec(v_stop_1473_);
v_res_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1471_, v_i_boxed_1475_, v_stop_boxed_1476_, v_b_1474_);
lean_dec_ref(v_as_1471_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1479_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_array_get_size(v_items_1478_);
v___x_1482_ = lean_nat_dec_lt(v___x_1480_, v___x_1481_);
if (v___x_1482_ == 0)
{
return v___x_1479_;
}
else
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_nat_dec_le(v___x_1481_, v___x_1481_);
if (v___x_1483_ == 0)
{
if (v___x_1482_ == 0)
{
return v___x_1479_;
}
else
{
size_t v___x_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = lean_usize_of_nat(v___x_1481_);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1478_, v___x_1484_, v___x_1485_, v___x_1479_);
return v___x_1486_;
}
}
else
{
size_t v___x_1487_; size_t v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = lean_usize_of_nat(v___x_1481_);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1478_, v___x_1487_, v___x_1488_, v___x_1479_);
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1490_);
lean_dec_ref(v_items_1490_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1494_);
lean_inc_ref(v_a_1493_);
v___x_1497_ = lean_apply_4(v_x_1492_, v___x_1496_, v_a_1493_, v_a_1494_, lean_box(0));
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1508_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_snd_1502_; lean_object* v_items_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v_snd_1502_ = lean_ctor_get(v_a_1498_, 1);
lean_inc(v_snd_1502_);
lean_dec(v_a_1498_);
v_items_1503_ = lean_ctor_get(v_snd_1502_, 5);
lean_inc_ref(v_items_1503_);
lean_dec(v_snd_1502_);
v___x_1504_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1503_);
lean_dec_ref(v_items_1503_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1504_);
v___x_1506_ = v___x_1500_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_a_1509_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1497_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1497_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1517_, v_a_1518_, v_a_1519_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1530_, uint8_t v___y_1531_, lean_object* v_x_1532_){
_start:
{
if (lean_obj_tag(v_x_1532_) == 1)
{
lean_object* v_pre_1533_; 
v_pre_1533_ = lean_ctor_get(v_x_1532_, 0);
switch(lean_obj_tag(v_pre_1533_))
{
case 1:
{
lean_object* v_pre_1534_; 
v_pre_1534_ = lean_ctor_get(v_pre_1533_, 0);
switch(lean_obj_tag(v_pre_1534_))
{
case 0:
{
lean_object* v_str_1535_; lean_object* v_str_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_str_1535_ = lean_ctor_get(v_x_1532_, 1);
v_str_1536_ = lean_ctor_get(v_pre_1533_, 1);
v___x_1537_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1538_ = lean_string_dec_eq(v_str_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1540_ = lean_string_dec_eq(v_str_1536_, v___x_1539_);
if (v___x_1540_ == 0)
{
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1542_ = lean_string_dec_eq(v_str_1535_, v___x_1541_);
if (v___x_1542_ == 0)
{
return v___x_1542_;
}
else
{
return v_suppressElabErrors_1530_;
}
}
}
else
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1544_ = lean_string_dec_eq(v_str_1535_, v___x_1543_);
if (v___x_1544_ == 0)
{
return v___x_1544_;
}
else
{
return v_suppressElabErrors_1530_;
}
}
}
case 1:
{
lean_object* v_pre_1545_; 
v_pre_1545_ = lean_ctor_get(v_pre_1534_, 0);
if (lean_obj_tag(v_pre_1545_) == 0)
{
lean_object* v_str_1546_; lean_object* v_str_1547_; lean_object* v_str_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_str_1546_ = lean_ctor_get(v_x_1532_, 1);
v_str_1547_ = lean_ctor_get(v_pre_1533_, 1);
v_str_1548_ = lean_ctor_get(v_pre_1534_, 1);
v___x_1549_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1550_ = lean_string_dec_eq(v_str_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1552_ = lean_string_dec_eq(v_str_1547_, v___x_1551_);
if (v___x_1552_ == 0)
{
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1554_ = lean_string_dec_eq(v_str_1546_, v___x_1553_);
if (v___x_1554_ == 0)
{
return v___x_1554_;
}
else
{
return v_suppressElabErrors_1530_;
}
}
}
}
else
{
return v___y_1531_;
}
}
default: 
{
return v___y_1531_;
}
}
}
case 0:
{
lean_object* v_str_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_str_1555_ = lean_ctor_get(v_x_1532_, 1);
v___x_1556_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1557_ = lean_string_dec_eq(v_str_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
return v___x_1557_;
}
else
{
return v_suppressElabErrors_1530_;
}
}
default: 
{
return v___y_1531_;
}
}
}
else
{
return v___y_1531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1558_, lean_object* v___y_1559_, lean_object* v_x_1560_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1561_; uint8_t v___y_10628__boxed_1562_; uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_suppressElabErrors_boxed_1561_ = lean_unbox(v_suppressElabErrors_1558_);
v___y_10628__boxed_1562_ = lean_unbox(v___y_1559_);
v_res_1563_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1561_, v___y_10628__boxed_1562_, v_x_1560_);
lean_dec(v_x_1560_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1565_, lean_object* v_opt_1566_){
_start:
{
lean_object* v_name_1567_; lean_object* v_defValue_1568_; lean_object* v_map_1569_; lean_object* v___x_1570_; 
v_name_1567_ = lean_ctor_get(v_opt_1566_, 0);
v_defValue_1568_ = lean_ctor_get(v_opt_1566_, 1);
v_map_1569_ = lean_ctor_get(v_opts_1565_, 0);
v___x_1570_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1569_, v_name_1567_);
if (lean_obj_tag(v___x_1570_) == 0)
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_unbox(v_defValue_1568_);
return v___x_1571_;
}
else
{
lean_object* v_val_1572_; 
v_val_1572_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v___x_1570_, 1);
if (lean_obj_tag(v_val_1572_) == 1)
{
uint8_t v_v_1573_; 
v_v_1573_ = lean_ctor_get_uint8(v_val_1572_, 0);
lean_dec_ref_known(v_val_1572_, 0);
return v_v_1573_;
}
else
{
uint8_t v___x_1574_; 
lean_dec(v_val_1572_);
v___x_1574_ = lean_unbox(v_defValue_1568_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1575_, lean_object* v_opt_1576_){
_start:
{
uint8_t v_res_1577_; lean_object* v_r_1578_; 
v_res_1577_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1575_, v_opt_1576_);
lean_dec_ref(v_opt_1576_);
lean_dec_ref(v_opts_1575_);
v_r_1578_ = lean_box(v_res_1577_);
return v_r_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1580_, lean_object* v_msgData_1581_, uint8_t v_severity_1582_, uint8_t v_isSilent_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_a_1589_; uint8_t v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; uint8_t v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1628_; uint8_t v___y_1629_; lean_object* v___y_1630_; uint8_t v___y_1631_; uint8_t v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1653_; lean_object* v___y_1654_; uint8_t v___y_1655_; uint8_t v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1663_; uint8_t v___y_1664_; lean_object* v___y_1665_; uint8_t v___y_1666_; lean_object* v___y_1667_; uint8_t v___y_1668_; uint8_t v___x_1673_; lean_object* v___y_1675_; lean_object* v___y_1676_; uint8_t v___y_1677_; lean_object* v___y_1678_; uint8_t v___y_1679_; uint8_t v___y_1680_; uint8_t v___y_1682_; uint8_t v___x_1697_; 
v___x_1673_ = 2;
v___x_1697_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1582_, v___x_1673_);
if (v___x_1697_ == 0)
{
v___y_1682_ = v___x_1697_;
goto v___jp_1681_;
}
else
{
uint8_t v___x_1698_; 
lean_inc_ref(v_msgData_1581_);
v___x_1698_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1581_);
v___y_1682_ = v___x_1698_;
goto v___jp_1681_;
}
v___jp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_a_1589_);
lean_ctor_set(v___x_1590_, 1, v___y_1584_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
v___jp_1592_:
{
lean_object* v___x_1602_; lean_object* v_currNamespace_1603_; lean_object* v_openDecls_1604_; lean_object* v_env_1605_; lean_object* v_nextMacroScope_1606_; lean_object* v_ngen_1607_; lean_object* v_auxDeclNGen_1608_; lean_object* v_traceState_1609_; lean_object* v_cache_1610_; lean_object* v_messages_1611_; lean_object* v_infoState_1612_; lean_object* v_snapshotTasks_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1626_; 
v___x_1602_ = lean_st_ref_take(v___y_1601_);
v_currNamespace_1603_ = lean_ctor_get(v___y_1600_, 5);
v_openDecls_1604_ = lean_ctor_get(v___y_1600_, 6);
v_env_1605_ = lean_ctor_get(v___x_1602_, 0);
v_nextMacroScope_1606_ = lean_ctor_get(v___x_1602_, 1);
v_ngen_1607_ = lean_ctor_get(v___x_1602_, 2);
v_auxDeclNGen_1608_ = lean_ctor_get(v___x_1602_, 3);
v_traceState_1609_ = lean_ctor_get(v___x_1602_, 4);
v_cache_1610_ = lean_ctor_get(v___x_1602_, 5);
v_messages_1611_ = lean_ctor_get(v___x_1602_, 6);
v_infoState_1612_ = lean_ctor_get(v___x_1602_, 7);
v_snapshotTasks_1613_ = lean_ctor_get(v___x_1602_, 8);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1615_ = v___x_1602_;
v_isShared_1616_ = v_isSharedCheck_1626_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_snapshotTasks_1613_);
lean_inc(v_infoState_1612_);
lean_inc(v_messages_1611_);
lean_inc(v_cache_1610_);
lean_inc(v_traceState_1609_);
lean_inc(v_auxDeclNGen_1608_);
lean_inc(v_ngen_1607_);
lean_inc(v_nextMacroScope_1606_);
lean_inc(v_env_1605_);
lean_dec(v___x_1602_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1626_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_inc(v_openDecls_1604_);
lean_inc(v_currNamespace_1603_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_currNamespace_1603_);
lean_ctor_set(v___x_1617_, 1, v_openDecls_1604_);
v___x_1618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___y_1594_);
lean_inc_ref(v___y_1599_);
lean_inc_ref(v___y_1595_);
v___x_1619_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1619_, 0, v___y_1595_);
lean_ctor_set(v___x_1619_, 1, v___y_1596_);
lean_ctor_set(v___x_1619_, 2, v___y_1598_);
lean_ctor_set(v___x_1619_, 3, v___y_1599_);
lean_ctor_set(v___x_1619_, 4, v___x_1618_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*5, v___y_1593_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*5 + 1, v___y_1597_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*5 + 2, v_isSilent_1583_);
v___x_1620_ = l_Lean_MessageLog_add(v___x_1619_, v_messages_1611_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 6, v___x_1620_);
v___x_1622_ = v___x_1615_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_env_1605_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_nextMacroScope_1606_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_ngen_1607_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_auxDeclNGen_1608_);
lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_traceState_1609_);
lean_ctor_set(v_reuseFailAlloc_1625_, 5, v_cache_1610_);
lean_ctor_set(v_reuseFailAlloc_1625_, 6, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1625_, 7, v_infoState_1612_);
lean_ctor_set(v_reuseFailAlloc_1625_, 8, v_snapshotTasks_1613_);
v___x_1622_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_st_ref_put(v___y_1601_, v___x_1622_);
v___x_1624_ = lean_box(0);
v_a_1589_ = v___x_1624_;
goto v___jp_1588_;
}
}
}
v___jp_1627_:
{
lean_object* v_fileName_1635_; lean_object* v_fileMap_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1651_; 
v_fileName_1635_ = lean_ctor_get(v___y_1633_, 0);
v_fileMap_1636_ = lean_ctor_get(v___y_1633_, 1);
v___x_1637_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1581_);
v___x_1638_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1637_, v___y_1585_, v___y_1586_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1651_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1651_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
lean_inc_ref_n(v_fileMap_1636_, 2);
v___x_1643_ = l_Lean_FileMap_toPosition(v_fileMap_1636_, v___y_1630_);
lean_dec(v___y_1630_);
v___x_1644_ = l_Lean_FileMap_toPosition(v_fileMap_1636_, v___y_1634_);
lean_dec(v___y_1634_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 1);
lean_ctor_set(v___x_1641_, 0, v___x_1644_);
v___x_1646_ = v___x_1641_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1632_ == 0)
{
lean_dec_ref(v___y_1628_);
v___y_1593_ = v___y_1629_;
v___y_1594_ = v_a_1639_;
v___y_1595_ = v_fileName_1635_;
v___y_1596_ = v___x_1643_;
v___y_1597_ = v___y_1631_;
v___y_1598_ = v___x_1646_;
v___y_1599_ = v___x_1647_;
v___y_1600_ = v___y_1585_;
v___y_1601_ = v___y_1586_;
goto v___jp_1592_;
}
else
{
uint8_t v___x_1648_; 
lean_inc(v_a_1639_);
v___x_1648_ = l_Lean_MessageData_hasTag(v___y_1628_, v_a_1639_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
lean_dec_ref(v___x_1646_);
lean_dec_ref(v___x_1643_);
lean_dec(v_a_1639_);
v___x_1649_ = lean_box(0);
v_a_1589_ = v___x_1649_;
goto v___jp_1588_;
}
else
{
v___y_1593_ = v___y_1629_;
v___y_1594_ = v_a_1639_;
v___y_1595_ = v_fileName_1635_;
v___y_1596_ = v___x_1643_;
v___y_1597_ = v___y_1631_;
v___y_1598_ = v___x_1646_;
v___y_1599_ = v___x_1647_;
v___y_1600_ = v___y_1585_;
v___y_1601_ = v___y_1586_;
goto v___jp_1592_;
}
}
}
}
}
v___jp_1652_:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_Syntax_getTailPos_x3f(v___y_1654_, v___y_1655_);
lean_dec(v___y_1654_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_inc(v___y_1659_);
v___y_1628_ = v___y_1653_;
v___y_1629_ = v___y_1655_;
v___y_1630_ = v___y_1659_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v___y_1659_;
goto v___jp_1627_;
}
else
{
lean_object* v_val_1661_; 
v_val_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_val_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___y_1628_ = v___y_1653_;
v___y_1629_ = v___y_1655_;
v___y_1630_ = v___y_1659_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v_val_1661_;
goto v___jp_1627_;
}
}
v___jp_1662_:
{
lean_object* v_ref_1669_; lean_object* v___x_1670_; 
v_ref_1669_ = l_Lean_replaceRef(v_ref_1580_, v___y_1665_);
v___x_1670_ = l_Lean_Syntax_getPos_x3f(v_ref_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_unsigned_to_nat(0u);
v___y_1653_ = v___y_1663_;
v___y_1654_ = v_ref_1669_;
v___y_1655_ = v___y_1664_;
v___y_1656_ = v___y_1668_;
v___y_1657_ = v___y_1666_;
v___y_1658_ = v___y_1667_;
v___y_1659_ = v___x_1671_;
goto v___jp_1652_;
}
else
{
lean_object* v_val_1672_; 
v_val_1672_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_val_1672_);
lean_dec_ref_known(v___x_1670_, 1);
v___y_1653_ = v___y_1663_;
v___y_1654_ = v_ref_1669_;
v___y_1655_ = v___y_1664_;
v___y_1656_ = v___y_1668_;
v___y_1657_ = v___y_1666_;
v___y_1658_ = v___y_1667_;
v___y_1659_ = v_val_1672_;
goto v___jp_1652_;
}
}
v___jp_1674_:
{
if (v___y_1680_ == 0)
{
v___y_1663_ = v___y_1676_;
v___y_1664_ = v___y_1679_;
v___y_1665_ = v___y_1675_;
v___y_1666_ = v___y_1677_;
v___y_1667_ = v___y_1678_;
v___y_1668_ = v_severity_1582_;
goto v___jp_1662_;
}
else
{
v___y_1663_ = v___y_1676_;
v___y_1664_ = v___y_1679_;
v___y_1665_ = v___y_1675_;
v___y_1666_ = v___y_1677_;
v___y_1667_ = v___y_1678_;
v___y_1668_ = v___x_1673_;
goto v___jp_1662_;
}
}
v___jp_1681_:
{
if (v___y_1682_ == 0)
{
lean_object* v_toCold_1683_; lean_object* v_options_1684_; lean_object* v_ref_1685_; uint8_t v_suppressElabErrors_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; uint8_t v___x_1690_; uint8_t v___x_1691_; 
v_toCold_1683_ = lean_ctor_get(v___y_1585_, 0);
v_options_1684_ = lean_ctor_get(v___y_1585_, 1);
v_ref_1685_ = lean_ctor_get(v___y_1585_, 4);
v_suppressElabErrors_1686_ = lean_ctor_get_uint8(v___y_1585_, sizeof(void*)*10 + 1);
v___x_1687_ = lean_box(v_suppressElabErrors_1686_);
v___x_1688_ = lean_box(v___y_1682_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1689_, 0, v___x_1687_);
lean_closure_set(v___f_1689_, 1, v___x_1688_);
v___x_1690_ = 1;
v___x_1691_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1582_, v___x_1690_);
if (v___x_1691_ == 0)
{
v___y_1675_ = v_ref_1685_;
v___y_1676_ = v___f_1689_;
v___y_1677_ = v_suppressElabErrors_1686_;
v___y_1678_ = v_toCold_1683_;
v___y_1679_ = v___y_1682_;
v___y_1680_ = v___x_1691_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1692_ = l_Lean_warningAsError;
v___x_1693_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_options_1684_, v___x_1692_);
v___y_1675_ = v_ref_1685_;
v___y_1676_ = v___f_1689_;
v___y_1677_ = v_suppressElabErrors_1686_;
v___y_1678_ = v_toCold_1683_;
v___y_1679_ = v___y_1682_;
v___y_1680_ = v___x_1693_;
goto v___jp_1674_;
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec_ref(v_msgData_1581_);
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___y_1584_);
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
return v___x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1699_, lean_object* v_msgData_1700_, lean_object* v_severity_1701_, lean_object* v_isSilent_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v_severity_boxed_1707_; uint8_t v_isSilent_boxed_1708_; lean_object* v_res_1709_; 
v_severity_boxed_1707_ = lean_unbox(v_severity_1701_);
v_isSilent_boxed_1708_ = lean_unbox(v_isSilent_1702_);
v_res_1709_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1699_, v_msgData_1700_, v_severity_boxed_1707_, v_isSilent_boxed_1708_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v_ref_1699_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1710_, lean_object* v_msgData_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v___x_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = 2;
v___x_1717_ = 0;
v___x_1718_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1710_, v_msgData_1711_, v___x_1716_, v___x_1717_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1719_, lean_object* v_msgData_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1719_, v_msgData_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v_ref_1719_);
return v_res_1725_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1729_ = l_Lean_MessageData_ofFormat(v___x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1730_, lean_object* v_as_1731_, size_t v_sz_1732_, size_t v_i_1733_, uint8_t v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_snd_1740_; lean_object* v_snd_1741_; lean_object* v___y_1747_; uint8_t v___y_1748_; lean_object* v_a_1765_; uint8_t v___x_1768_; 
v___x_1768_ = lean_usize_dec_lt(v_i_1733_, v_sz_1732_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_box(v_b_1734_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v___y_1735_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1773_; uint8_t v_recovering_1774_; 
v_a_1772_ = lean_array_uget_borrowed(v_as_1731_, v_i_1733_);
v___x_1773_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1772_);
v_recovering_1774_ = l_Lean_Syntax_isOfKind(v_a_1772_, v___x_1773_);
if (v_recovering_1774_ == 0)
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_a_1772_);
v___x_1776_ = l_Lean_Syntax_isOfKind(v_a_1772_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1772_);
v___x_1778_ = l_Lean_Syntax_isOfKind(v_a_1772_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1735_);
v___x_1780_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1772_, v___x_1779_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v_snd_1782_; lean_object* v___x_1783_; 
lean_dec_ref(v___y_1735_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v_snd_1782_ = lean_ctor_get(v_a_1781_, 1);
lean_inc(v_snd_1782_);
lean_dec(v_a_1781_);
v___x_1783_ = lean_box(v_b_1734_);
v_snd_1740_ = v___x_1783_;
v_snd_1741_ = v_snd_1782_;
goto v___jp_1739_;
}
else
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1780_, 1);
v_a_1765_ = v_a_1784_;
goto v___jp_1764_;
}
}
else
{
lean_object* v___x_1785_; 
lean_inc_ref(v___y_1735_);
lean_inc(v_a_1772_);
v___x_1785_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1772_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v_snd_1787_; lean_object* v___x_1788_; 
lean_dec_ref(v___y_1735_);
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v_snd_1787_ = lean_ctor_get(v_a_1786_, 1);
lean_inc(v_snd_1787_);
lean_dec(v_a_1786_);
v___x_1788_ = lean_box(v_recovering_1774_);
v_snd_1740_ = v___x_1788_;
v_snd_1741_ = v_snd_1787_;
goto v___jp_1739_;
}
else
{
lean_object* v_a_1789_; 
v_a_1789_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1785_, 1);
v_a_1765_ = v_a_1789_;
goto v___jp_1764_;
}
}
}
else
{
lean_object* v___x_1790_; 
lean_inc_ref(v___y_1735_);
lean_inc(v_a_1772_);
v___x_1790_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1772_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v_snd_1792_; lean_object* v___x_1793_; 
lean_dec_ref(v___y_1735_);
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v_snd_1792_ = lean_ctor_get(v_a_1791_, 1);
lean_inc(v_snd_1792_);
lean_dec(v_a_1791_);
v___x_1793_ = lean_box(v_recovering_1774_);
v_snd_1740_ = v___x_1793_;
v_snd_1741_ = v_snd_1792_;
goto v___jp_1739_;
}
else
{
lean_object* v_a_1794_; 
v_a_1794_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1790_, 1);
v_a_1765_ = v_a_1794_;
goto v___jp_1764_;
}
}
}
else
{
if (v_b_1734_ == 0)
{
lean_object* v___x_1795_; 
lean_inc_ref(v___y_1735_);
lean_inc(v_a_1772_);
v___x_1795_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1772_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v_snd_1797_; lean_object* v___x_1798_; 
lean_dec_ref(v___y_1735_);
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v_snd_1797_ = lean_ctor_get(v_a_1796_, 1);
lean_inc(v_snd_1797_);
lean_dec(v_a_1796_);
v___x_1798_ = lean_box(v_b_1734_);
v_snd_1740_ = v___x_1798_;
v_snd_1741_ = v_snd_1797_;
goto v___jp_1739_;
}
else
{
lean_object* v_a_1799_; 
v_a_1799_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1795_, 1);
v_a_1765_ = v_a_1799_;
goto v___jp_1764_;
}
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_box(v_b_1734_);
v_snd_1740_ = v___x_1800_;
v_snd_1741_ = v___y_1735_;
goto v___jp_1739_;
}
}
}
v___jp_1739_:
{
size_t v___x_1742_; size_t v___x_1743_; uint8_t v___x_1744_; 
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_add(v_i_1733_, v___x_1742_);
v___x_1744_ = lean_unbox(v_snd_1740_);
lean_dec(v_snd_1740_);
v_i_1733_ = v___x_1743_;
v_b_1734_ = v___x_1744_;
v___y_1735_ = v_snd_1741_;
goto _start;
}
v___jp_1746_:
{
if (v___y_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = l_Lean_Exception_getRef(v___y_1747_);
v___x_1750_ = l_Lean_Exception_toMessageData(v___y_1747_);
v___x_1751_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1749_, v___x_1750_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___x_1749_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v_snd_1753_; lean_object* v___x_1754_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v_snd_1753_ = lean_ctor_get(v_a_1752_, 1);
lean_inc(v_snd_1753_);
lean_dec(v_a_1752_);
v___x_1754_ = lean_box(v_recovering_1730_);
v_snd_1740_ = v___x_1754_;
v_snd_1741_ = v_snd_1753_;
goto v___jp_1739_;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
v_a_1755_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1751_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1751_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
lean_object* v___x_1763_; 
lean_dec_ref(v___y_1735_);
v___x_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___y_1747_);
return v___x_1763_;
}
}
v___jp_1764_:
{
uint8_t v___x_1766_; 
v___x_1766_ = l_Lean_Exception_isInterrupt(v_a_1765_);
if (v___x_1766_ == 0)
{
uint8_t v___x_1767_; 
lean_inc_ref(v_a_1765_);
v___x_1767_ = l_Lean_Exception_isRuntime(v_a_1765_);
v___y_1747_ = v_a_1765_;
v___y_1748_ = v___x_1767_;
goto v___jp_1746_;
}
else
{
v___y_1747_ = v_a_1765_;
v___y_1748_ = v___x_1766_;
goto v___jp_1746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1801_, lean_object* v_as_1802_, lean_object* v_sz_1803_, lean_object* v_i_1804_, lean_object* v_b_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
uint8_t v_recovering_boxed_1810_; size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; uint8_t v_b_boxed_1813_; lean_object* v_res_1814_; 
v_recovering_boxed_1810_ = lean_unbox(v_recovering_1801_);
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1803_);
lean_dec(v_sz_1803_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1804_);
lean_dec(v_i_1804_);
v_b_boxed_1813_ = lean_unbox(v_b_1805_);
v_res_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1810_, v_as_1802_, v_sz_boxed_1811_, v_i_boxed_1812_, v_b_boxed_1813_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_as_1802_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_ref_1819_; lean_object* v___x_1820_; lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1829_; 
v_ref_1819_ = lean_ctor_get(v___y_1816_, 4);
v___x_1820_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1815_, v___y_1816_, v___y_1817_);
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
lean_inc(v_ref_1819_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_ref_1819_);
lean_ctor_set(v___x_1825_, 1, v_a_1821_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set_tag(v___x_1823_, 1);
lean_ctor_set(v___x_1823_, 0, v___x_1825_);
v___x_1827_ = v___x_1823_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1835_, lean_object* v_msg_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_toCold_1840_; lean_object* v_options_1841_; lean_object* v_currRecDepth_1842_; lean_object* v_maxRecDepth_1843_; lean_object* v_ref_1844_; lean_object* v_currNamespace_1845_; lean_object* v_openDecls_1846_; lean_object* v_initHeartbeats_1847_; lean_object* v_maxHeartbeats_1848_; lean_object* v_currMacroScope_1849_; uint8_t v_diag_1850_; uint8_t v_suppressElabErrors_1851_; lean_object* v_ref_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_toCold_1840_ = lean_ctor_get(v___y_1837_, 0);
v_options_1841_ = lean_ctor_get(v___y_1837_, 1);
v_currRecDepth_1842_ = lean_ctor_get(v___y_1837_, 2);
v_maxRecDepth_1843_ = lean_ctor_get(v___y_1837_, 3);
v_ref_1844_ = lean_ctor_get(v___y_1837_, 4);
v_currNamespace_1845_ = lean_ctor_get(v___y_1837_, 5);
v_openDecls_1846_ = lean_ctor_get(v___y_1837_, 6);
v_initHeartbeats_1847_ = lean_ctor_get(v___y_1837_, 7);
v_maxHeartbeats_1848_ = lean_ctor_get(v___y_1837_, 8);
v_currMacroScope_1849_ = lean_ctor_get(v___y_1837_, 9);
v_diag_1850_ = lean_ctor_get_uint8(v___y_1837_, sizeof(void*)*10);
v_suppressElabErrors_1851_ = lean_ctor_get_uint8(v___y_1837_, sizeof(void*)*10 + 1);
v_ref_1852_ = l_Lean_replaceRef(v_ref_1835_, v_ref_1844_);
lean_inc(v_currMacroScope_1849_);
lean_inc(v_maxHeartbeats_1848_);
lean_inc(v_initHeartbeats_1847_);
lean_inc(v_openDecls_1846_);
lean_inc(v_currNamespace_1845_);
lean_inc(v_maxRecDepth_1843_);
lean_inc(v_currRecDepth_1842_);
lean_inc_ref(v_options_1841_);
lean_inc_ref(v_toCold_1840_);
v___x_1853_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1853_, 0, v_toCold_1840_);
lean_ctor_set(v___x_1853_, 1, v_options_1841_);
lean_ctor_set(v___x_1853_, 2, v_currRecDepth_1842_);
lean_ctor_set(v___x_1853_, 3, v_maxRecDepth_1843_);
lean_ctor_set(v___x_1853_, 4, v_ref_1852_);
lean_ctor_set(v___x_1853_, 5, v_currNamespace_1845_);
lean_ctor_set(v___x_1853_, 6, v_openDecls_1846_);
lean_ctor_set(v___x_1853_, 7, v_initHeartbeats_1847_);
lean_ctor_set(v___x_1853_, 8, v_maxHeartbeats_1848_);
lean_ctor_set(v___x_1853_, 9, v_currMacroScope_1849_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*10, v_diag_1850_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*10 + 1, v_suppressElabErrors_1851_);
v___x_1854_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1836_, v___x_1853_, v___y_1838_);
lean_dec_ref_known(v___x_1853_, 10);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1855_, lean_object* v_msg_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1855_, v_msg_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v_ref_1855_);
return v_res_1860_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1868_ = l_Lean_stringToMessageData(v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1873_);
v___x_1878_ = l_Lean_Syntax_isOfKind(v_x_1873_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1880_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1873_, v___x_1879_, v_a_1874_, v_a_1875_);
lean_dec(v_x_1873_);
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v_recovering_1884_; 
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = l_Lean_Syntax_getArg(v_x_1873_, v___x_1881_);
v___x_1883_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1884_ = l_Lean_Syntax_isOfKind(v___x_1882_, v___x_1883_);
if (v_recovering_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1886_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1873_, v___x_1885_, v_a_1874_, v_a_1875_);
lean_dec(v_x_1873_);
return v___x_1886_;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_xs_1889_; uint8_t v_recovering_1890_; lean_object* v___x_1891_; size_t v_sz_1892_; size_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = l_Lean_Syntax_getArg(v_x_1873_, v___x_1887_);
lean_dec(v_x_1873_);
v_xs_1889_ = l_Lean_Syntax_getArgs(v___x_1888_);
lean_dec(v___x_1888_);
v_recovering_1890_ = 0;
v___x_1891_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1889_);
lean_dec_ref(v_xs_1889_);
v_sz_1892_ = lean_array_size(v___x_1891_);
v___x_1893_ = ((size_t)0ULL);
v___x_1894_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1884_, v___x_1891_, v_sz_1892_, v___x_1893_, v_recovering_1890_, v___x_1894_, v_a_1874_, v_a_1875_);
lean_dec_ref(v___x_1891_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1906_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1906_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1906_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_snd_1900_; lean_object* v_items_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v_snd_1900_ = lean_ctor_get(v_a_1896_, 1);
lean_inc(v_snd_1900_);
lean_dec(v_a_1896_);
v_items_1901_ = lean_ctor_get(v_snd_1900_, 5);
lean_inc_ref(v_items_1901_);
lean_dec(v_snd_1900_);
v___x_1902_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1901_);
lean_dec_ref(v_items_1901_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1902_);
v___x_1904_ = v___x_1898_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1895_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1895_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lake_Toml_elabToml(v_x_1915_, v_a_1916_, v_a_1917_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1920_, lean_object* v_ref_1921_, lean_object* v_msg_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1921_, v_msg_1922_, v___y_1923_, v___y_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_ref_1928_, lean_object* v_msg_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1927_, v_ref_1928_, v_msg_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v_ref_1928_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1934_, lean_object* v_msg_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1935_, v___y_1936_, v___y_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1940_, lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1940_, v_msg_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1945_;
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
