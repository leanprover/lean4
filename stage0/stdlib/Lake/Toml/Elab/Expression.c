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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
v___x_130_ = lean_alloc_ctor(0, 10, 0);
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
uint8_t v___x_4084__boxed_412_; size_t v_i_boxed_413_; size_t v_stop_boxed_414_; lean_object* v_res_415_; 
v___x_4084__boxed_412_ = lean_unbox(v___x_407_);
v_i_boxed_413_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_stop_boxed_414_ = lean_unbox_usize(v_stop_410_);
lean_dec(v_stop_410_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_4084__boxed_412_, v_as_408_, v_i_boxed_413_, v_stop_boxed_414_, v_b_411_);
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
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_box(v___x_474_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_588_);
v___x_593_ = lean_nat_dec_le(v___x_589_, v___x_589_);
if (v___x_593_ == 0)
{
if (v___x_590_ == 0)
{
lean_dec_ref_known(v___x_592_, 2);
lean_dec_ref(v___x_587_);
v___y_480_ = v___x_588_;
goto v___jp_479_;
}
else
{
size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; lean_object* v_snd_597_; 
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_589_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_474_, v___x_587_, v___x_594_, v___x_595_, v___x_592_);
lean_dec_ref(v___x_587_);
v_snd_597_ = lean_ctor_get(v___x_596_, 1);
lean_inc(v_snd_597_);
lean_dec_ref(v___x_596_);
v___y_480_ = v_snd_597_;
goto v___jp_479_;
}
}
else
{
size_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; lean_object* v_snd_601_; 
v___x_598_ = ((size_t)0ULL);
v___x_599_ = lean_usize_of_nat(v___x_589_);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_474_, v___x_587_, v___x_598_, v___x_599_, v___x_592_);
lean_dec_ref(v___x_587_);
v_snd_601_ = lean_ctor_get(v___x_600_, 1);
lean_inc(v_snd_601_);
lean_dec_ref(v___x_600_);
v___y_480_ = v_snd_601_;
goto v___jp_479_;
}
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_602_, v_a_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
return v_res_607_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_610_ = l_Lean_stringToMessageData(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_611_, size_t v_i_612_, size_t v_stop_613_, lean_object* v_b_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_fst_620_; lean_object* v_snd_621_; uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_eq(v_i_612_, v_stop_613_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_array_uget_borrowed(v_as_611_, v_i_612_);
lean_inc(v___x_626_);
v___x_627_ = l_Lake_Toml_elabSimpleKey(v___x_626_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v_keyTys_629_; lean_object* v_arrKeyTys_630_; lean_object* v_arrParents_631_; lean_object* v_currArrKey_632_; lean_object* v_currKey_633_; lean_object* v_items_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v_keyTys_629_ = lean_ctor_get(v___y_615_, 0);
v_arrKeyTys_630_ = lean_ctor_get(v___y_615_, 1);
v_arrParents_631_ = lean_ctor_get(v___y_615_, 2);
v_currArrKey_632_ = lean_ctor_get(v___y_615_, 3);
v_currKey_633_ = lean_ctor_get(v___y_615_, 4);
v_items_634_ = lean_ctor_get(v___y_615_, 5);
v___x_635_ = l_Lean_Name_str___override(v_b_614_, v_a_628_);
v___x_636_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_629_, v___x_635_);
if (lean_obj_tag(v___x_636_) == 1)
{
lean_object* v_val_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_698_; 
v_val_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_698_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_698_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_val_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_698_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
uint8_t v___x_641_; 
v___x_641_ = lean_unbox(v_val_637_);
switch(v___x_641_)
{
case 2:
{
lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_666_; 
lean_inc_ref(v_items_634_);
lean_inc(v_currKey_633_);
lean_inc(v_arrParents_631_);
lean_inc(v_arrKeyTys_630_);
lean_del_object(v___x_639_);
lean_dec(v_val_637_);
v_isSharedCheck_666_ = !lean_is_exclusive(v___y_615_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; lean_object* v_unused_669_; lean_object* v_unused_670_; lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_667_ = lean_ctor_get(v___y_615_, 5);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v___y_615_, 4);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v___y_615_, 3);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v___y_615_, 2);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v___y_615_, 1);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v___y_615_, 0);
lean_dec(v_unused_672_);
v___x_643_ = v___y_615_;
v_isShared_644_ = v_isSharedCheck_666_;
goto v_resetjp_642_;
}
else
{
lean_dec(v___y_615_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_666_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_630_, v___x_635_);
if (lean_obj_tag(v___x_645_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_648_; 
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_645_, 1);
lean_inc(v___x_635_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 3, v___x_635_);
lean_ctor_set(v___x_643_, 0, v_val_646_);
v___x_648_ = v___x_643_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_val_646_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_arrKeyTys_630_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_arrParents_631_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v_currKey_633_);
lean_ctor_set(v_reuseFailAlloc_649_, 5, v_items_634_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
v_fst_620_ = v___x_635_;
v_snd_621_ = v___x_648_;
goto v___jp_619_;
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v___x_645_);
lean_del_object(v___x_643_);
lean_dec_ref(v_items_634_);
lean_dec(v_currKey_633_);
lean_dec(v_arrParents_631_);
lean_dec(v_arrKeyTys_630_);
v___x_650_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_635_);
v___x_651_ = l_Lean_MessageData_ofName(v___x_635_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_654_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v_snd_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v_snd_657_ = lean_ctor_get(v_a_656_, 1);
lean_inc(v_snd_657_);
lean_dec(v_a_656_);
v_fst_620_ = v___x_635_;
v_snd_621_ = v_snd_657_;
goto v___jp_619_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v___x_635_);
v_a_658_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_655_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_655_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
}
case 1:
{
lean_del_object(v___x_639_);
lean_dec(v_val_637_);
v_fst_620_ = v___x_635_;
v_snd_621_ = v___y_615_;
goto v___jp_619_;
}
case 4:
{
lean_del_object(v___x_639_);
lean_dec(v_val_637_);
v_fst_620_ = v___x_635_;
v_snd_621_ = v___y_615_;
goto v___jp_619_;
}
case 3:
{
lean_del_object(v___x_639_);
lean_dec(v_val_637_);
v_fst_620_ = v___x_635_;
v_snd_621_ = v___y_615_;
goto v___jp_619_;
}
default: 
{
lean_object* v___x_673_; uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_673_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_674_ = lean_unbox(v_val_637_);
lean_dec(v_val_637_);
v___x_675_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_674_);
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 3);
lean_ctor_set(v___x_639_, 0, v___x_675_);
v___x_677_ = v___x_639_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_697_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_678_ = l_Lean_MessageData_ofFormat(v___x_677_);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_673_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_inc(v___x_635_);
v___x_682_ = l_Lean_MessageData_ofName(v___x_635_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_626_, v___x_685_, v___y_615_, v___y_616_, v___y_617_);
lean_dec_ref(v___y_615_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v_snd_688_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v_snd_688_ = lean_ctor_get(v_a_687_, 1);
lean_inc(v_snd_688_);
lean_dec(v_a_687_);
v_fst_620_ = v___x_635_;
v_snd_621_ = v_snd_688_;
goto v___jp_619_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v___x_635_);
v_a_689_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_686_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
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
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_708_; 
lean_inc_ref(v_items_634_);
lean_inc(v_currKey_633_);
lean_inc(v_currArrKey_632_);
lean_inc(v_arrParents_631_);
lean_inc(v_arrKeyTys_630_);
lean_inc(v_keyTys_629_);
lean_dec(v___x_636_);
v_isSharedCheck_708_ = !lean_is_exclusive(v___y_615_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; lean_object* v_unused_713_; lean_object* v_unused_714_; 
v_unused_709_ = lean_ctor_get(v___y_615_, 5);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v___y_615_, 4);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v___y_615_, 3);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v___y_615_, 2);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v___y_615_, 1);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v___y_615_, 0);
lean_dec(v_unused_714_);
v___x_700_ = v___y_615_;
v_isShared_701_ = v_isSharedCheck_708_;
goto v_resetjp_699_;
}
else
{
lean_dec(v___y_615_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_708_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_702_ = 4;
v___x_703_ = lean_box(v___x_702_);
lean_inc(v___x_635_);
v___x_704_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_635_, v___x_703_, v_keyTys_629_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_704_);
v___x_706_ = v___x_700_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_arrKeyTys_630_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_arrParents_631_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_currArrKey_632_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_currKey_633_);
lean_ctor_set(v_reuseFailAlloc_707_, 5, v_items_634_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v_fst_620_ = v___x_635_;
v_snd_621_ = v___x_706_;
goto v___jp_619_;
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v___y_615_);
lean_dec(v_b_614_);
v_a_715_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_627_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_627_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v_b_614_);
lean_ctor_set(v___x_723_, 1, v___y_615_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
v___jp_619_:
{
size_t v___x_622_; size_t v___x_623_; 
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_612_, v___x_622_);
v_i_612_ = v___x_623_;
v_b_614_ = v_fst_620_;
v___y_615_ = v_snd_621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_725_, lean_object* v_i_726_, lean_object* v_stop_727_, lean_object* v_b_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
size_t v_i_boxed_733_; size_t v_stop_boxed_734_; lean_object* v_res_735_; 
v_i_boxed_733_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_stop_boxed_734_ = lean_unbox_usize(v_stop_727_);
lean_dec(v_stop_727_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_725_, v_i_boxed_733_, v_stop_boxed_734_, v_b_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec_ref(v_as_725_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_736_, lean_object* v_k_737_){
_start:
{
if (lean_obj_tag(v_t_736_) == 0)
{
lean_object* v_k_738_; lean_object* v_v_739_; lean_object* v_l_740_; lean_object* v_r_741_; uint8_t v___x_742_; 
v_k_738_ = lean_ctor_get(v_t_736_, 1);
v_v_739_ = lean_ctor_get(v_t_736_, 2);
v_l_740_ = lean_ctor_get(v_t_736_, 3);
v_r_741_ = lean_ctor_get(v_t_736_, 4);
v___x_742_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_737_, v_k_738_);
switch(v___x_742_)
{
case 0:
{
v_t_736_ = v_l_740_;
goto _start;
}
case 1:
{
lean_object* v___x_744_; 
lean_inc(v_v_739_);
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v_v_739_);
return v___x_744_;
}
default: 
{
v_t_736_ = v_r_741_;
goto _start;
}
}
}
else
{
lean_object* v___x_746_; 
v___x_746_ = lean_box(0);
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_747_, lean_object* v_k_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_747_, v_k_748_);
lean_dec(v_k_748_);
lean_dec(v_t_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_keyTys_755_; lean_object* v_arrKeyTys_756_; lean_object* v_arrParents_757_; lean_object* v_currArrKey_758_; lean_object* v_currKey_759_; lean_object* v_items_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_788_; 
v_keyTys_755_ = lean_ctor_get(v_a_751_, 0);
v_arrKeyTys_756_ = lean_ctor_get(v_a_751_, 1);
v_arrParents_757_ = lean_ctor_get(v_a_751_, 2);
v_currArrKey_758_ = lean_ctor_get(v_a_751_, 3);
v_currKey_759_ = lean_ctor_get(v_a_751_, 4);
v_items_760_ = lean_ctor_get(v_a_751_, 5);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_751_);
if (v_isSharedCheck_788_ == 0)
{
v___x_762_ = v_a_751_;
v_isShared_763_ = v_isSharedCheck_788_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_items_760_);
lean_inc(v_currKey_759_);
lean_inc(v_currArrKey_758_);
lean_inc(v_arrParents_757_);
lean_inc(v_arrKeyTys_756_);
lean_inc(v_keyTys_755_);
lean_dec(v_a_751_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_788_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_arrKeyTys_764_; lean_object* v___x_765_; lean_object* v___y_767_; lean_object* v___x_785_; 
v_arrKeyTys_764_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_758_, v_keyTys_755_, v_arrKeyTys_756_);
v___x_765_ = lean_box(0);
v___x_785_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_764_, v___x_765_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_786_; 
v___x_786_ = lean_box(1);
v___y_767_ = v___x_786_;
goto v___jp_766_;
}
else
{
lean_object* v_val_787_; 
v_val_787_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v___x_785_, 1);
v___y_767_ = v_val_787_;
goto v___jp_766_;
}
v___jp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 3, v___x_765_);
lean_ctor_set(v___x_762_, 1, v_arrKeyTys_764_);
lean_ctor_set(v___x_762_, 0, v___y_767_);
v___x_769_ = v___x_762_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___y_767_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_arrKeyTys_764_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_arrParents_757_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_currKey_759_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v_items_760_);
v___x_769_ = v_reuseFailAlloc_784_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_array_get_size(v_ks_750_);
v___x_772_ = lean_nat_dec_lt(v___x_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_765_);
lean_ctor_set(v___x_773_, 1, v___x_769_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = lean_nat_dec_le(v___x_771_, v___x_771_);
if (v___x_775_ == 0)
{
if (v___x_772_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_765_);
lean_ctor_set(v___x_776_, 1, v___x_769_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
else
{
size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
v___x_778_ = ((size_t)0ULL);
v___x_779_ = lean_usize_of_nat(v___x_771_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_750_, v___x_778_, v___x_779_, v___x_765_, v___x_769_, v_a_752_, v_a_753_);
return v___x_780_;
}
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_of_nat(v___x_771_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_750_, v___x_781_, v___x_782_, v___x_765_, v___x_769_, v_a_752_, v_a_753_);
return v___x_783_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec_ref(v_ks_789_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_795_, lean_object* v_t_796_, lean_object* v_k_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_796_, v_k_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_799_, lean_object* v_t_800_, lean_object* v_k_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_799_, v_t_800_, v_k_801_);
lean_dec(v_k_801_);
lean_dec(v_t_800_);
return v_res_802_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
v___x_805_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v___y_820_; lean_object* v_keyTys_821_; lean_object* v_arrKeyTys_822_; lean_object* v_arrParents_823_; lean_object* v_currArrKey_824_; lean_object* v_items_825_; lean_object* v_fileName_837_; lean_object* v_fileMap_838_; lean_object* v_options_839_; lean_object* v_currRecDepth_840_; lean_object* v_maxRecDepth_841_; lean_object* v_ref_842_; lean_object* v_currNamespace_843_; lean_object* v_openDecls_844_; lean_object* v_initHeartbeats_845_; lean_object* v_maxHeartbeats_846_; lean_object* v_quotContext_847_; lean_object* v_currMacroScope_848_; uint8_t v_diag_849_; lean_object* v_cancelTk_x3f_850_; uint8_t v_suppressElabErrors_851_; lean_object* v_inheritedTraceOptions_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v_ref_855_; lean_object* v___x_856_; 
v_fileName_837_ = lean_ctor_get(v_a_816_, 0);
v_fileMap_838_ = lean_ctor_get(v_a_816_, 1);
v_options_839_ = lean_ctor_get(v_a_816_, 2);
v_currRecDepth_840_ = lean_ctor_get(v_a_816_, 3);
v_maxRecDepth_841_ = lean_ctor_get(v_a_816_, 4);
v_ref_842_ = lean_ctor_get(v_a_816_, 5);
v_currNamespace_843_ = lean_ctor_get(v_a_816_, 6);
v_openDecls_844_ = lean_ctor_get(v_a_816_, 7);
v_initHeartbeats_845_ = lean_ctor_get(v_a_816_, 8);
v_maxHeartbeats_846_ = lean_ctor_get(v_a_816_, 9);
v_quotContext_847_ = lean_ctor_get(v_a_816_, 10);
v_currMacroScope_848_ = lean_ctor_get(v_a_816_, 11);
v_diag_849_ = lean_ctor_get_uint8(v_a_816_, sizeof(void*)*14);
v_cancelTk_x3f_850_ = lean_ctor_get(v_a_816_, 12);
v_suppressElabErrors_851_ = lean_ctor_get_uint8(v_a_816_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_852_ = lean_ctor_get(v_a_816_, 13);
v___x_853_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_814_);
v___x_854_ = l_Lean_Syntax_isOfKind(v_x_814_, v___x_853_);
v_ref_855_ = l_Lean_replaceRef(v_x_814_, v_ref_842_);
lean_inc_ref(v_inheritedTraceOptions_852_);
lean_inc(v_cancelTk_x3f_850_);
lean_inc(v_currMacroScope_848_);
lean_inc(v_quotContext_847_);
lean_inc(v_maxHeartbeats_846_);
lean_inc(v_initHeartbeats_845_);
lean_inc(v_openDecls_844_);
lean_inc(v_currNamespace_843_);
lean_inc(v_maxRecDepth_841_);
lean_inc(v_currRecDepth_840_);
lean_inc_ref(v_options_839_);
lean_inc_ref(v_fileMap_838_);
lean_inc_ref(v_fileName_837_);
v___x_856_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_856_, 0, v_fileName_837_);
lean_ctor_set(v___x_856_, 1, v_fileMap_838_);
lean_ctor_set(v___x_856_, 2, v_options_839_);
lean_ctor_set(v___x_856_, 3, v_currRecDepth_840_);
lean_ctor_set(v___x_856_, 4, v_maxRecDepth_841_);
lean_ctor_set(v___x_856_, 5, v_ref_855_);
lean_ctor_set(v___x_856_, 6, v_currNamespace_843_);
lean_ctor_set(v___x_856_, 7, v_openDecls_844_);
lean_ctor_set(v___x_856_, 8, v_initHeartbeats_845_);
lean_ctor_set(v___x_856_, 9, v_maxHeartbeats_846_);
lean_ctor_set(v___x_856_, 10, v_quotContext_847_);
lean_ctor_set(v___x_856_, 11, v_currMacroScope_848_);
lean_ctor_set(v___x_856_, 12, v_cancelTk_x3f_850_);
lean_ctor_set(v___x_856_, 13, v_inheritedTraceOptions_852_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*14, v_diag_849_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*14 + 1, v_suppressElabErrors_851_);
if (v___x_854_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5);
v___x_858_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_814_, v___x_857_, v_a_815_, v___x_856_, v_a_817_);
lean_dec_ref_known(v___x_856_, 14);
lean_dec_ref(v_a_815_);
lean_dec(v_x_814_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___y_862_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_859_ = lean_unsigned_to_nat(1u);
v___x_860_ = l_Lean_Syntax_getArg(v_x_814_, v___x_859_);
v___x_930_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_860_);
v___x_931_ = l_Lean_Syntax_isOfKind(v___x_860_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v_x_814_);
v___x_932_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_933_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_860_, v___x_932_, v_a_815_, v___x_856_, v_a_817_);
lean_dec_ref_known(v___x_856_, 14);
lean_dec_ref(v_a_815_);
lean_dec(v___x_860_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = l_Lean_Syntax_getArg(v___x_860_, v___x_934_);
v___x_936_ = l_Lean_Syntax_getArgs(v___x_935_);
lean_dec(v___x_935_);
v___x_937_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_938_ = lean_array_get_size(v___x_936_);
v___x_939_ = lean_nat_dec_lt(v___x_934_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec_ref(v___x_936_);
v___y_862_ = v___x_937_;
goto v___jp_861_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = lean_box(v___x_931_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_937_);
v___x_942_ = lean_nat_dec_le(v___x_938_, v___x_938_);
if (v___x_942_ == 0)
{
if (v___x_939_ == 0)
{
lean_dec_ref_known(v___x_941_, 2);
lean_dec_ref(v___x_936_);
v___y_862_ = v___x_937_;
goto v___jp_861_;
}
else
{
size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; lean_object* v_snd_946_; 
v___x_943_ = ((size_t)0ULL);
v___x_944_ = lean_usize_of_nat(v___x_938_);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_931_, v___x_936_, v___x_943_, v___x_944_, v___x_941_);
lean_dec_ref(v___x_936_);
v_snd_946_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_snd_946_);
lean_dec_ref(v___x_945_);
v___y_862_ = v_snd_946_;
goto v___jp_861_;
}
}
else
{
size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; lean_object* v_snd_950_; 
v___x_947_ = ((size_t)0ULL);
v___x_948_ = lean_usize_of_nat(v___x_938_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_931_, v___x_936_, v___x_947_, v___x_948_, v___x_941_);
lean_dec_ref(v___x_936_);
v_snd_950_ = lean_ctor_get(v___x_949_, 1);
lean_inc(v_snd_950_);
lean_dec_ref(v___x_949_);
v___y_862_ = v_snd_950_;
goto v___jp_861_;
}
}
}
v___jp_861_:
{
size_t v_sz_863_; size_t v___x_864_; lean_object* v___x_865_; 
v_sz_863_ = lean_array_size(v___y_862_);
v___x_864_ = ((size_t)0ULL);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_863_, v___x_864_, v___y_862_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v_x_814_);
v___x_866_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_867_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_860_, v___x_866_, v_a_815_, v___x_856_, v_a_817_);
lean_dec_ref_known(v___x_856_, 14);
lean_dec_ref(v_a_815_);
lean_dec(v___x_860_);
return v___x_867_;
}
else
{
lean_object* v_val_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v_tailKey_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec(v___x_860_);
v_val_868_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v___x_865_, 1);
v___x_869_ = lean_box(0);
v___x_870_ = lean_array_get_size(v_val_868_);
v___x_871_ = lean_nat_sub(v___x_870_, v___x_859_);
v_tailKey_872_ = lean_array_get(v___x_869_, v_val_868_, v___x_871_);
lean_dec(v___x_871_);
v___x_873_ = lean_array_pop(v_val_868_);
v___x_874_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_873_, v_a_815_, v___x_856_, v_a_817_);
lean_dec_ref(v___x_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v_fst_876_; lean_object* v_snd_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_921_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v_fst_876_ = lean_ctor_get(v_a_875_, 0);
v_snd_877_ = lean_ctor_get(v_a_875_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_875_);
if (v_isSharedCheck_921_ == 0)
{
v___x_879_ = v_a_875_;
v_isShared_880_ = v_isSharedCheck_921_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_snd_877_);
lean_inc(v_fst_876_);
lean_dec(v_a_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_921_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; 
lean_inc(v_tailKey_872_);
v___x_881_ = l_Lake_Toml_elabSimpleKey(v_tailKey_872_, v___x_856_, v_a_817_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v_keyTys_883_; lean_object* v_arrKeyTys_884_; lean_object* v_arrParents_885_; lean_object* v_currArrKey_886_; lean_object* v_items_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v_keyTys_883_ = lean_ctor_get(v_snd_877_, 0);
v_arrKeyTys_884_ = lean_ctor_get(v_snd_877_, 1);
v_arrParents_885_ = lean_ctor_get(v_snd_877_, 2);
v_currArrKey_886_ = lean_ctor_get(v_snd_877_, 3);
v_items_887_ = lean_ctor_get(v_snd_877_, 5);
v___x_888_ = l_Lean_Name_str___override(v_fst_876_, v_a_882_);
v___x_889_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_883_, v___x_888_);
if (lean_obj_tag(v___x_889_) == 1)
{
lean_object* v_val_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_912_; 
v_val_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_912_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_912_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_val_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_912_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = lean_unbox(v_val_890_);
if (v___x_894_ == 4)
{
lean_inc_ref(v_items_887_);
lean_inc(v_currArrKey_886_);
lean_inc(v_arrParents_885_);
lean_inc(v_arrKeyTys_884_);
lean_inc(v_keyTys_883_);
lean_del_object(v___x_892_);
lean_dec(v_val_890_);
lean_del_object(v___x_879_);
lean_dec(v_snd_877_);
lean_dec(v_tailKey_872_);
lean_dec_ref_known(v___x_856_, 14);
v___y_820_ = v___x_888_;
v_keyTys_821_ = v_keyTys_883_;
v_arrKeyTys_822_ = v_arrKeyTys_884_;
v_arrParents_823_ = v_arrParents_885_;
v_currArrKey_824_ = v_currArrKey_886_;
v_items_825_ = v_items_887_;
goto v___jp_819_;
}
else
{
lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec(v_x_814_);
v___x_895_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_896_ = lean_unbox(v_val_890_);
lean_dec(v_val_890_);
v___x_897_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_896_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 3);
lean_ctor_set(v___x_892_, 0, v___x_897_);
v___x_899_ = v___x_892_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_911_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = l_Lean_MessageData_ofFormat(v___x_899_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 7);
lean_ctor_set(v___x_879_, 1, v___x_900_);
lean_ctor_set(v___x_879_, 0, v___x_895_);
v___x_902_ = v___x_879_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_900_);
v___x_902_ = v_reuseFailAlloc_910_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_903_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_MessageData_ofName(v___x_888_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_872_, v___x_908_, v_snd_877_, v___x_856_, v_a_817_);
lean_dec_ref_known(v___x_856_, 14);
lean_dec(v_snd_877_);
lean_dec(v_tailKey_872_);
return v___x_909_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_887_);
lean_inc(v_currArrKey_886_);
lean_inc(v_arrParents_885_);
lean_inc(v_arrKeyTys_884_);
lean_inc(v_keyTys_883_);
lean_dec(v___x_889_);
lean_del_object(v___x_879_);
lean_dec(v_snd_877_);
lean_dec(v_tailKey_872_);
lean_dec_ref_known(v___x_856_, 14);
v___y_820_ = v___x_888_;
v_keyTys_821_ = v_keyTys_883_;
v_arrKeyTys_822_ = v_arrKeyTys_884_;
v_arrParents_823_ = v_arrParents_885_;
v_currArrKey_824_ = v_currArrKey_886_;
v_items_825_ = v_items_887_;
goto v___jp_819_;
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_del_object(v___x_879_);
lean_dec(v_snd_877_);
lean_dec(v_fst_876_);
lean_dec(v_tailKey_872_);
lean_dec_ref_known(v___x_856_, 14);
lean_dec(v_x_814_);
v_a_913_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_881_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_881_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_tailKey_872_);
lean_dec_ref_known(v___x_856_, 14);
lean_dec(v_x_814_);
v_a_922_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_874_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_874_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
}
v___jp_819_:
{
lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_826_ = lean_box(0);
v___x_827_ = 1;
v___x_828_ = lean_box(v___x_827_);
lean_inc_n(v___y_820_, 2);
v___x_829_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_820_, v___x_828_, v_keyTys_821_);
v___x_830_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc(v_x_814_);
v___x_831_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_831_, 0, v_x_814_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_832_, 0, v_x_814_);
lean_ctor_set(v___x_832_, 1, v___y_820_);
lean_ctor_set(v___x_832_, 2, v___x_831_);
v___x_833_ = lean_array_push(v_items_825_, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_834_, 0, v___x_829_);
lean_ctor_set(v___x_834_, 1, v_arrKeyTys_822_);
lean_ctor_set(v___x_834_, 2, v_arrParents_823_);
lean_ctor_set(v___x_834_, 3, v_currArrKey_824_);
lean_ctor_set(v___x_834_, 4, v___y_820_);
lean_ctor_set(v___x_834_, 5, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_826_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_951_, v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_956_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_fileName_970_; lean_object* v_fileMap_971_; lean_object* v_options_972_; lean_object* v_currRecDepth_973_; lean_object* v_maxRecDepth_974_; lean_object* v_ref_975_; lean_object* v_currNamespace_976_; lean_object* v_openDecls_977_; lean_object* v_initHeartbeats_978_; lean_object* v_maxHeartbeats_979_; lean_object* v_quotContext_980_; lean_object* v_currMacroScope_981_; uint8_t v_diag_982_; lean_object* v_cancelTk_x3f_983_; uint8_t v_suppressElabErrors_984_; lean_object* v_inheritedTraceOptions_985_; lean_object* v___x_986_; uint8_t v___x_987_; lean_object* v_ref_988_; lean_object* v___x_989_; lean_object* v___y_991_; 
v_fileName_970_ = lean_ctor_get(v_a_967_, 0);
v_fileMap_971_ = lean_ctor_get(v_a_967_, 1);
v_options_972_ = lean_ctor_get(v_a_967_, 2);
v_currRecDepth_973_ = lean_ctor_get(v_a_967_, 3);
v_maxRecDepth_974_ = lean_ctor_get(v_a_967_, 4);
v_ref_975_ = lean_ctor_get(v_a_967_, 5);
v_currNamespace_976_ = lean_ctor_get(v_a_967_, 6);
v_openDecls_977_ = lean_ctor_get(v_a_967_, 7);
v_initHeartbeats_978_ = lean_ctor_get(v_a_967_, 8);
v_maxHeartbeats_979_ = lean_ctor_get(v_a_967_, 9);
v_quotContext_980_ = lean_ctor_get(v_a_967_, 10);
v_currMacroScope_981_ = lean_ctor_get(v_a_967_, 11);
v_diag_982_ = lean_ctor_get_uint8(v_a_967_, sizeof(void*)*14);
v_cancelTk_x3f_983_ = lean_ctor_get(v_a_967_, 12);
v_suppressElabErrors_984_ = lean_ctor_get_uint8(v_a_967_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_985_ = lean_ctor_get(v_a_967_, 13);
v___x_986_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_965_);
v___x_987_ = l_Lean_Syntax_isOfKind(v_x_965_, v___x_986_);
v_ref_988_ = l_Lean_replaceRef(v_x_965_, v_ref_975_);
lean_inc_ref(v_inheritedTraceOptions_985_);
lean_inc(v_cancelTk_x3f_983_);
lean_inc(v_currMacroScope_981_);
lean_inc(v_quotContext_980_);
lean_inc(v_maxHeartbeats_979_);
lean_inc(v_initHeartbeats_978_);
lean_inc(v_openDecls_977_);
lean_inc(v_currNamespace_976_);
lean_inc(v_maxRecDepth_974_);
lean_inc(v_currRecDepth_973_);
lean_inc_ref(v_options_972_);
lean_inc_ref(v_fileMap_971_);
lean_inc_ref(v_fileName_970_);
v___x_989_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_989_, 0, v_fileName_970_);
lean_ctor_set(v___x_989_, 1, v_fileMap_971_);
lean_ctor_set(v___x_989_, 2, v_options_972_);
lean_ctor_set(v___x_989_, 3, v_currRecDepth_973_);
lean_ctor_set(v___x_989_, 4, v_maxRecDepth_974_);
lean_ctor_set(v___x_989_, 5, v_ref_988_);
lean_ctor_set(v___x_989_, 6, v_currNamespace_976_);
lean_ctor_set(v___x_989_, 7, v_openDecls_977_);
lean_ctor_set(v___x_989_, 8, v_initHeartbeats_978_);
lean_ctor_set(v___x_989_, 9, v_maxHeartbeats_979_);
lean_ctor_set(v___x_989_, 10, v_quotContext_980_);
lean_ctor_set(v___x_989_, 11, v_currMacroScope_981_);
lean_ctor_set(v___x_989_, 12, v_cancelTk_x3f_983_);
lean_ctor_set(v___x_989_, 13, v_inheritedTraceOptions_985_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*14, v_diag_982_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*14 + 1, v_suppressElabErrors_984_);
if (v___x_987_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_999_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_965_, v___x_998_, v_a_966_, v___x_989_, v_a_968_);
lean_dec_ref_known(v___x_989_, 14);
lean_dec_ref(v_a_966_);
lean_dec(v_x_965_);
return v___x_999_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___y_1005_; 
v___x_1000_ = lean_unsigned_to_nat(2u);
v___x_1001_ = l_Lean_Syntax_getArg(v_x_965_, v___x_1000_);
v___x_1002_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_1001_);
v___x_1003_ = l_Lean_Syntax_isOfKind(v___x_1001_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v___x_1001_);
v___x_1139_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1140_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_965_, v___x_1139_, v_a_966_, v___x_989_, v_a_968_);
lean_dec_ref_known(v___x_989_, 14);
lean_dec_ref(v_a_966_);
lean_dec(v_x_965_);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = l_Lean_Syntax_getArg(v___x_1001_, v___x_1141_);
lean_dec(v___x_1001_);
v___x_1143_ = l_Lean_Syntax_getArgs(v___x_1142_);
lean_dec(v___x_1142_);
v___x_1144_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1145_ = lean_array_get_size(v___x_1143_);
v___x_1146_ = lean_nat_dec_lt(v___x_1141_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_dec_ref(v___x_1143_);
v___y_1005_ = v___x_1144_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = lean_box(v___x_1003_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v___x_1144_);
v___x_1149_ = lean_nat_dec_le(v___x_1145_, v___x_1145_);
if (v___x_1149_ == 0)
{
if (v___x_1146_ == 0)
{
lean_dec_ref_known(v___x_1148_, 2);
lean_dec_ref(v___x_1143_);
v___y_1005_ = v___x_1144_;
goto v___jp_1004_;
}
else
{
size_t v___x_1150_; size_t v___x_1151_; lean_object* v___x_1152_; lean_object* v_snd_1153_; 
v___x_1150_ = ((size_t)0ULL);
v___x_1151_ = lean_usize_of_nat(v___x_1145_);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_1003_, v___x_1143_, v___x_1150_, v___x_1151_, v___x_1148_);
lean_dec_ref(v___x_1143_);
v_snd_1153_ = lean_ctor_get(v___x_1152_, 1);
lean_inc(v_snd_1153_);
lean_dec_ref(v___x_1152_);
v___y_1005_ = v_snd_1153_;
goto v___jp_1004_;
}
}
else
{
size_t v___x_1154_; size_t v___x_1155_; lean_object* v___x_1156_; lean_object* v_snd_1157_; 
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = lean_usize_of_nat(v___x_1145_);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_1003_, v___x_1143_, v___x_1154_, v___x_1155_, v___x_1148_);
lean_dec_ref(v___x_1143_);
v_snd_1157_ = lean_ctor_get(v___x_1156_, 1);
lean_inc(v_snd_1157_);
lean_dec_ref(v___x_1156_);
v___y_1005_ = v_snd_1157_;
goto v___jp_1004_;
}
}
}
v___jp_1004_:
{
size_t v_sz_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
v_sz_1006_ = lean_array_size(v___y_1005_);
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_1006_, v___x_1007_, v___y_1005_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1010_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_965_, v___x_1009_, v_a_966_, v___x_989_, v_a_968_);
lean_dec_ref_known(v___x_989_, 14);
lean_dec_ref(v_a_966_);
lean_dec(v_x_965_);
return v___x_1010_;
}
else
{
lean_object* v_val_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_tailKey_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_val_1011_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_array_get_size(v_val_1011_);
v___x_1014_ = lean_unsigned_to_nat(1u);
v___x_1015_ = lean_nat_sub(v___x_1013_, v___x_1014_);
v_tailKey_1016_ = lean_array_get(v___x_1012_, v_val_1011_, v___x_1015_);
lean_dec(v___x_1015_);
v___x_1017_ = lean_array_pop(v_val_1011_);
v___x_1018_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_1017_, v_a_966_, v___x_989_, v_a_968_);
lean_dec_ref(v___x_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v_fst_1020_; lean_object* v_snd_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1130_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v_fst_1020_ = lean_ctor_get(v_a_1019_, 0);
v_snd_1021_ = lean_ctor_get(v_a_1019_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_a_1019_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1023_ = v_a_1019_;
v_isShared_1024_ = v_isSharedCheck_1130_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_snd_1021_);
lean_inc(v_fst_1020_);
lean_dec(v_a_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1130_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; 
lean_inc(v_tailKey_1016_);
v___x_1025_ = l_Lake_Toml_elabSimpleKey(v_tailKey_1016_, v___x_989_, v_a_968_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1121_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1121_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1121_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_keyTys_1030_; lean_object* v_arrKeyTys_1031_; lean_object* v_arrParents_1032_; lean_object* v_currArrKey_1033_; lean_object* v_items_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_keyTys_1030_ = lean_ctor_get(v_snd_1021_, 0);
v_arrKeyTys_1031_ = lean_ctor_get(v_snd_1021_, 1);
v_arrParents_1032_ = lean_ctor_get(v_snd_1021_, 2);
v_currArrKey_1033_ = lean_ctor_get(v_snd_1021_, 3);
v_items_1034_ = lean_ctor_get(v_snd_1021_, 5);
v___x_1035_ = l_Lean_Name_str___override(v_fst_1020_, v_a_1026_);
v___x_1036_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_1030_, v___x_1035_);
if (lean_obj_tag(v___x_1036_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1088_; 
v_val_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1088_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_val_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1088_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
uint8_t v___x_1041_; 
v___x_1041_ = lean_unbox(v_val_1037_);
if (v___x_1041_ == 2)
{
lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1066_; 
lean_inc_ref(v_items_1034_);
lean_inc(v_arrParents_1032_);
lean_inc(v_arrKeyTys_1031_);
lean_del_object(v___x_1039_);
lean_dec(v_val_1037_);
lean_dec(v_tailKey_1016_);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_snd_1021_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; lean_object* v_unused_1070_; lean_object* v_unused_1071_; lean_object* v_unused_1072_; 
v_unused_1067_ = lean_ctor_get(v_snd_1021_, 5);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_snd_1021_, 4);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_snd_1021_, 3);
lean_dec(v_unused_1069_);
v_unused_1070_ = lean_ctor_get(v_snd_1021_, 2);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v_snd_1021_, 1);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_snd_1021_, 0);
lean_dec(v_unused_1072_);
v___x_1043_ = v_snd_1021_;
v_isShared_1044_ = v_isSharedCheck_1066_;
goto v_resetjp_1042_;
}
else
{
lean_dec(v_snd_1021_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1066_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_1032_, v___x_1035_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_del_object(v___x_1043_);
lean_dec_ref(v_items_1034_);
lean_dec(v_arrParents_1032_);
lean_dec(v_arrKeyTys_1031_);
lean_del_object(v___x_1028_);
lean_del_object(v___x_1023_);
lean_dec(v_x_965_);
v___y_991_ = v___x_1035_;
goto v___jp_990_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1047_; 
v_val_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_val_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_1031_, v_val_1046_);
lean_dec(v_val_1046_);
if (lean_obj_tag(v___x_1047_) == 1)
{
lean_object* v_val_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_dec_ref_known(v___x_989_, 14);
v_val_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_965_, 2);
v___x_1051_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_x_965_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_mk_empty_array_with_capacity(v___x_1014_);
v___x_1053_ = lean_array_push(v___x_1052_, v___x_1051_);
v___x_1054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_x_965_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
lean_inc_n(v___x_1035_, 2);
v___x_1055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1055_, 0, v_x_965_);
lean_ctor_set(v___x_1055_, 1, v___x_1035_);
lean_ctor_set(v___x_1055_, 2, v___x_1054_);
v___x_1056_ = lean_array_push(v_items_1034_, v___x_1055_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 5, v___x_1056_);
lean_ctor_set(v___x_1043_, 4, v___x_1035_);
lean_ctor_set(v___x_1043_, 3, v___x_1035_);
lean_ctor_set(v___x_1043_, 0, v_val_1048_);
v___x_1058_ = v___x_1043_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_val_1048_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_arrKeyTys_1031_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_arrParents_1032_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1065_, 5, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1058_);
lean_ctor_set(v___x_1023_, 0, v___x_1049_);
v___x_1060_ = v___x_1023_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1060_);
v___x_1062_ = v___x_1028_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_dec(v___x_1047_);
lean_del_object(v___x_1043_);
lean_dec_ref(v_items_1034_);
lean_dec(v_arrParents_1032_);
lean_dec(v_arrKeyTys_1031_);
lean_del_object(v___x_1028_);
lean_del_object(v___x_1023_);
lean_dec(v_x_965_);
v___y_991_ = v___x_1035_;
goto v___jp_990_;
}
}
}
}
else
{
lean_object* v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_del_object(v___x_1028_);
lean_del_object(v___x_1023_);
lean_dec(v_x_965_);
v___x_1073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1074_ = lean_unbox(v_val_1037_);
lean_dec(v_val_1037_);
v___x_1075_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1074_);
v___x_1076_ = lean_string_append(v___x_1073_, v___x_1075_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
v___x_1079_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1035_, v___x_1003_);
v___x_1080_ = lean_string_append(v___x_1078_, v___x_1079_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1082_ = lean_string_append(v___x_1080_, v___x_1081_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 3);
lean_ctor_set(v___x_1039_, 0, v___x_1082_);
v___x_1084_ = v___x_1039_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = l_Lean_MessageData_ofFormat(v___x_1084_);
v___x_1086_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_1016_, v___x_1085_, v_snd_1021_, v___x_989_, v_a_968_);
lean_dec_ref_known(v___x_989_, 14);
lean_dec(v_snd_1021_);
lean_dec(v_tailKey_1016_);
return v___x_1086_;
}
}
}
}
else
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1114_; 
lean_inc_ref(v_items_1034_);
lean_inc(v_currArrKey_1033_);
lean_inc(v_arrParents_1032_);
lean_inc(v_arrKeyTys_1031_);
lean_inc(v_keyTys_1030_);
lean_dec(v___x_1036_);
lean_dec(v_tailKey_1016_);
lean_dec_ref_known(v___x_989_, 14);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_snd_1021_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1115_ = lean_ctor_get(v_snd_1021_, 5);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_snd_1021_, 4);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_snd_1021_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_snd_1021_, 2);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_snd_1021_, 1);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_snd_1021_, 0);
lean_dec(v_unused_1120_);
v___x_1090_ = v_snd_1021_;
v_isShared_1091_ = v_isSharedCheck_1114_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v_snd_1021_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1114_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = 2;
v___x_1094_ = lean_box(v___x_1093_);
lean_inc_n(v___x_1035_, 4);
v___x_1095_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1035_, v___x_1094_, v_keyTys_1030_);
lean_inc(v___x_1095_);
lean_inc(v_currArrKey_1033_);
v___x_1096_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_1033_, v___x_1095_, v_arrKeyTys_1031_);
v___x_1097_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1035_, v_currArrKey_1033_, v_arrParents_1032_);
v___x_1098_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_965_, 2);
v___x_1099_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_x_965_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_mk_empty_array_with_capacity(v___x_1014_);
v___x_1101_ = lean_array_push(v___x_1100_, v___x_1099_);
v___x_1102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_x_965_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1103_, 0, v_x_965_);
lean_ctor_set(v___x_1103_, 1, v___x_1035_);
lean_ctor_set(v___x_1103_, 2, v___x_1102_);
v___x_1104_ = lean_array_push(v_items_1034_, v___x_1103_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 5, v___x_1104_);
lean_ctor_set(v___x_1090_, 4, v___x_1035_);
lean_ctor_set(v___x_1090_, 3, v___x_1035_);
lean_ctor_set(v___x_1090_, 2, v___x_1097_);
lean_ctor_set(v___x_1090_, 1, v___x_1096_);
lean_ctor_set(v___x_1090_, 0, v___x_1095_);
v___x_1106_ = v___x_1090_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1113_, 5, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1106_);
lean_ctor_set(v___x_1023_, 0, v___x_1092_);
v___x_1108_ = v___x_1023_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1108_);
v___x_1110_ = v___x_1028_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_del_object(v___x_1023_);
lean_dec(v_snd_1021_);
lean_dec(v_fst_1020_);
lean_dec(v_tailKey_1016_);
lean_dec_ref_known(v___x_989_, 14);
lean_dec(v_x_965_);
v_a_1122_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1025_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1025_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_tailKey_1016_);
lean_dec_ref_known(v___x_989_, 14);
lean_dec(v_x_965_);
v_a_1131_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1018_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1018_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
v___jp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_992_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_993_ = l_Lean_MessageData_ofName(v___y_991_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_996_, v___x_989_, v_a_968_);
lean_dec_ref_known(v___x_989_, 14);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1163_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1167_);
v___x_1173_ = l_Lean_Syntax_isOfKind(v_x_1167_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_1167_);
v___x_1175_ = l_Lean_Syntax_isOfKind(v_x_1167_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1167_);
v___x_1177_ = l_Lean_Syntax_isOfKind(v_x_1167_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1179_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1167_, v___x_1178_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec_ref(v_a_1168_);
lean_dec(v_x_1167_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; 
v___x_1180_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
return v___x_1180_;
}
}
else
{
lean_object* v___x_1181_; 
v___x_1181_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
return v___x_1181_;
}
}
else
{
lean_object* v___x_1182_; 
v___x_1182_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1189_, lean_object* v_as_1190_, size_t v_i_1191_, size_t v_stop_1192_, lean_object* v_b_1193_){
_start:
{
lean_object* v___y_1195_; uint8_t v___x_1199_; 
v___x_1199_ = lean_usize_dec_eq(v_i_1191_, v_stop_1192_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v_fst_1201_; lean_object* v_snd_1202_; lean_object* v___x_1203_; 
v___x_1200_ = lean_array_uget_borrowed(v_as_1190_, v_i_1191_);
v_fst_1201_ = lean_ctor_get(v___x_1200_, 0);
v_snd_1202_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_fst_1201_);
v___x_1203_ = l_Lean_Name_components(v_fst_1201_);
if (lean_obj_tag(v___x_1203_) == 0)
{
v___y_1195_ = v_b_1193_;
goto v___jp_1194_;
}
else
{
lean_object* v_head_1204_; lean_object* v_tail_1205_; lean_object* v___x_1206_; 
v_head_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_head_1204_);
v_tail_1205_ = lean_ctor_get(v___x_1203_, 1);
lean_inc(v_tail_1205_);
lean_dec_ref_known(v___x_1203_, 2);
lean_inc(v_snd_1202_);
lean_inc(v_ref_1189_);
v___x_1206_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1193_, v_ref_1189_, v_head_1204_, v_tail_1205_, v_snd_1202_);
v___y_1195_ = v___x_1206_;
goto v___jp_1194_;
}
}
else
{
lean_dec(v_ref_1189_);
return v_b_1193_;
}
v___jp_1194_:
{
size_t v___x_1196_; size_t v___x_1197_; 
v___x_1196_ = ((size_t)1ULL);
v___x_1197_ = lean_usize_add(v_i_1191_, v___x_1196_);
v_i_1191_ = v___x_1197_;
v_b_1193_ = v___y_1195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1207_, size_t v_i_1208_, lean_object* v_bs_1209_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_usize_dec_lt(v_i_1208_, v_sz_1207_);
if (v___x_1210_ == 0)
{
return v_bs_1209_;
}
else
{
lean_object* v_v_1211_; lean_object* v___x_1212_; lean_object* v_bs_x27_1213_; lean_object* v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v_v_1211_ = lean_array_uget(v_bs_1209_, v_i_1208_);
v___x_1212_ = lean_unsigned_to_nat(0u);
v_bs_x27_1213_ = lean_array_uset(v_bs_1209_, v_i_1208_, v___x_1212_);
v___x_1214_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1211_);
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1208_, v___x_1215_);
v___x_1217_ = lean_array_uset(v_bs_x27_1213_, v_i_1208_, v___x_1214_);
v_i_1208_ = v___x_1216_;
v_bs_1209_ = v___x_1217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1219_){
_start:
{
switch(lean_obj_tag(v_a_1219_))
{
case 6:
{
lean_object* v_xs_1220_; lean_object* v_ref_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1249_; 
v_xs_1220_ = lean_ctor_get(v_a_1219_, 1);
v_ref_1221_ = lean_ctor_get(v_a_1219_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_a_1219_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1223_ = v_a_1219_;
v_isShared_1224_ = v_isSharedCheck_1249_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_xs_1220_);
lean_inc(v_ref_1221_);
lean_dec(v_a_1219_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1249_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_items_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v_items_1225_ = lean_ctor_get(v_xs_1220_, 0);
lean_inc_ref(v_items_1225_);
lean_dec_ref(v_xs_1220_);
v___x_1226_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_array_get_size(v_items_1225_);
v___x_1229_ = lean_nat_dec_lt(v___x_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1231_; 
lean_dec_ref(v_items_1225_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1226_);
v___x_1231_ = v___x_1223_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_ref_1221_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_nat_dec_le(v___x_1228_, v___x_1228_);
if (v___x_1233_ == 0)
{
if (v___x_1229_ == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref(v_items_1225_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1226_);
v___x_1235_ = v___x_1223_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_ref_1221_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1226_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
else
{
size_t v___x_1237_; size_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1237_ = ((size_t)0ULL);
v___x_1238_ = lean_usize_of_nat(v___x_1228_);
lean_inc(v_ref_1221_);
v___x_1239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1221_, v_items_1225_, v___x_1237_, v___x_1238_, v___x_1226_);
lean_dec_ref(v_items_1225_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1239_);
v___x_1241_ = v___x_1223_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_ref_1221_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
size_t v___x_1243_; size_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1243_ = ((size_t)0ULL);
v___x_1244_ = lean_usize_of_nat(v___x_1228_);
lean_inc(v_ref_1221_);
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1221_, v_items_1225_, v___x_1243_, v___x_1244_, v___x_1226_);
lean_dec_ref(v_items_1225_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1245_);
v___x_1247_ = v___x_1223_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_ref_1221_);
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
}
}
case 5:
{
lean_object* v_ref_1250_; lean_object* v_xs_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1261_; 
v_ref_1250_ = lean_ctor_get(v_a_1219_, 0);
v_xs_1251_ = lean_ctor_get(v_a_1219_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_a_1219_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1253_ = v_a_1219_;
v_isShared_1254_ = v_isSharedCheck_1261_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_xs_1251_);
lean_inc(v_ref_1250_);
lean_dec(v_a_1219_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1261_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
size_t v_sz_1255_; size_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_sz_1255_ = lean_array_size(v_xs_1251_);
v___x_1256_ = ((size_t)0ULL);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1255_, v___x_1256_, v_xs_1251_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v___x_1257_);
v___x_1259_ = v___x_1253_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_ref_1250_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
default: 
{
return v_a_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1262_, lean_object* v___x_1263_, lean_object* v_v_x3f_1264_){
_start:
{
if (lean_obj_tag(v_v_x3f_1264_) == 1)
{
lean_object* v_val_1265_; 
v_val_1265_ = lean_ctor_get(v_v_x3f_1264_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v_v_x3f_1264_, 1);
switch(lean_obj_tag(v_val_1265_))
{
case 6:
{
lean_object* v_ref_1266_; lean_object* v_xs_1267_; lean_object* v___x_1268_; 
v_ref_1266_ = lean_ctor_get(v_val_1265_, 0);
lean_inc(v_ref_1266_);
v_xs_1267_ = lean_ctor_get(v_val_1265_, 1);
lean_inc_ref(v_xs_1267_);
lean_dec_ref_known(v_val_1265_, 2);
v___x_1268_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1262_);
if (lean_obj_tag(v___x_1268_) == 6)
{
lean_object* v_xs_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1278_; 
v_xs_1269_ = lean_ctor_get(v___x_1268_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1268_, 0);
lean_dec(v_unused_1279_);
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1278_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_xs_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1278_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_items_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v_items_1273_ = lean_ctor_get(v_xs_1269_, 0);
lean_inc_ref(v_items_1273_);
lean_dec_ref(v_xs_1269_);
v___x_1274_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1263_, v_xs_1267_, v_items_1273_);
lean_dec_ref(v_items_1273_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1274_);
lean_ctor_set(v___x_1271_, 0, v_ref_1266_);
v___x_1276_ = v___x_1271_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_ref_1266_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_dec_ref(v_xs_1267_);
lean_dec(v_ref_1266_);
lean_dec_ref(v___x_1263_);
return v___x_1268_;
}
}
case 5:
{
lean_object* v_ref_1280_; lean_object* v_xs_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v___x_1263_);
v_ref_1280_ = lean_ctor_get(v_val_1265_, 0);
v_xs_1281_ = lean_ctor_get(v_val_1265_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_val_1265_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1283_ = v_val_1265_;
v_isShared_1284_ = v_isSharedCheck_1300_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_xs_1281_);
lean_inc(v_ref_1280_);
lean_dec(v_val_1265_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1300_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; 
v___x_1285_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1262_);
if (lean_obj_tag(v___x_1285_) == 5)
{
lean_object* v_xs_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1294_; 
lean_del_object(v___x_1283_);
v_xs_1286_ = lean_ctor_get(v___x_1285_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v___x_1285_, 0);
lean_dec(v_unused_1295_);
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_xs_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = l_Array_append___redArg(v_xs_1281_, v_xs_1286_);
lean_dec_ref(v_xs_1286_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___x_1290_);
lean_ctor_set(v___x_1288_, 0, v_ref_1280_);
v___x_1292_ = v___x_1288_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_ref_1280_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = lean_array_push(v_xs_1281_, v___x_1285_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v___x_1296_);
v___x_1298_ = v___x_1283_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_ref_1280_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
default: 
{
lean_object* v___x_1301_; 
lean_dec(v_val_1265_);
lean_dec_ref(v___x_1263_);
v___x_1301_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1262_);
return v___x_1301_;
}
}
}
else
{
lean_object* v___x_1302_; 
lean_dec(v_v_x3f_1264_);
lean_dec_ref(v___x_1263_);
v___x_1302_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1262_);
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1303_, lean_object* v_k_1304_, lean_object* v_t_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1305_);
lean_inc(v_k_1304_);
v___x_1307_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1306_, v_k_1304_, v_t_1305_);
if (lean_obj_tag(v___x_1307_) == 1)
{
lean_object* v_val_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_k_1304_);
v_val_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1343_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_val_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1343_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_items_1312_; lean_object* v_indices_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1342_; 
v_items_1312_ = lean_ctor_get(v_t_1305_, 0);
v_indices_1313_ = lean_ctor_get(v_t_1305_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_t_1305_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1315_ = v_t_1305_;
v_isShared_1316_ = v_isSharedCheck_1342_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_indices_1313_);
lean_inc(v_items_1312_);
lean_dec(v_t_1305_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1342_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_array_get_size(v_items_1312_);
v___x_1318_ = lean_nat_dec_lt(v_val_1308_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1320_; 
lean_del_object(v___x_1310_);
lean_dec(v_val_1308_);
lean_dec_ref(v_newV_1303_);
if (v_isShared_1316_ == 0)
{
v___x_1320_ = v___x_1315_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_items_1312_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_indices_1313_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
lean_object* v_v_1322_; lean_object* v_fst_1323_; lean_object* v_snd_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1341_; 
v_v_1322_ = lean_array_fget(v_items_1312_, v_val_1308_);
v_fst_1323_ = lean_ctor_get(v_v_1322_, 0);
v_snd_1324_ = lean_ctor_get(v_v_1322_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_v_1322_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1326_ = v_v_1322_;
v_isShared_1327_ = v_isSharedCheck_1341_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_snd_1324_);
lean_inc(v_fst_1323_);
lean_dec(v_v_1322_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1341_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v_xs_x27_1329_; lean_object* v___x_1331_; 
v___x_1328_ = lean_box(0);
v_xs_x27_1329_ = lean_array_fset(v_items_1312_, v_val_1308_, v___x_1328_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v_snd_1324_);
v___x_1331_ = v___x_1310_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_snd_1324_);
v___x_1331_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1303_, v___x_1306_, v___x_1331_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v___x_1332_);
v___x_1334_ = v___x_1326_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_fst_1323_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_array_fset(v_xs_x27_1329_, v_val_1308_, v___x_1334_);
lean_dec(v_val_1308_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1335_);
v___x_1337_ = v___x_1315_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_indices_1313_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
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
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v___x_1307_);
v___x_1344_ = lean_box(0);
v___x_1345_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1303_, v___x_1306_, v___x_1344_);
v___x_1346_ = l_Lake_Toml_RBDict_push___redArg(v___x_1306_, v_k_1304_, v___x_1345_, v_t_1305_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1347_, lean_object* v_head_1348_, lean_object* v_tail_1349_, lean_object* v_newV_1350_, lean_object* v___x_1351_, lean_object* v_v_x3f_1352_){
_start:
{
if (lean_obj_tag(v_v_x3f_1352_) == 1)
{
lean_object* v_val_1353_; 
v_val_1353_ = lean_ctor_get(v_v_x3f_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v_v_x3f_1352_, 1);
switch(lean_obj_tag(v_val_1353_))
{
case 5:
{
lean_object* v_ref_1354_; lean_object* v_xs_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v_ref_1354_ = lean_ctor_get(v_val_1353_, 0);
v_xs_1355_ = lean_ctor_get(v_val_1353_, 1);
v___x_1356_ = lean_array_get_size(v_xs_1355_);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_nat_sub(v___x_1356_, v___x_1357_);
v___x_1359_ = lean_nat_dec_lt(v___x_1358_, v___x_1356_);
if (v___x_1359_ == 0)
{
lean_dec(v___x_1358_);
lean_dec_ref(v_newV_1350_);
lean_dec(v_tail_1349_);
lean_dec(v_head_1348_);
lean_dec(v_kRef_1347_);
return v_val_1353_;
}
else
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1384_; 
lean_inc_ref(v_xs_1355_);
lean_inc(v_ref_1354_);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_val_1353_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; lean_object* v_unused_1386_; 
v_unused_1385_ = lean_ctor_get(v_val_1353_, 1);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_val_1353_, 0);
lean_dec(v_unused_1386_);
v___x_1361_ = v_val_1353_;
v_isShared_1362_ = v_isSharedCheck_1384_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v_val_1353_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1384_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v_v_1363_; lean_object* v___x_1364_; lean_object* v_xs_x27_1365_; lean_object* v___y_1367_; 
v_v_1363_ = lean_array_fget(v_xs_1355_, v___x_1358_);
v___x_1364_ = lean_box(0);
v_xs_x27_1365_ = lean_array_fset(v_xs_1355_, v___x_1358_, v___x_1364_);
if (lean_obj_tag(v_v_1363_) == 6)
{
lean_object* v_ref_1372_; lean_object* v_xs_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1381_; 
v_ref_1372_ = lean_ctor_get(v_v_1363_, 0);
v_xs_1373_ = lean_ctor_get(v_v_1363_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_v_1363_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1375_ = v_v_1363_;
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_xs_1373_);
lean_inc(v_ref_1372_);
lean_dec(v_v_1363_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1373_, v_kRef_1347_, v_head_1348_, v_tail_1349_, v_newV_1350_);
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
v___y_1367_ = v___x_1379_;
goto v___jp_1366_;
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v_v_1363_);
lean_dec_ref(v_newV_1350_);
lean_dec(v_tail_1349_);
lean_dec(v_head_1348_);
v___x_1382_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1351_);
v___x_1383_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_kRef_1347_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___y_1367_ = v___x_1383_;
goto v___jp_1366_;
}
v___jp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = lean_array_fset(v_xs_x27_1365_, v___x_1358_, v___y_1367_);
lean_dec(v___x_1358_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v___x_1368_);
v___x_1370_ = v___x_1361_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_ref_1354_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1387_; lean_object* v_xs_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1396_; 
v_ref_1387_ = lean_ctor_get(v_val_1353_, 0);
v_xs_1388_ = lean_ctor_get(v_val_1353_, 1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_val_1353_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1390_ = v_val_1353_;
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_xs_1388_);
lean_inc(v_ref_1387_);
lean_dec(v_val_1353_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1388_, v_kRef_1347_, v_head_1348_, v_tail_1349_, v_newV_1350_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v___x_1392_);
v___x_1394_ = v___x_1390_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_ref_1387_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
default: 
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec(v_val_1353_);
v___x_1397_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1351_);
lean_inc(v_kRef_1347_);
v___x_1398_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1397_, v_kRef_1347_, v_head_1348_, v_tail_1349_, v_newV_1350_);
v___x_1399_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_kRef_1347_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
return v___x_1399_;
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec(v_v_x3f_1352_);
v___x_1400_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1351_);
lean_inc(v_kRef_1347_);
v___x_1401_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1400_, v_kRef_1347_, v_head_1348_, v_tail_1349_, v_newV_1350_);
v___x_1402_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_kRef_1347_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1403_, lean_object* v_head_1404_, lean_object* v_tail_1405_, lean_object* v_newV_1406_, lean_object* v_k_1407_, lean_object* v_t_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1408_);
lean_inc(v_k_1407_);
v___x_1410_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1409_, v_k_1407_, v_t_1408_);
if (lean_obj_tag(v___x_1410_) == 1)
{
lean_object* v_val_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_k_1407_);
v_val_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1446_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_val_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1446_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_items_1415_; lean_object* v_indices_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1445_; 
v_items_1415_ = lean_ctor_get(v_t_1408_, 0);
v_indices_1416_ = lean_ctor_get(v_t_1408_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_t_1408_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1418_ = v_t_1408_;
v_isShared_1419_ = v_isSharedCheck_1445_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_indices_1416_);
lean_inc(v_items_1415_);
lean_dec(v_t_1408_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1445_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = lean_array_get_size(v_items_1415_);
v___x_1421_ = lean_nat_dec_lt(v_val_1411_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1423_; 
lean_del_object(v___x_1413_);
lean_dec(v_val_1411_);
lean_dec_ref(v_newV_1406_);
lean_dec(v_tail_1405_);
lean_dec(v_head_1404_);
lean_dec(v_kRef_1403_);
if (v_isShared_1419_ == 0)
{
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_items_1415_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_indices_1416_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
else
{
lean_object* v_v_1425_; lean_object* v_fst_1426_; lean_object* v_snd_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1444_; 
v_v_1425_ = lean_array_fget(v_items_1415_, v_val_1411_);
v_fst_1426_ = lean_ctor_get(v_v_1425_, 0);
v_snd_1427_ = lean_ctor_get(v_v_1425_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_v_1425_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1429_ = v_v_1425_;
v_isShared_1430_ = v_isSharedCheck_1444_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_snd_1427_);
lean_inc(v_fst_1426_);
lean_dec(v_v_1425_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1444_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v_xs_x27_1432_; lean_object* v___x_1434_; 
v___x_1431_ = lean_box(0);
v_xs_x27_1432_ = lean_array_fset(v_items_1415_, v_val_1411_, v___x_1431_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v_snd_1427_);
v___x_1434_ = v___x_1413_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_snd_1427_);
v___x_1434_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1403_, v_head_1404_, v_tail_1405_, v_newV_1406_, v___x_1409_, v___x_1434_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 1, v___x_1435_);
v___x_1437_ = v___x_1429_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_fst_1426_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_array_fset(v_xs_x27_1432_, v_val_1411_, v___x_1437_);
lean_dec(v_val_1411_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1438_);
v___x_1440_ = v___x_1418_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_indices_1416_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
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
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec(v___x_1410_);
v___x_1447_ = lean_box(0);
v___x_1448_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1403_, v_head_1404_, v_tail_1405_, v_newV_1406_, v___x_1409_, v___x_1447_);
v___x_1449_ = l_Lake_Toml_RBDict_push___redArg(v___x_1409_, v_k_1407_, v___x_1448_, v_t_1408_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1450_, lean_object* v_kRef_1451_, lean_object* v_k_1452_, lean_object* v_ks_1453_, lean_object* v_newV_1454_){
_start:
{
if (lean_obj_tag(v_ks_1453_) == 0)
{
lean_object* v___x_1455_; 
lean_dec(v_kRef_1451_);
v___x_1455_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1454_, v_k_1452_, v_t_1450_);
return v___x_1455_;
}
else
{
lean_object* v_head_1456_; lean_object* v_tail_1457_; lean_object* v___x_1458_; 
v_head_1456_ = lean_ctor_get(v_ks_1453_, 0);
lean_inc(v_head_1456_);
v_tail_1457_ = lean_ctor_get(v_ks_1453_, 1);
lean_inc(v_tail_1457_);
lean_dec_ref_known(v_ks_1453_, 2);
v___x_1458_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1451_, v_head_1456_, v_tail_1457_, v_newV_1454_, v_k_1452_, v_t_1450_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1459_, lean_object* v_i_1460_, lean_object* v_bs_1461_){
_start:
{
size_t v_sz_boxed_1462_; size_t v_i_boxed_1463_; lean_object* v_res_1464_; 
v_sz_boxed_1462_ = lean_unbox_usize(v_sz_1459_);
lean_dec(v_sz_1459_);
v_i_boxed_1463_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1462_, v_i_boxed_1463_, v_bs_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1465_, lean_object* v_as_1466_, lean_object* v_i_1467_, lean_object* v_stop_1468_, lean_object* v_b_1469_){
_start:
{
size_t v_i_boxed_1470_; size_t v_stop_boxed_1471_; lean_object* v_res_1472_; 
v_i_boxed_1470_ = lean_unbox_usize(v_i_1467_);
lean_dec(v_i_1467_);
v_stop_boxed_1471_ = lean_unbox_usize(v_stop_1468_);
lean_dec(v_stop_1468_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1465_, v_as_1466_, v_i_boxed_1470_, v_stop_boxed_1471_, v_b_1469_);
lean_dec_ref(v_as_1466_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0___boxed(lean_object* v_kRef_1473_, lean_object* v_head_1474_, lean_object* v_tail_1475_, lean_object* v_newV_1476_, lean_object* v___x_1477_, lean_object* v_v_x3f_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1473_, v_head_1474_, v_tail_1475_, v_newV_1476_, v___x_1477_, v_v_x3f_1478_);
lean_dec_ref(v___x_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1480_, size_t v_i_1481_, size_t v_stop_1482_, lean_object* v_b_1483_){
_start:
{
lean_object* v___y_1485_; uint8_t v___x_1489_; 
v___x_1489_ = lean_usize_dec_eq(v_i_1481_, v_stop_1482_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v_ref_1491_; lean_object* v_key_1492_; lean_object* v_val_1493_; lean_object* v___x_1494_; 
v___x_1490_ = lean_array_uget_borrowed(v_as_1480_, v_i_1481_);
v_ref_1491_ = lean_ctor_get(v___x_1490_, 0);
v_key_1492_ = lean_ctor_get(v___x_1490_, 1);
v_val_1493_ = lean_ctor_get(v___x_1490_, 2);
lean_inc(v_key_1492_);
v___x_1494_ = l_Lean_Name_components(v_key_1492_);
if (lean_obj_tag(v___x_1494_) == 0)
{
v___y_1485_ = v_b_1483_;
goto v___jp_1484_;
}
else
{
lean_object* v_head_1495_; lean_object* v_tail_1496_; lean_object* v___x_1497_; 
v_head_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_head_1495_);
v_tail_1496_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_tail_1496_);
lean_dec_ref_known(v___x_1494_, 2);
lean_inc_ref(v_val_1493_);
lean_inc(v_ref_1491_);
v___x_1497_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1483_, v_ref_1491_, v_head_1495_, v_tail_1496_, v_val_1493_);
v___y_1485_ = v___x_1497_;
goto v___jp_1484_;
}
}
else
{
return v_b_1483_;
}
v___jp_1484_:
{
size_t v___x_1486_; size_t v___x_1487_; 
v___x_1486_ = ((size_t)1ULL);
v___x_1487_ = lean_usize_add(v_i_1481_, v___x_1486_);
v_i_1481_ = v___x_1487_;
v_b_1483_ = v___y_1485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1498_, lean_object* v_i_1499_, lean_object* v_stop_1500_, lean_object* v_b_1501_){
_start:
{
size_t v_i_boxed_1502_; size_t v_stop_boxed_1503_; lean_object* v_res_1504_; 
v_i_boxed_1502_ = lean_unbox_usize(v_i_1499_);
lean_dec(v_i_1499_);
v_stop_boxed_1503_ = lean_unbox_usize(v_stop_1500_);
lean_dec(v_stop_1500_);
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1498_, v_i_boxed_1502_, v_stop_boxed_1503_, v_b_1501_);
lean_dec_ref(v_as_1498_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1506_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_array_get_size(v_items_1505_);
v___x_1509_ = lean_nat_dec_lt(v___x_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
return v___x_1506_;
}
else
{
uint8_t v___x_1510_; 
v___x_1510_ = lean_nat_dec_le(v___x_1508_, v___x_1508_);
if (v___x_1510_ == 0)
{
if (v___x_1509_ == 0)
{
return v___x_1506_;
}
else
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = ((size_t)0ULL);
v___x_1512_ = lean_usize_of_nat(v___x_1508_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1505_, v___x_1511_, v___x_1512_, v___x_1506_);
return v___x_1513_;
}
}
else
{
size_t v___x_1514_; size_t v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = ((size_t)0ULL);
v___x_1515_ = lean_usize_of_nat(v___x_1508_);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1505_, v___x_1514_, v___x_1515_, v___x_1506_);
return v___x_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1517_);
lean_dec_ref(v_items_1517_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1521_);
lean_inc_ref(v_a_1520_);
v___x_1524_ = lean_apply_4(v_x_1519_, v___x_1523_, v_a_1520_, v_a_1521_, lean_box(0));
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1535_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1535_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1535_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_snd_1529_; lean_object* v_items_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v_snd_1529_ = lean_ctor_get(v_a_1525_, 1);
lean_inc(v_snd_1529_);
lean_dec(v_a_1525_);
v_items_1530_ = lean_ctor_get(v_snd_1529_, 5);
lean_inc_ref(v_items_1530_);
lean_dec(v_snd_1529_);
v___x_1531_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1530_);
lean_dec_ref(v_items_1530_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1531_);
v___x_1533_ = v___x_1527_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_a_1536_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1524_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1524_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1544_, v_a_1545_, v_a_1546_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
return v_res_1548_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v___y_1557_, uint8_t v_suppressElabErrors_1558_, lean_object* v_x_1559_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 1)
{
lean_object* v_pre_1560_; 
v_pre_1560_ = lean_ctor_get(v_x_1559_, 0);
switch(lean_obj_tag(v_pre_1560_))
{
case 1:
{
lean_object* v_pre_1561_; 
v_pre_1561_ = lean_ctor_get(v_pre_1560_, 0);
switch(lean_obj_tag(v_pre_1561_))
{
case 0:
{
lean_object* v_str_1562_; lean_object* v_str_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v_str_1562_ = lean_ctor_get(v_x_1559_, 1);
v_str_1563_ = lean_ctor_get(v_pre_1560_, 1);
v___x_1564_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1565_ = lean_string_dec_eq(v_str_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1567_ = lean_string_dec_eq(v_str_1563_, v___x_1566_);
if (v___x_1567_ == 0)
{
return v___y_1557_;
}
else
{
lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1569_ = lean_string_dec_eq(v_str_1562_, v___x_1568_);
if (v___x_1569_ == 0)
{
return v___y_1557_;
}
else
{
return v_suppressElabErrors_1558_;
}
}
}
else
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1571_ = lean_string_dec_eq(v_str_1562_, v___x_1570_);
if (v___x_1571_ == 0)
{
return v___y_1557_;
}
else
{
return v_suppressElabErrors_1558_;
}
}
}
case 1:
{
lean_object* v_pre_1572_; 
v_pre_1572_ = lean_ctor_get(v_pre_1561_, 0);
if (lean_obj_tag(v_pre_1572_) == 0)
{
lean_object* v_str_1573_; lean_object* v_str_1574_; lean_object* v_str_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v_str_1573_ = lean_ctor_get(v_x_1559_, 1);
v_str_1574_ = lean_ctor_get(v_pre_1560_, 1);
v_str_1575_ = lean_ctor_get(v_pre_1561_, 1);
v___x_1576_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1577_ = lean_string_dec_eq(v_str_1575_, v___x_1576_);
if (v___x_1577_ == 0)
{
return v___y_1557_;
}
else
{
lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1579_ = lean_string_dec_eq(v_str_1574_, v___x_1578_);
if (v___x_1579_ == 0)
{
return v___y_1557_;
}
else
{
lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1581_ = lean_string_dec_eq(v_str_1573_, v___x_1580_);
if (v___x_1581_ == 0)
{
return v___y_1557_;
}
else
{
return v_suppressElabErrors_1558_;
}
}
}
}
else
{
return v___y_1557_;
}
}
default: 
{
return v___y_1557_;
}
}
}
case 0:
{
lean_object* v_str_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_str_1582_ = lean_ctor_get(v_x_1559_, 1);
v___x_1583_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1584_ = lean_string_dec_eq(v_str_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
return v___y_1557_;
}
else
{
return v_suppressElabErrors_1558_;
}
}
default: 
{
return v___y_1557_;
}
}
}
else
{
return v___y_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v___y_1585_, lean_object* v_suppressElabErrors_1586_, lean_object* v_x_1587_){
_start:
{
uint8_t v___y_11747__boxed_1588_; uint8_t v_suppressElabErrors_boxed_1589_; uint8_t v_res_1590_; lean_object* v_r_1591_; 
v___y_11747__boxed_1588_ = lean_unbox(v___y_1585_);
v_suppressElabErrors_boxed_1589_ = lean_unbox(v_suppressElabErrors_1586_);
v_res_1590_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v___y_11747__boxed_1588_, v_suppressElabErrors_boxed_1589_, v_x_1587_);
lean_dec(v_x_1587_);
v_r_1591_ = lean_box(v_res_1590_);
return v_r_1591_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1592_, lean_object* v_opt_1593_){
_start:
{
lean_object* v_name_1594_; lean_object* v_defValue_1595_; lean_object* v_map_1596_; lean_object* v___x_1597_; 
v_name_1594_ = lean_ctor_get(v_opt_1593_, 0);
v_defValue_1595_ = lean_ctor_get(v_opt_1593_, 1);
v_map_1596_ = lean_ctor_get(v_opts_1592_, 0);
v___x_1597_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1596_, v_name_1594_);
if (lean_obj_tag(v___x_1597_) == 0)
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_unbox(v_defValue_1595_);
return v___x_1598_;
}
else
{
lean_object* v_val_1599_; 
v_val_1599_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_val_1599_);
lean_dec_ref_known(v___x_1597_, 1);
if (lean_obj_tag(v_val_1599_) == 1)
{
uint8_t v_v_1600_; 
v_v_1600_ = lean_ctor_get_uint8(v_val_1599_, 0);
lean_dec_ref_known(v_val_1599_, 0);
return v_v_1600_;
}
else
{
uint8_t v___x_1601_; 
lean_dec(v_val_1599_);
v___x_1601_ = lean_unbox(v_defValue_1595_);
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1602_, lean_object* v_opt_1603_){
_start:
{
uint8_t v_res_1604_; lean_object* v_r_1605_; 
v_res_1604_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1602_, v_opt_1603_);
lean_dec_ref(v_opt_1603_);
lean_dec_ref(v_opts_1602_);
v_r_1605_ = lean_box(v_res_1604_);
return v_r_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1607_, lean_object* v_msgData_1608_, uint8_t v_severity_1609_, uint8_t v_isSilent_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_a_1616_; lean_object* v___y_1620_; lean_object* v___y_1621_; uint8_t v___y_1622_; uint8_t v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1655_; uint8_t v___y_1656_; uint8_t v___y_1657_; uint8_t v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1679_; lean_object* v___y_1680_; uint8_t v___y_1681_; uint8_t v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1690_; uint8_t v___y_1691_; lean_object* v___y_1692_; uint8_t v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; uint8_t v___y_1696_; uint8_t v___x_1701_; uint8_t v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1708_; uint8_t v___y_1709_; uint8_t v___y_1711_; uint8_t v___x_1727_; 
v___x_1701_ = 2;
v___x_1727_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1609_, v___x_1701_);
if (v___x_1727_ == 0)
{
v___y_1711_ = v___x_1727_;
goto v___jp_1710_;
}
else
{
uint8_t v___x_1728_; 
lean_inc_ref(v_msgData_1608_);
v___x_1728_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1608_);
v___y_1711_ = v___x_1728_;
goto v___jp_1710_;
}
v___jp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_a_1616_);
lean_ctor_set(v___x_1617_, 1, v___y_1611_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
v___jp_1619_:
{
lean_object* v___x_1629_; lean_object* v_currNamespace_1630_; lean_object* v_openDecls_1631_; lean_object* v_env_1632_; lean_object* v_nextMacroScope_1633_; lean_object* v_ngen_1634_; lean_object* v_auxDeclNGen_1635_; lean_object* v_traceState_1636_; lean_object* v_cache_1637_; lean_object* v_messages_1638_; lean_object* v_infoState_1639_; lean_object* v_snapshotTasks_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1653_; 
v___x_1629_ = lean_st_ref_take(v___y_1628_);
v_currNamespace_1630_ = lean_ctor_get(v___y_1627_, 6);
v_openDecls_1631_ = lean_ctor_get(v___y_1627_, 7);
v_env_1632_ = lean_ctor_get(v___x_1629_, 0);
v_nextMacroScope_1633_ = lean_ctor_get(v___x_1629_, 1);
v_ngen_1634_ = lean_ctor_get(v___x_1629_, 2);
v_auxDeclNGen_1635_ = lean_ctor_get(v___x_1629_, 3);
v_traceState_1636_ = lean_ctor_get(v___x_1629_, 4);
v_cache_1637_ = lean_ctor_get(v___x_1629_, 5);
v_messages_1638_ = lean_ctor_get(v___x_1629_, 6);
v_infoState_1639_ = lean_ctor_get(v___x_1629_, 7);
v_snapshotTasks_1640_ = lean_ctor_get(v___x_1629_, 8);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1642_ = v___x_1629_;
v_isShared_1643_ = v_isSharedCheck_1653_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_snapshotTasks_1640_);
lean_inc(v_infoState_1639_);
lean_inc(v_messages_1638_);
lean_inc(v_cache_1637_);
lean_inc(v_traceState_1636_);
lean_inc(v_auxDeclNGen_1635_);
lean_inc(v_ngen_1634_);
lean_inc(v_nextMacroScope_1633_);
lean_inc(v_env_1632_);
lean_dec(v___x_1629_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1653_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
lean_inc(v_openDecls_1631_);
lean_inc(v_currNamespace_1630_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_currNamespace_1630_);
lean_ctor_set(v___x_1644_, 1, v_openDecls_1631_);
v___x_1645_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v___y_1625_);
lean_inc_ref(v___y_1621_);
lean_inc_ref(v___y_1626_);
v___x_1646_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1646_, 0, v___y_1626_);
lean_ctor_set(v___x_1646_, 1, v___y_1620_);
lean_ctor_set(v___x_1646_, 2, v___y_1624_);
lean_ctor_set(v___x_1646_, 3, v___y_1621_);
lean_ctor_set(v___x_1646_, 4, v___x_1645_);
lean_ctor_set_uint8(v___x_1646_, sizeof(void*)*5, v___y_1623_);
lean_ctor_set_uint8(v___x_1646_, sizeof(void*)*5 + 1, v___y_1622_);
lean_ctor_set_uint8(v___x_1646_, sizeof(void*)*5 + 2, v_isSilent_1610_);
v___x_1647_ = l_Lean_MessageLog_add(v___x_1646_, v_messages_1638_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 6, v___x_1647_);
v___x_1649_ = v___x_1642_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_env_1632_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_nextMacroScope_1633_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_ngen_1634_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_auxDeclNGen_1635_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_traceState_1636_);
lean_ctor_set(v_reuseFailAlloc_1652_, 5, v_cache_1637_);
lean_ctor_set(v_reuseFailAlloc_1652_, 6, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1652_, 7, v_infoState_1639_);
lean_ctor_set(v_reuseFailAlloc_1652_, 8, v_snapshotTasks_1640_);
v___x_1649_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_st_ref_set(v___y_1628_, v___x_1649_);
v___x_1651_ = lean_box(0);
v_a_1616_ = v___x_1651_;
goto v___jp_1615_;
}
}
}
v___jp_1654_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1677_; 
v___x_1663_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1608_);
v___x_1664_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1663_, v___y_1612_, v___y_1613_);
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1677_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1677_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
lean_inc_ref_n(v___y_1661_, 2);
v___x_1669_ = l_Lean_FileMap_toPosition(v___y_1661_, v___y_1659_);
lean_dec(v___y_1659_);
v___x_1670_ = l_Lean_FileMap_toPosition(v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
lean_ctor_set(v___x_1667_, 0, v___x_1670_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; 
v___x_1673_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1656_ == 0)
{
lean_dec_ref(v___y_1655_);
v___y_1620_ = v___x_1669_;
v___y_1621_ = v___x_1673_;
v___y_1622_ = v___y_1657_;
v___y_1623_ = v___y_1658_;
v___y_1624_ = v___x_1672_;
v___y_1625_ = v_a_1665_;
v___y_1626_ = v___y_1660_;
v___y_1627_ = v___y_1612_;
v___y_1628_ = v___y_1613_;
goto v___jp_1619_;
}
else
{
uint8_t v___x_1674_; 
lean_inc(v_a_1665_);
v___x_1674_ = l_Lean_MessageData_hasTag(v___y_1655_, v_a_1665_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
lean_dec_ref(v___x_1672_);
lean_dec_ref(v___x_1669_);
lean_dec(v_a_1665_);
v___x_1675_ = lean_box(0);
v_a_1616_ = v___x_1675_;
goto v___jp_1615_;
}
else
{
v___y_1620_ = v___x_1669_;
v___y_1621_ = v___x_1673_;
v___y_1622_ = v___y_1657_;
v___y_1623_ = v___y_1658_;
v___y_1624_ = v___x_1672_;
v___y_1625_ = v_a_1665_;
v___y_1626_ = v___y_1660_;
v___y_1627_ = v___y_1612_;
v___y_1628_ = v___y_1613_;
goto v___jp_1619_;
}
}
}
}
}
v___jp_1678_:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_Syntax_getTailPos_x3f(v___y_1680_, v___y_1683_);
lean_dec(v___y_1680_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_inc(v___y_1686_);
v___y_1655_ = v___y_1679_;
v___y_1656_ = v___y_1681_;
v___y_1657_ = v___y_1682_;
v___y_1658_ = v___y_1683_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v___y_1685_;
v___y_1661_ = v___y_1684_;
v___y_1662_ = v___y_1686_;
goto v___jp_1654_;
}
else
{
lean_object* v_val_1688_; 
v_val_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_val_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___y_1655_ = v___y_1679_;
v___y_1656_ = v___y_1681_;
v___y_1657_ = v___y_1682_;
v___y_1658_ = v___y_1683_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v___y_1685_;
v___y_1661_ = v___y_1684_;
v___y_1662_ = v_val_1688_;
goto v___jp_1654_;
}
}
v___jp_1689_:
{
lean_object* v_ref_1697_; lean_object* v___x_1698_; 
v_ref_1697_ = l_Lean_replaceRef(v_ref_1607_, v___y_1692_);
v___x_1698_ = l_Lean_Syntax_getPos_x3f(v_ref_1697_, v___y_1693_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_unsigned_to_nat(0u);
v___y_1679_ = v___y_1690_;
v___y_1680_ = v_ref_1697_;
v___y_1681_ = v___y_1691_;
v___y_1682_ = v___y_1696_;
v___y_1683_ = v___y_1693_;
v___y_1684_ = v___y_1695_;
v___y_1685_ = v___y_1694_;
v___y_1686_ = v___x_1699_;
goto v___jp_1678_;
}
else
{
lean_object* v_val_1700_; 
v_val_1700_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v___x_1698_, 1);
v___y_1679_ = v___y_1690_;
v___y_1680_ = v_ref_1697_;
v___y_1681_ = v___y_1691_;
v___y_1682_ = v___y_1696_;
v___y_1683_ = v___y_1693_;
v___y_1684_ = v___y_1695_;
v___y_1685_ = v___y_1694_;
v___y_1686_ = v_val_1700_;
goto v___jp_1678_;
}
}
v___jp_1702_:
{
if (v___y_1709_ == 0)
{
v___y_1690_ = v___y_1705_;
v___y_1691_ = v___y_1703_;
v___y_1692_ = v___y_1704_;
v___y_1693_ = v___y_1708_;
v___y_1694_ = v___y_1707_;
v___y_1695_ = v___y_1706_;
v___y_1696_ = v_severity_1609_;
goto v___jp_1689_;
}
else
{
v___y_1690_ = v___y_1705_;
v___y_1691_ = v___y_1703_;
v___y_1692_ = v___y_1704_;
v___y_1693_ = v___y_1708_;
v___y_1694_ = v___y_1707_;
v___y_1695_ = v___y_1706_;
v___y_1696_ = v___x_1701_;
goto v___jp_1689_;
}
}
v___jp_1710_:
{
if (v___y_1711_ == 0)
{
lean_object* v_fileName_1712_; lean_object* v_fileMap_1713_; lean_object* v_options_1714_; lean_object* v_ref_1715_; uint8_t v_suppressElabErrors_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___f_1719_; uint8_t v___x_1720_; uint8_t v___x_1721_; 
v_fileName_1712_ = lean_ctor_get(v___y_1612_, 0);
v_fileMap_1713_ = lean_ctor_get(v___y_1612_, 1);
v_options_1714_ = lean_ctor_get(v___y_1612_, 2);
v_ref_1715_ = lean_ctor_get(v___y_1612_, 5);
v_suppressElabErrors_1716_ = lean_ctor_get_uint8(v___y_1612_, sizeof(void*)*14 + 1);
v___x_1717_ = lean_box(v___y_1711_);
v___x_1718_ = lean_box(v_suppressElabErrors_1716_);
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1719_, 0, v___x_1717_);
lean_closure_set(v___f_1719_, 1, v___x_1718_);
v___x_1720_ = 1;
v___x_1721_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1609_, v___x_1720_);
if (v___x_1721_ == 0)
{
v___y_1703_ = v_suppressElabErrors_1716_;
v___y_1704_ = v_ref_1715_;
v___y_1705_ = v___f_1719_;
v___y_1706_ = v_fileMap_1713_;
v___y_1707_ = v_fileName_1712_;
v___y_1708_ = v___y_1711_;
v___y_1709_ = v___x_1721_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = l_Lean_warningAsError;
v___x_1723_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_options_1714_, v___x_1722_);
v___y_1703_ = v_suppressElabErrors_1716_;
v___y_1704_ = v_ref_1715_;
v___y_1705_ = v___f_1719_;
v___y_1706_ = v_fileMap_1713_;
v___y_1707_ = v_fileName_1712_;
v___y_1708_ = v___y_1711_;
v___y_1709_ = v___x_1723_;
goto v___jp_1702_;
}
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_dec_ref(v_msgData_1608_);
v___x_1724_ = lean_box(0);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
lean_ctor_set(v___x_1725_, 1, v___y_1611_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1729_, lean_object* v_msgData_1730_, lean_object* v_severity_1731_, lean_object* v_isSilent_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v_severity_boxed_1737_; uint8_t v_isSilent_boxed_1738_; lean_object* v_res_1739_; 
v_severity_boxed_1737_ = lean_unbox(v_severity_1731_);
v_isSilent_boxed_1738_ = lean_unbox(v_isSilent_1732_);
v_res_1739_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1729_, v_msgData_1730_, v_severity_boxed_1737_, v_isSilent_boxed_1738_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v_ref_1729_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1740_, lean_object* v_msgData_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v___x_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = 2;
v___x_1747_ = 0;
v___x_1748_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1740_, v_msgData_1741_, v___x_1746_, v___x_1747_, v___y_1742_, v___y_1743_, v___y_1744_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1749_, lean_object* v_msgData_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1749_, v_msgData_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v_ref_1749_);
return v_res_1755_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1759_ = l_Lean_MessageData_ofFormat(v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1760_, lean_object* v_as_1761_, size_t v_sz_1762_, size_t v_i_1763_, uint8_t v_b_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_snd_1770_; lean_object* v_snd_1771_; lean_object* v___y_1777_; uint8_t v___y_1778_; lean_object* v_a_1795_; uint8_t v___x_1798_; 
v___x_1798_ = lean_usize_dec_lt(v_i_1763_, v_sz_1762_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_box(v_b_1764_);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___y_1765_);
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
return v___x_1801_;
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1803_; uint8_t v_recovering_1804_; 
v_a_1802_ = lean_array_uget_borrowed(v_as_1761_, v_i_1763_);
v___x_1803_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1802_);
v_recovering_1804_ = l_Lean_Syntax_isOfKind(v_a_1802_, v___x_1803_);
if (v_recovering_1804_ == 0)
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_a_1802_);
v___x_1806_ = l_Lean_Syntax_isOfKind(v_a_1802_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1802_);
v___x_1808_ = l_Lean_Syntax_isOfKind(v_a_1802_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1765_);
v___x_1810_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1802_, v___x_1809_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v_snd_1812_; lean_object* v___x_1813_; 
lean_dec_ref(v___y_1765_);
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v_snd_1812_ = lean_ctor_get(v_a_1811_, 1);
lean_inc(v_snd_1812_);
lean_dec(v_a_1811_);
v___x_1813_ = lean_box(v_b_1764_);
v_snd_1770_ = v___x_1813_;
v_snd_1771_ = v_snd_1812_;
goto v___jp_1769_;
}
else
{
lean_object* v_a_1814_; 
v_a_1814_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1810_, 1);
v_a_1795_ = v_a_1814_;
goto v___jp_1794_;
}
}
else
{
lean_object* v___x_1815_; 
lean_inc_ref(v___y_1765_);
lean_inc(v_a_1802_);
v___x_1815_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1802_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v_snd_1817_; lean_object* v___x_1818_; 
lean_dec_ref(v___y_1765_);
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1815_, 1);
v_snd_1817_ = lean_ctor_get(v_a_1816_, 1);
lean_inc(v_snd_1817_);
lean_dec(v_a_1816_);
v___x_1818_ = lean_box(v_recovering_1804_);
v_snd_1770_ = v___x_1818_;
v_snd_1771_ = v_snd_1817_;
goto v___jp_1769_;
}
else
{
lean_object* v_a_1819_; 
v_a_1819_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1815_, 1);
v_a_1795_ = v_a_1819_;
goto v___jp_1794_;
}
}
}
else
{
lean_object* v___x_1820_; 
lean_inc_ref(v___y_1765_);
lean_inc(v_a_1802_);
v___x_1820_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1802_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v_snd_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v___y_1765_);
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v_snd_1822_ = lean_ctor_get(v_a_1821_, 1);
lean_inc(v_snd_1822_);
lean_dec(v_a_1821_);
v___x_1823_ = lean_box(v_recovering_1804_);
v_snd_1770_ = v___x_1823_;
v_snd_1771_ = v_snd_1822_;
goto v___jp_1769_;
}
else
{
lean_object* v_a_1824_; 
v_a_1824_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1820_, 1);
v_a_1795_ = v_a_1824_;
goto v___jp_1794_;
}
}
}
else
{
if (v_b_1764_ == 0)
{
lean_object* v___x_1825_; 
lean_inc_ref(v___y_1765_);
lean_inc(v_a_1802_);
v___x_1825_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1802_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v_snd_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v___y_1765_);
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v_snd_1827_ = lean_ctor_get(v_a_1826_, 1);
lean_inc(v_snd_1827_);
lean_dec(v_a_1826_);
v___x_1828_ = lean_box(v_b_1764_);
v_snd_1770_ = v___x_1828_;
v_snd_1771_ = v_snd_1827_;
goto v___jp_1769_;
}
else
{
lean_object* v_a_1829_; 
v_a_1829_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1825_, 1);
v_a_1795_ = v_a_1829_;
goto v___jp_1794_;
}
}
else
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_box(v_b_1764_);
v_snd_1770_ = v___x_1830_;
v_snd_1771_ = v___y_1765_;
goto v___jp_1769_;
}
}
}
v___jp_1769_:
{
size_t v___x_1772_; size_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = ((size_t)1ULL);
v___x_1773_ = lean_usize_add(v_i_1763_, v___x_1772_);
v___x_1774_ = lean_unbox(v_snd_1770_);
lean_dec(v_snd_1770_);
v_i_1763_ = v___x_1773_;
v_b_1764_ = v___x_1774_;
v___y_1765_ = v_snd_1771_;
goto _start;
}
v___jp_1776_:
{
if (v___y_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = l_Lean_Exception_getRef(v___y_1777_);
v___x_1780_ = l_Lean_Exception_toMessageData(v___y_1777_);
v___x_1781_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1779_, v___x_1780_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___x_1779_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v_snd_1783_; lean_object* v___x_1784_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v_snd_1783_ = lean_ctor_get(v_a_1782_, 1);
lean_inc(v_snd_1783_);
lean_dec(v_a_1782_);
v___x_1784_ = lean_box(v_recovering_1760_);
v_snd_1770_ = v___x_1784_;
v_snd_1771_ = v_snd_1783_;
goto v___jp_1769_;
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
v_a_1785_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1781_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1781_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v___x_1793_; 
lean_dec_ref(v___y_1765_);
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___y_1777_);
return v___x_1793_;
}
}
v___jp_1794_:
{
uint8_t v___x_1796_; 
v___x_1796_ = l_Lean_Exception_isInterrupt(v_a_1795_);
if (v___x_1796_ == 0)
{
uint8_t v___x_1797_; 
lean_inc_ref(v_a_1795_);
v___x_1797_ = l_Lean_Exception_isRuntime(v_a_1795_);
v___y_1777_ = v_a_1795_;
v___y_1778_ = v___x_1797_;
goto v___jp_1776_;
}
else
{
v___y_1777_ = v_a_1795_;
v___y_1778_ = v___x_1796_;
goto v___jp_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1831_, lean_object* v_as_1832_, lean_object* v_sz_1833_, lean_object* v_i_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v_recovering_boxed_1840_; size_t v_sz_boxed_1841_; size_t v_i_boxed_1842_; uint8_t v_b_boxed_1843_; lean_object* v_res_1844_; 
v_recovering_boxed_1840_ = lean_unbox(v_recovering_1831_);
v_sz_boxed_1841_ = lean_unbox_usize(v_sz_1833_);
lean_dec(v_sz_1833_);
v_i_boxed_1842_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_b_boxed_1843_ = lean_unbox(v_b_1835_);
v_res_1844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1840_, v_as_1832_, v_sz_boxed_1841_, v_i_boxed_1842_, v_b_boxed_1843_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec_ref(v_as_1832_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_ref_1849_; lean_object* v___x_1850_; lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_ref_1849_ = lean_ctor_get(v___y_1846_, 5);
v___x_1850_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1845_, v___y_1846_, v___y_1847_);
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_inc(v_ref_1849_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_ref_1849_);
lean_ctor_set(v___x_1855_, 1, v_a_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 1);
lean_ctor_set(v___x_1853_, 0, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1865_, lean_object* v_msg_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_fileName_1870_; lean_object* v_fileMap_1871_; lean_object* v_options_1872_; lean_object* v_currRecDepth_1873_; lean_object* v_maxRecDepth_1874_; lean_object* v_ref_1875_; lean_object* v_currNamespace_1876_; lean_object* v_openDecls_1877_; lean_object* v_initHeartbeats_1878_; lean_object* v_maxHeartbeats_1879_; lean_object* v_quotContext_1880_; lean_object* v_currMacroScope_1881_; uint8_t v_diag_1882_; lean_object* v_cancelTk_x3f_1883_; uint8_t v_suppressElabErrors_1884_; lean_object* v_inheritedTraceOptions_1885_; lean_object* v_ref_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_fileName_1870_ = lean_ctor_get(v___y_1867_, 0);
v_fileMap_1871_ = lean_ctor_get(v___y_1867_, 1);
v_options_1872_ = lean_ctor_get(v___y_1867_, 2);
v_currRecDepth_1873_ = lean_ctor_get(v___y_1867_, 3);
v_maxRecDepth_1874_ = lean_ctor_get(v___y_1867_, 4);
v_ref_1875_ = lean_ctor_get(v___y_1867_, 5);
v_currNamespace_1876_ = lean_ctor_get(v___y_1867_, 6);
v_openDecls_1877_ = lean_ctor_get(v___y_1867_, 7);
v_initHeartbeats_1878_ = lean_ctor_get(v___y_1867_, 8);
v_maxHeartbeats_1879_ = lean_ctor_get(v___y_1867_, 9);
v_quotContext_1880_ = lean_ctor_get(v___y_1867_, 10);
v_currMacroScope_1881_ = lean_ctor_get(v___y_1867_, 11);
v_diag_1882_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*14);
v_cancelTk_x3f_1883_ = lean_ctor_get(v___y_1867_, 12);
v_suppressElabErrors_1884_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1885_ = lean_ctor_get(v___y_1867_, 13);
v_ref_1886_ = l_Lean_replaceRef(v_ref_1865_, v_ref_1875_);
lean_inc_ref(v_inheritedTraceOptions_1885_);
lean_inc(v_cancelTk_x3f_1883_);
lean_inc(v_currMacroScope_1881_);
lean_inc(v_quotContext_1880_);
lean_inc(v_maxHeartbeats_1879_);
lean_inc(v_initHeartbeats_1878_);
lean_inc(v_openDecls_1877_);
lean_inc(v_currNamespace_1876_);
lean_inc(v_maxRecDepth_1874_);
lean_inc(v_currRecDepth_1873_);
lean_inc_ref(v_options_1872_);
lean_inc_ref(v_fileMap_1871_);
lean_inc_ref(v_fileName_1870_);
v___x_1887_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1887_, 0, v_fileName_1870_);
lean_ctor_set(v___x_1887_, 1, v_fileMap_1871_);
lean_ctor_set(v___x_1887_, 2, v_options_1872_);
lean_ctor_set(v___x_1887_, 3, v_currRecDepth_1873_);
lean_ctor_set(v___x_1887_, 4, v_maxRecDepth_1874_);
lean_ctor_set(v___x_1887_, 5, v_ref_1886_);
lean_ctor_set(v___x_1887_, 6, v_currNamespace_1876_);
lean_ctor_set(v___x_1887_, 7, v_openDecls_1877_);
lean_ctor_set(v___x_1887_, 8, v_initHeartbeats_1878_);
lean_ctor_set(v___x_1887_, 9, v_maxHeartbeats_1879_);
lean_ctor_set(v___x_1887_, 10, v_quotContext_1880_);
lean_ctor_set(v___x_1887_, 11, v_currMacroScope_1881_);
lean_ctor_set(v___x_1887_, 12, v_cancelTk_x3f_1883_);
lean_ctor_set(v___x_1887_, 13, v_inheritedTraceOptions_1885_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*14, v_diag_1882_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*14 + 1, v_suppressElabErrors_1884_);
v___x_1888_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1866_, v___x_1887_, v___y_1868_);
lean_dec_ref_known(v___x_1887_, 14);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1889_, lean_object* v_msg_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1889_, v_msg_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v_ref_1889_);
return v_res_1894_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1902_ = l_Lean_stringToMessageData(v___x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1907_);
v___x_1912_ = l_Lean_Syntax_isOfKind(v_x_1907_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1914_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1907_, v___x_1913_, v_a_1908_, v_a_1909_);
lean_dec(v_x_1907_);
return v___x_1914_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v_recovering_1918_; 
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = l_Lean_Syntax_getArg(v_x_1907_, v___x_1915_);
v___x_1917_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1918_ = l_Lean_Syntax_isOfKind(v___x_1916_, v___x_1917_);
if (v_recovering_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1920_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1907_, v___x_1919_, v_a_1908_, v_a_1909_);
lean_dec(v_x_1907_);
return v___x_1920_;
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v_xs_1923_; uint8_t v_recovering_1924_; lean_object* v___x_1925_; size_t v_sz_1926_; size_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1921_ = lean_unsigned_to_nat(1u);
v___x_1922_ = l_Lean_Syntax_getArg(v_x_1907_, v___x_1921_);
lean_dec(v_x_1907_);
v_xs_1923_ = l_Lean_Syntax_getArgs(v___x_1922_);
lean_dec(v___x_1922_);
v_recovering_1924_ = 0;
v___x_1925_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1923_);
lean_dec_ref(v_xs_1923_);
v_sz_1926_ = lean_array_size(v___x_1925_);
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1918_, v___x_1925_, v_sz_1926_, v___x_1927_, v_recovering_1924_, v___x_1928_, v_a_1908_, v_a_1909_);
lean_dec_ref(v___x_1925_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1940_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v_snd_1934_; lean_object* v_items_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v_snd_1934_ = lean_ctor_get(v_a_1930_, 1);
lean_inc(v_snd_1934_);
lean_dec(v_a_1930_);
v_items_1935_ = lean_ctor_get(v_snd_1934_, 5);
lean_inc_ref(v_items_1935_);
lean_dec(v_snd_1934_);
v___x_1936_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1935_);
lean_dec_ref(v_items_1935_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1936_);
v___x_1938_ = v___x_1932_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v_a_1941_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1929_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1929_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lake_Toml_elabToml(v_x_1949_, v_a_1950_, v_a_1951_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1954_, lean_object* v_ref_1955_, lean_object* v_msg_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1955_, v_msg_1956_, v___y_1957_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_ref_1962_, lean_object* v_msg_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1961_, v_ref_1962_, v_msg_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v_ref_1962_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1968_, lean_object* v_msg_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1969_, v___y_1970_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_msg_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1974_, v_msg_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1979_;
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
