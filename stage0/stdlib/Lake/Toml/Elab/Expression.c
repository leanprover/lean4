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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx(uint8_t v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(v_x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx___boxed(lean_object* v_x_12_){
_start:
{
uint8_t v_x_4__boxed_13_; lean_object* v_res_14_; 
v_x_4__boxed_13_ = lean_unbox(v_x_12_);
v_res_14_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx(v_x_4__boxed_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg___boxed(lean_object* v_k_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(v_k_16_);
lean_dec(v_k_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, uint8_t v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_inc(v_k_22_);
return v_k_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___boxed(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
uint8_t v_t_boxed_28_; lean_object* v_res_29_; 
v_t_boxed_28_ = lean_unbox(v_t_25_);
v_res_29_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(v_motive_23_, v_ctorIdx_24_, v_t_boxed_28_, v_h_26_, v_k_27_);
lean_dec(v_k_27_);
lean_dec(v_ctorIdx_24_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(lean_object* v_value_30_){
_start:
{
lean_inc(v_value_30_);
return v_value_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg___boxed(lean_object* v_value_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(v_value_31_);
lean_dec(v_value_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(lean_object* v_motive_33_, uint8_t v_t_34_, lean_object* v_h_35_, lean_object* v_value_36_){
_start:
{
lean_inc(v_value_36_);
return v_value_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___boxed(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_value_40_){
_start:
{
uint8_t v_t_boxed_41_; lean_object* v_res_42_; 
v_t_boxed_41_ = lean_unbox(v_t_38_);
v_res_42_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(v_motive_37_, v_t_boxed_41_, v_h_39_, v_value_40_);
lean_dec(v_value_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(lean_object* v_stdTable_43_){
_start:
{
lean_inc(v_stdTable_43_);
return v_stdTable_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg___boxed(lean_object* v_stdTable_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(v_stdTable_44_);
lean_dec(v_stdTable_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(lean_object* v_motive_46_, uint8_t v_t_47_, lean_object* v_h_48_, lean_object* v_stdTable_49_){
_start:
{
lean_inc(v_stdTable_49_);
return v_stdTable_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___boxed(lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_stdTable_53_){
_start:
{
uint8_t v_t_boxed_54_; lean_object* v_res_55_; 
v_t_boxed_54_ = lean_unbox(v_t_51_);
v_res_55_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(v_motive_50_, v_t_boxed_54_, v_h_52_, v_stdTable_53_);
lean_dec(v_stdTable_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(lean_object* v_array_56_){
_start:
{
lean_inc(v_array_56_);
return v_array_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg___boxed(lean_object* v_array_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(v_array_57_);
lean_dec(v_array_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(lean_object* v_motive_59_, uint8_t v_t_60_, lean_object* v_h_61_, lean_object* v_array_62_){
_start:
{
lean_inc(v_array_62_);
return v_array_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___boxed(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_array_66_){
_start:
{
uint8_t v_t_boxed_67_; lean_object* v_res_68_; 
v_t_boxed_67_ = lean_unbox(v_t_64_);
v_res_68_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(v_motive_63_, v_t_boxed_67_, v_h_65_, v_array_66_);
lean_dec(v_array_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(lean_object* v_dottedPrefix_69_){
_start:
{
lean_inc(v_dottedPrefix_69_);
return v_dottedPrefix_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg___boxed(lean_object* v_dottedPrefix_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(v_dottedPrefix_70_);
lean_dec(v_dottedPrefix_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(lean_object* v_motive_72_, uint8_t v_t_73_, lean_object* v_h_74_, lean_object* v_dottedPrefix_75_){
_start:
{
lean_inc(v_dottedPrefix_75_);
return v_dottedPrefix_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___boxed(lean_object* v_motive_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_dottedPrefix_79_){
_start:
{
uint8_t v_t_boxed_80_; lean_object* v_res_81_; 
v_t_boxed_80_ = lean_unbox(v_t_77_);
v_res_81_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(v_motive_76_, v_t_boxed_80_, v_h_78_, v_dottedPrefix_79_);
lean_dec(v_dottedPrefix_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(lean_object* v_headerPrefix_82_){
_start:
{
lean_inc(v_headerPrefix_82_);
return v_headerPrefix_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg___boxed(lean_object* v_headerPrefix_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(v_headerPrefix_83_);
lean_dec(v_headerPrefix_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(lean_object* v_motive_85_, uint8_t v_t_86_, lean_object* v_h_87_, lean_object* v_headerPrefix_88_){
_start:
{
lean_inc(v_headerPrefix_88_);
return v_headerPrefix_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___boxed(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_headerPrefix_92_){
_start:
{
uint8_t v_t_boxed_93_; lean_object* v_res_94_; 
v_t_boxed_93_ = lean_unbox(v_t_90_);
v_res_94_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(v_motive_89_, v_t_boxed_93_, v_h_91_, v_headerPrefix_92_);
lean_dec(v_headerPrefix_92_);
return v_res_94_;
}
}
static uint8_t _init_l_Lake_Toml_instInhabitedKeyTy_default(void){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
static uint8_t _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy(void){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(uint8_t v_ty_102_){
_start:
{
switch(v_ty_102_)
{
case 0:
{
lean_object* v___x_103_; 
v___x_103_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0));
return v___x_103_;
}
case 1:
{
lean_object* v___x_104_; 
v___x_104_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1));
return v___x_104_;
}
case 2:
{
lean_object* v___x_105_; 
v___x_105_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2));
return v___x_105_;
}
case 3:
{
lean_object* v___x_106_; 
v___x_106_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3));
return v___x_106_;
}
default: 
{
lean_object* v___x_107_; 
v___x_107_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4));
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed(lean_object* v_ty_108_){
_start:
{
uint8_t v_ty_boxed_109_; lean_object* v_res_110_; 
v_ty_boxed_109_ = lean_unbox(v_ty_108_);
v_res_110_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v_ty_boxed_109_);
return v_res_110_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(uint8_t v_ty_113_){
_start:
{
switch(v_ty_113_)
{
case 1:
{
uint8_t v___x_114_; 
v___x_114_ = 1;
return v___x_114_;
}
case 4:
{
uint8_t v___x_115_; 
v___x_115_ = 1;
return v___x_115_;
}
case 3:
{
uint8_t v___x_116_; 
v___x_116_ = 1;
return v___x_116_;
}
default: 
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix___boxed(lean_object* v_ty_118_){
_start:
{
uint8_t v_ty_boxed_119_; uint8_t v_res_120_; lean_object* v_r_121_; 
v_ty_boxed_119_ = lean_unbox(v_ty_118_);
v_res_120_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(v_ty_boxed_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
lean_ctor_set(v___x_135_, 2, v___x_134_);
lean_ctor_set(v___x_135_, 3, v___x_134_);
lean_ctor_set(v___x_135_, 4, v___x_133_);
lean_ctor_set(v___x_135_, 5, v___x_133_);
lean_ctor_set(v___x_135_, 6, v___x_133_);
lean_ctor_set(v___x_135_, 7, v___x_133_);
lean_ctor_set(v___x_135_, 8, v___x_133_);
lean_ctor_set(v___x_135_, 9, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_unsigned_to_nat(32u);
v___x_137_ = lean_mk_empty_array_with_capacity(v___x_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_139_ = ((size_t)5ULL);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_unsigned_to_nat(32u);
v___x_142_ = lean_mk_empty_array_with_capacity(v___x_141_);
v___x_143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3);
v___x_144_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
lean_ctor_set(v___x_144_, 2, v___x_140_);
lean_ctor_set(v___x_144_, 3, v___x_140_);
lean_ctor_set_usize(v___x_144_, 4, v___x_139_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = lean_box(1);
v___x_146_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4);
v___x_147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_145_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(lean_object* v_msgData_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; lean_object* v_env_154_; lean_object* v_options_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_153_ = lean_st_ref_get(v___y_151_);
v_env_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc_ref(v_env_154_);
lean_dec(v___x_153_);
v_options_155_ = lean_ctor_get(v___y_150_, 2);
v___x_156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2);
v___x_157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_155_);
v___x_158_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_158_, 0, v_env_154_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
lean_ctor_set(v___x_158_, 3, v_options_155_);
v___x_159_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v_msgData_149_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msgData_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_ref_170_; lean_object* v___x_171_; lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_180_; 
v_ref_170_ = lean_ctor_get(v___y_167_, 5);
v___x_171_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_166_, v___y_167_, v___y_168_);
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_180_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_180_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_180_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_178_; 
lean_inc(v_ref_170_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v_ref_170_);
lean_ctor_set(v___x_176_, 1, v_a_172_);
if (v_isShared_175_ == 0)
{
lean_ctor_set_tag(v___x_174_, 1);
lean_ctor_set(v___x_174_, 0, v___x_176_);
v___x_178_ = v___x_174_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg___boxed(lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(lean_object* v_ref_186_, lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_fileName_192_; lean_object* v_fileMap_193_; lean_object* v_options_194_; lean_object* v_currRecDepth_195_; lean_object* v_maxRecDepth_196_; lean_object* v_ref_197_; lean_object* v_currNamespace_198_; lean_object* v_openDecls_199_; lean_object* v_initHeartbeats_200_; lean_object* v_maxHeartbeats_201_; lean_object* v_quotContext_202_; lean_object* v_currMacroScope_203_; uint8_t v_diag_204_; lean_object* v_cancelTk_x3f_205_; uint8_t v_suppressElabErrors_206_; lean_object* v_inheritedTraceOptions_207_; lean_object* v_ref_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_fileName_192_ = lean_ctor_get(v___y_189_, 0);
v_fileMap_193_ = lean_ctor_get(v___y_189_, 1);
v_options_194_ = lean_ctor_get(v___y_189_, 2);
v_currRecDepth_195_ = lean_ctor_get(v___y_189_, 3);
v_maxRecDepth_196_ = lean_ctor_get(v___y_189_, 4);
v_ref_197_ = lean_ctor_get(v___y_189_, 5);
v_currNamespace_198_ = lean_ctor_get(v___y_189_, 6);
v_openDecls_199_ = lean_ctor_get(v___y_189_, 7);
v_initHeartbeats_200_ = lean_ctor_get(v___y_189_, 8);
v_maxHeartbeats_201_ = lean_ctor_get(v___y_189_, 9);
v_quotContext_202_ = lean_ctor_get(v___y_189_, 10);
v_currMacroScope_203_ = lean_ctor_get(v___y_189_, 11);
v_diag_204_ = lean_ctor_get_uint8(v___y_189_, sizeof(void*)*14);
v_cancelTk_x3f_205_ = lean_ctor_get(v___y_189_, 12);
v_suppressElabErrors_206_ = lean_ctor_get_uint8(v___y_189_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_207_ = lean_ctor_get(v___y_189_, 13);
v_ref_208_ = l_Lean_replaceRef(v_ref_186_, v_ref_197_);
lean_inc_ref(v_inheritedTraceOptions_207_);
lean_inc(v_cancelTk_x3f_205_);
lean_inc(v_currMacroScope_203_);
lean_inc(v_quotContext_202_);
lean_inc(v_maxHeartbeats_201_);
lean_inc(v_initHeartbeats_200_);
lean_inc(v_openDecls_199_);
lean_inc(v_currNamespace_198_);
lean_inc(v_maxRecDepth_196_);
lean_inc(v_currRecDepth_195_);
lean_inc_ref(v_options_194_);
lean_inc_ref(v_fileMap_193_);
lean_inc_ref(v_fileName_192_);
v___x_209_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_209_, 0, v_fileName_192_);
lean_ctor_set(v___x_209_, 1, v_fileMap_193_);
lean_ctor_set(v___x_209_, 2, v_options_194_);
lean_ctor_set(v___x_209_, 3, v_currRecDepth_195_);
lean_ctor_set(v___x_209_, 4, v_maxRecDepth_196_);
lean_ctor_set(v___x_209_, 5, v_ref_208_);
lean_ctor_set(v___x_209_, 6, v_currNamespace_198_);
lean_ctor_set(v___x_209_, 7, v_openDecls_199_);
lean_ctor_set(v___x_209_, 8, v_initHeartbeats_200_);
lean_ctor_set(v___x_209_, 9, v_maxHeartbeats_201_);
lean_ctor_set(v___x_209_, 10, v_quotContext_202_);
lean_ctor_set(v___x_209_, 11, v_currMacroScope_203_);
lean_ctor_set(v___x_209_, 12, v_cancelTk_x3f_205_);
lean_ctor_set(v___x_209_, 13, v_inheritedTraceOptions_207_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*14, v_diag_204_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*14 + 1, v_suppressElabErrors_206_);
v___x_210_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_187_, v___x_209_, v___y_190_);
lean_dec_ref(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object* v_ref_211_, lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_211_, v_msg_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v_ref_211_);
return v_res_217_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_223_ = l_Lean_stringToMessageData(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_226_ = l_Lean_stringToMessageData(v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object* v_as_227_, size_t v_i_228_, size_t v_stop_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_fst_236_; lean_object* v_snd_237_; uint8_t v___x_241_; 
v___x_241_ = lean_usize_dec_eq(v_i_228_, v_stop_229_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_array_uget_borrowed(v_as_227_, v_i_228_);
lean_inc(v___x_242_);
v___x_243_ = l_Lake_Toml_elabSimpleKey(v___x_242_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v_keyTys_245_; lean_object* v_arrKeyTys_246_; lean_object* v_arrParents_247_; lean_object* v_currArrKey_248_; lean_object* v_currKey_249_; lean_object* v_items_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref(v___x_243_);
v_keyTys_245_ = lean_ctor_get(v___y_231_, 0);
v_arrKeyTys_246_ = lean_ctor_get(v___y_231_, 1);
v_arrParents_247_ = lean_ctor_get(v___y_231_, 2);
v_currArrKey_248_ = lean_ctor_get(v___y_231_, 3);
v_currKey_249_ = lean_ctor_get(v___y_231_, 4);
v_items_250_ = lean_ctor_get(v___y_231_, 5);
v___x_251_ = l_Lean_Name_str___override(v_b_230_, v_a_244_);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_245_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 1)
{
lean_object* v_val_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_283_; 
v_val_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_283_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_283_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_val_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_283_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; 
v___x_257_ = lean_unbox(v_val_253_);
if (v___x_257_ == 3)
{
lean_del_object(v___x_255_);
lean_dec(v_val_253_);
v_fst_236_ = v___x_251_;
v_snd_237_ = v___y_231_;
goto v___jp_235_;
}
else
{
lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_258_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_259_ = lean_unbox(v_val_253_);
lean_dec(v_val_253_);
v___x_260_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_259_);
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 3);
lean_ctor_set(v___x_255_, 0, v___x_260_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_282_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_263_ = l_Lean_MessageData_ofFormat(v___x_262_);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_258_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
lean_inc(v___x_251_);
v___x_267_ = l_Lean_MessageData_ofName(v___x_251_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_242_, v___x_270_, v___y_231_, v___y_232_, v___y_233_);
lean_dec_ref(v___y_231_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_snd_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref(v___x_271_);
v_snd_273_ = lean_ctor_get(v_a_272_, 1);
lean_inc(v_snd_273_);
lean_dec(v_a_272_);
v_fst_236_ = v___x_251_;
v_snd_237_ = v_snd_273_;
goto v___jp_235_;
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec(v___x_251_);
v_a_274_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_271_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_271_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_293_; 
lean_inc_ref(v_items_250_);
lean_inc(v_currKey_249_);
lean_inc(v_currArrKey_248_);
lean_inc(v_arrParents_247_);
lean_inc(v_arrKeyTys_246_);
lean_inc(v_keyTys_245_);
lean_dec(v___x_252_);
v_isSharedCheck_293_ = !lean_is_exclusive(v___y_231_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_294_ = lean_ctor_get(v___y_231_, 5);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v___y_231_, 4);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v___y_231_, 3);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v___y_231_, 2);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v___y_231_, 1);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v___y_231_, 0);
lean_dec(v_unused_299_);
v___x_285_ = v___y_231_;
v_isShared_286_ = v_isSharedCheck_293_;
goto v_resetjp_284_;
}
else
{
lean_dec(v___y_231_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_293_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_287_ = 3;
v___x_288_ = lean_box(v___x_287_);
lean_inc(v___x_251_);
v___x_289_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_251_, v___x_288_, v_keyTys_245_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_289_);
v___x_291_ = v___x_285_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_arrKeyTys_246_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_arrParents_247_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_currArrKey_248_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v_currKey_249_);
lean_ctor_set(v_reuseFailAlloc_292_, 5, v_items_250_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
v_fst_236_ = v___x_251_;
v_snd_237_ = v___x_291_;
goto v___jp_235_;
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v___y_231_);
lean_dec(v_b_230_);
v_a_300_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_243_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_243_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_b_230_);
lean_ctor_set(v___x_308_, 1, v___y_231_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
v___jp_235_:
{
size_t v___x_238_; size_t v___x_239_; 
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_add(v_i_228_, v___x_238_);
v_i_228_ = v___x_239_;
v_b_230_ = v_fst_236_;
v___y_231_ = v_snd_237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object* v_as_310_, lean_object* v_i_311_, lean_object* v_stop_312_, lean_object* v_b_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
size_t v_i_boxed_318_; size_t v_stop_boxed_319_; lean_object* v_res_320_; 
v_i_boxed_318_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_stop_boxed_319_ = lean_unbox_usize(v_stop_312_);
lean_dec(v_stop_312_);
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_310_, v_i_boxed_318_, v_stop_boxed_319_, v_b_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec_ref(v_as_310_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object* v_ks_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_currKey_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_currKey_326_ = lean_ctor_get(v_a_322_, 4);
lean_inc(v_currKey_326_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_array_get_size(v_ks_321_);
v___x_329_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_currKey_326_);
lean_ctor_set(v___x_330_, 1, v_a_322_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = lean_nat_dec_le(v___x_328_, v___x_328_);
if (v___x_332_ == 0)
{
if (v___x_329_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_currKey_326_);
lean_ctor_set(v___x_333_, 1, v_a_322_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
else
{
size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v___x_335_ = ((size_t)0ULL);
v___x_336_ = lean_usize_of_nat(v___x_328_);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_321_, v___x_335_, v___x_336_, v_currKey_326_, v_a_322_, v_a_323_, v_a_324_);
return v___x_337_;
}
}
else
{
size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; 
v___x_338_ = ((size_t)0ULL);
v___x_339_ = lean_usize_of_nat(v___x_328_);
v___x_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_321_, v___x_338_, v___x_339_, v_currKey_326_, v_a_322_, v_a_323_, v_a_324_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object* v_ks_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec_ref(v_ks_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_347_, lean_object* v_ref_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_348_, v_msg_349_, v___y_350_, v___y_351_, v___y_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_355_, lean_object* v_ref_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_355_, v_ref_356_, v_msg_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v_ref_356_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_363_, lean_object* v_msg_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_364_, v___y_366_, v___y_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_370_, v_msg_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_377_, lean_object* v_as_378_, size_t v_i_379_, size_t v_stop_380_, lean_object* v_b_381_){
_start:
{
lean_object* v___y_383_; uint8_t v___x_387_; 
v___x_387_ = lean_usize_dec_eq(v_i_379_, v_stop_380_);
if (v___x_387_ == 0)
{
lean_object* v_fst_388_; uint8_t v___x_389_; 
v_fst_388_ = lean_ctor_get(v_b_381_, 0);
v___x_389_ = lean_unbox(v_fst_388_);
if (v___x_389_ == 0)
{
lean_object* v_snd_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_398_; 
v_snd_390_ = lean_ctor_get(v_b_381_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v_b_381_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v_b_381_, 0);
lean_dec(v_unused_399_);
v___x_392_ = v_b_381_;
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_snd_390_);
lean_dec(v_b_381_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_box(v___x_377_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_394_);
v___x_396_ = v___x_392_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_snd_390_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
v___y_383_ = v___x_396_;
goto v___jp_382_;
}
}
}
else
{
lean_object* v_snd_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_410_; 
v_snd_400_ = lean_ctor_get(v_b_381_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_b_381_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_b_381_, 0);
lean_dec(v_unused_411_);
v___x_402_ = v_b_381_;
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_snd_400_);
lean_dec(v_b_381_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_404_ = lean_array_uget_borrowed(v_as_378_, v_i_379_);
lean_inc(v___x_404_);
v___x_405_ = lean_array_push(v_snd_400_, v___x_404_);
v___x_406_ = lean_box(v___x_387_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v___x_405_);
lean_ctor_set(v___x_402_, 0, v___x_406_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_405_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
v___y_383_ = v___x_408_;
goto v___jp_382_;
}
}
}
}
else
{
return v_b_381_;
}
v___jp_382_:
{
size_t v___x_384_; size_t v___x_385_; 
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_379_, v___x_384_);
v_i_379_ = v___x_385_;
v_b_381_ = v___y_383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_412_, lean_object* v_as_413_, lean_object* v_i_414_, lean_object* v_stop_415_, lean_object* v_b_416_){
_start:
{
uint8_t v___x_4079__boxed_417_; size_t v_i_boxed_418_; size_t v_stop_boxed_419_; lean_object* v_res_420_; 
v___x_4079__boxed_417_ = lean_unbox(v___x_412_);
v_i_boxed_418_ = lean_unbox_usize(v_i_414_);
lean_dec(v_i_414_);
v_stop_boxed_419_ = lean_unbox_usize(v_stop_415_);
lean_dec(v_stop_415_);
v_res_420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_4079__boxed_417_, v_as_413_, v_i_boxed_418_, v_stop_boxed_419_, v_b_416_);
lean_dec_ref(v_as_413_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_428_, size_t v_i_429_, lean_object* v_bs_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_lt(v_i_429_, v_sz_428_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v_bs_430_);
return v___x_432_;
}
else
{
lean_object* v_v_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_v_433_ = lean_array_uget(v_bs_430_, v_i_429_);
v___x_434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_433_);
v___x_435_ = l_Lean_Syntax_isOfKind(v_v_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_dec(v_v_433_);
lean_dec_ref(v_bs_430_);
v___x_436_ = lean_box(0);
return v___x_436_;
}
else
{
lean_object* v___x_437_; lean_object* v_bs_x27_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v_bs_x27_438_ = lean_array_uset(v_bs_430_, v_i_429_, v___x_437_);
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_429_, v___x_439_);
v___x_441_ = lean_array_uset(v_bs_x27_438_, v_i_429_, v_v_433_);
v_i_429_ = v___x_440_;
v_bs_430_ = v___x_441_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_443_, lean_object* v_i_444_, lean_object* v_bs_445_){
_start:
{
size_t v_sz_boxed_446_; size_t v_i_boxed_447_; lean_object* v_res_448_; 
v_sz_boxed_446_ = lean_unbox_usize(v_sz_443_);
lean_dec(v_sz_443_);
v_i_boxed_447_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_446_, v_i_boxed_447_, v_bs_445_);
return v_res_448_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_464_ = l_Lean_stringToMessageData(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_467_);
v___x_473_ = l_Lean_Syntax_isOfKind(v_kv_467_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_475_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_467_, v___x_474_, v_a_468_, v_a_469_, v_a_470_);
lean_dec_ref(v_a_468_);
lean_dec(v_kv_467_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = l_Lean_Syntax_getArg(v_kv_467_, v___x_476_);
v___x_478_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_477_);
v___x_479_ = l_Lean_Syntax_isOfKind(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_kv_467_);
v___x_480_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_481_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_477_, v___x_480_, v_a_468_, v_a_469_, v_a_470_);
lean_dec_ref(v_a_468_);
lean_dec(v___x_477_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v_v_483_; lean_object* v___y_485_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_482_ = lean_unsigned_to_nat(2u);
v_v_483_ = l_Lean_Syntax_getArg(v_kv_467_, v___x_482_);
lean_dec(v_kv_467_);
v___x_591_ = l_Lean_Syntax_getArg(v___x_477_, v___x_476_);
v___x_592_ = l_Lean_Syntax_getArgs(v___x_591_);
lean_dec(v___x_591_);
v___x_593_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_594_ = lean_array_get_size(v___x_592_);
v___x_595_ = lean_nat_dec_lt(v___x_476_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec_ref(v___x_592_);
v___y_485_ = v___x_593_;
goto v___jp_484_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = lean_box(v___x_479_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_593_);
v___x_598_ = lean_nat_dec_le(v___x_594_, v___x_594_);
if (v___x_598_ == 0)
{
if (v___x_595_ == 0)
{
lean_dec_ref(v___x_597_);
lean_dec_ref(v___x_592_);
v___y_485_ = v___x_593_;
goto v___jp_484_;
}
else
{
size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; lean_object* v_snd_602_; 
v___x_599_ = ((size_t)0ULL);
v___x_600_ = lean_usize_of_nat(v___x_594_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_479_, v___x_592_, v___x_599_, v___x_600_, v___x_597_);
lean_dec_ref(v___x_592_);
v_snd_602_ = lean_ctor_get(v___x_601_, 1);
lean_inc(v_snd_602_);
lean_dec_ref(v___x_601_);
v___y_485_ = v_snd_602_;
goto v___jp_484_;
}
}
else
{
size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; lean_object* v_snd_606_; 
v___x_603_ = ((size_t)0ULL);
v___x_604_ = lean_usize_of_nat(v___x_594_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_479_, v___x_592_, v___x_603_, v___x_604_, v___x_597_);
lean_dec_ref(v___x_592_);
v_snd_606_ = lean_ctor_get(v___x_605_, 1);
lean_inc(v_snd_606_);
lean_dec_ref(v___x_605_);
v___y_485_ = v_snd_606_;
goto v___jp_484_;
}
}
v___jp_484_:
{
size_t v_sz_486_; size_t v___x_487_; lean_object* v___x_488_; 
v_sz_486_ = lean_array_size(v___y_485_);
v___x_487_ = ((size_t)0ULL);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_486_, v___x_487_, v___y_485_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_v_483_);
v___x_489_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_490_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_477_, v___x_489_, v_a_468_, v_a_469_, v_a_470_);
lean_dec_ref(v_a_468_);
lean_dec(v___x_477_);
return v___x_490_;
}
else
{
lean_object* v_val_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_tailKeyStx_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_val_491_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_val_491_);
lean_dec_ref(v___x_488_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_array_get_size(v_val_491_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_sub(v___x_493_, v___x_494_);
v_tailKeyStx_496_ = lean_array_get(v___x_492_, v_val_491_, v___x_495_);
lean_dec(v___x_495_);
v___x_497_ = lean_array_pop(v_val_491_);
v___x_498_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_497_, v_a_468_, v_a_469_, v_a_470_);
lean_dec_ref(v___x_497_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v_fst_500_; lean_object* v_snd_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_582_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
v_fst_500_ = lean_ctor_get(v_a_499_, 0);
v_snd_501_ = lean_ctor_get(v_a_499_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_a_499_);
if (v_isSharedCheck_582_ == 0)
{
v___x_503_ = v_a_499_;
v_isShared_504_ = v_isSharedCheck_582_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_snd_501_);
lean_inc(v_fst_500_);
lean_dec(v_a_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_582_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; 
lean_inc(v_tailKeyStx_496_);
v___x_505_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_496_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v_keyTys_507_; lean_object* v_arrKeyTys_508_; lean_object* v_arrParents_509_; lean_object* v_currArrKey_510_; lean_object* v_currKey_511_; lean_object* v_items_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
v_keyTys_507_ = lean_ctor_get(v_snd_501_, 0);
v_arrKeyTys_508_ = lean_ctor_get(v_snd_501_, 1);
v_arrParents_509_ = lean_ctor_get(v_snd_501_, 2);
v_currArrKey_510_ = lean_ctor_get(v_snd_501_, 3);
v_currKey_511_ = lean_ctor_get(v_snd_501_, 4);
v_items_512_ = lean_ctor_get(v_snd_501_, 5);
v___x_513_ = l_Lean_Name_str___override(v_fst_500_, v_a_506_);
v___x_514_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_507_, v___x_513_);
if (lean_obj_tag(v___x_514_) == 1)
{
lean_object* v_val_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_534_; 
lean_del_object(v___x_503_);
lean_dec(v_v_483_);
lean_dec(v___x_477_);
v_val_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_534_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_534_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_val_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_534_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_519_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_520_ = lean_unbox(v_val_515_);
lean_dec(v_val_515_);
v___x_521_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_520_);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 3);
lean_ctor_set(v___x_517_, 0, v___x_521_);
v___x_523_ = v___x_517_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_533_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_524_ = l_Lean_MessageData_ofFormat(v___x_523_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_519_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_MessageData_ofName(v___x_513_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_496_, v___x_531_, v_snd_501_, v_a_469_, v_a_470_);
lean_dec(v_snd_501_);
lean_dec(v_tailKeyStx_496_);
return v___x_532_;
}
}
}
else
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_567_; 
lean_inc_ref(v_items_512_);
lean_inc(v_currKey_511_);
lean_inc(v_currArrKey_510_);
lean_inc(v_arrParents_509_);
lean_inc(v_arrKeyTys_508_);
lean_inc(v_keyTys_507_);
lean_dec(v___x_514_);
lean_dec(v_tailKeyStx_496_);
v_isSharedCheck_567_ = !lean_is_exclusive(v_snd_501_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; 
v_unused_568_ = lean_ctor_get(v_snd_501_, 5);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_snd_501_, 4);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_snd_501_, 3);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_snd_501_, 2);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_snd_501_, 1);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_snd_501_, 0);
lean_dec(v_unused_573_);
v___x_536_ = v_snd_501_;
v_isShared_537_ = v_isSharedCheck_567_;
goto v_resetjp_535_;
}
else
{
lean_dec(v_snd_501_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_567_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lake_Toml_elabVal(v_v_483_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_558_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_558_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_558_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_558_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_543_ = lean_box(0);
v___x_544_ = 0;
v___x_545_ = lean_box(v___x_544_);
lean_inc(v___x_513_);
v___x_546_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_513_, v___x_545_, v_keyTys_507_);
v___x_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_547_, 0, v___x_477_);
lean_ctor_set(v___x_547_, 1, v___x_513_);
lean_ctor_set(v___x_547_, 2, v_a_539_);
v___x_548_ = lean_array_push(v_items_512_, v___x_547_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 5, v___x_548_);
lean_ctor_set(v___x_536_, 0, v___x_546_);
v___x_550_ = v___x_536_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_arrKeyTys_508_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_arrParents_509_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_currArrKey_510_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_currKey_511_);
lean_ctor_set(v_reuseFailAlloc_557_, 5, v___x_548_);
v___x_550_ = v_reuseFailAlloc_557_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_550_);
lean_ctor_set(v___x_503_, 0, v___x_543_);
v___x_552_ = v___x_503_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_552_);
v___x_554_ = v___x_541_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_del_object(v___x_536_);
lean_dec(v___x_513_);
lean_dec_ref(v_items_512_);
lean_dec(v_currKey_511_);
lean_dec(v_currArrKey_510_);
lean_dec(v_arrParents_509_);
lean_dec(v_arrKeyTys_508_);
lean_dec(v_keyTys_507_);
lean_del_object(v___x_503_);
lean_dec(v___x_477_);
v_a_559_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_538_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_538_);
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
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_del_object(v___x_503_);
lean_dec(v_snd_501_);
lean_dec(v_fst_500_);
lean_dec(v_tailKeyStx_496_);
lean_dec(v_v_483_);
lean_dec(v___x_477_);
v_a_574_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_505_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_505_);
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
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_tailKeyStx_496_);
lean_dec(v_v_483_);
lean_dec(v___x_477_);
v_a_583_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_498_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_498_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_607_, v_a_608_, v_a_609_, v_a_610_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
return v_res_612_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_615_ = l_Lean_stringToMessageData(v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_616_, size_t v_i_617_, size_t v_stop_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_fst_625_; lean_object* v_snd_626_; uint8_t v___x_630_; 
v___x_630_ = lean_usize_dec_eq(v_i_617_, v_stop_618_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_array_uget_borrowed(v_as_616_, v_i_617_);
lean_inc(v___x_631_);
v___x_632_ = l_Lake_Toml_elabSimpleKey(v___x_631_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v_keyTys_634_; lean_object* v_arrKeyTys_635_; lean_object* v_arrParents_636_; lean_object* v_currArrKey_637_; lean_object* v_currKey_638_; lean_object* v_items_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
v_keyTys_634_ = lean_ctor_get(v___y_620_, 0);
v_arrKeyTys_635_ = lean_ctor_get(v___y_620_, 1);
v_arrParents_636_ = lean_ctor_get(v___y_620_, 2);
v_currArrKey_637_ = lean_ctor_get(v___y_620_, 3);
v_currKey_638_ = lean_ctor_get(v___y_620_, 4);
v_items_639_ = lean_ctor_get(v___y_620_, 5);
v___x_640_ = l_Lean_Name_str___override(v_b_619_, v_a_633_);
v___x_641_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_634_, v___x_640_);
if (lean_obj_tag(v___x_641_) == 1)
{
lean_object* v_val_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_703_; 
v_val_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_703_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_703_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_val_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_703_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v___x_646_; 
v___x_646_ = lean_unbox(v_val_642_);
switch(v___x_646_)
{
case 2:
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_671_; 
lean_inc_ref(v_items_639_);
lean_inc(v_currKey_638_);
lean_inc(v_arrParents_636_);
lean_inc(v_arrKeyTys_635_);
lean_del_object(v___x_644_);
lean_dec(v_val_642_);
v_isSharedCheck_671_ = !lean_is_exclusive(v___y_620_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; lean_object* v_unused_673_; lean_object* v_unused_674_; lean_object* v_unused_675_; lean_object* v_unused_676_; lean_object* v_unused_677_; 
v_unused_672_ = lean_ctor_get(v___y_620_, 5);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v___y_620_, 4);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v___y_620_, 3);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v___y_620_, 2);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v___y_620_, 1);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v___y_620_, 0);
lean_dec(v_unused_677_);
v___x_648_ = v___y_620_;
v_isShared_649_ = v_isSharedCheck_671_;
goto v_resetjp_647_;
}
else
{
lean_dec(v___y_620_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_671_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_635_, v___x_640_);
if (lean_obj_tag(v___x_650_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_653_; 
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref(v___x_650_);
lean_inc(v___x_640_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 3, v___x_640_);
lean_ctor_set(v___x_648_, 0, v_val_651_);
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_val_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_arrKeyTys_635_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_arrParents_636_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v_currKey_638_);
lean_ctor_set(v_reuseFailAlloc_654_, 5, v_items_639_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
v_fst_625_ = v___x_640_;
v_snd_626_ = v___x_653_;
goto v___jp_624_;
}
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec(v___x_650_);
lean_del_object(v___x_648_);
lean_dec_ref(v_items_639_);
lean_dec(v_currKey_638_);
lean_dec(v_arrParents_636_);
lean_dec(v_arrKeyTys_635_);
v___x_655_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_640_);
v___x_656_ = l_Lean_MessageData_ofName(v___x_640_);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_659_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v_snd_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v___x_660_);
v_snd_662_ = lean_ctor_get(v_a_661_, 1);
lean_inc(v_snd_662_);
lean_dec(v_a_661_);
v_fst_625_ = v___x_640_;
v_snd_626_ = v_snd_662_;
goto v___jp_624_;
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v___x_640_);
v_a_663_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_660_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_660_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
case 1:
{
lean_del_object(v___x_644_);
lean_dec(v_val_642_);
v_fst_625_ = v___x_640_;
v_snd_626_ = v___y_620_;
goto v___jp_624_;
}
case 4:
{
lean_del_object(v___x_644_);
lean_dec(v_val_642_);
v_fst_625_ = v___x_640_;
v_snd_626_ = v___y_620_;
goto v___jp_624_;
}
case 3:
{
lean_del_object(v___x_644_);
lean_dec(v_val_642_);
v_fst_625_ = v___x_640_;
v_snd_626_ = v___y_620_;
goto v___jp_624_;
}
default: 
{
lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_678_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_679_ = lean_unbox(v_val_642_);
lean_dec(v_val_642_);
v___x_680_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_679_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 3);
lean_ctor_set(v___x_644_, 0, v___x_680_);
v___x_682_ = v___x_644_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_702_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_683_ = l_Lean_MessageData_ofFormat(v___x_682_);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_678_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
lean_inc(v___x_640_);
v___x_687_ = l_Lean_MessageData_ofName(v___x_640_);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_631_, v___x_690_, v___y_620_, v___y_621_, v___y_622_);
lean_dec_ref(v___y_620_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v_snd_693_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v___x_691_);
v_snd_693_ = lean_ctor_get(v_a_692_, 1);
lean_inc(v_snd_693_);
lean_dec(v_a_692_);
v_fst_625_ = v___x_640_;
v_snd_626_ = v_snd_693_;
goto v___jp_624_;
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec(v___x_640_);
v_a_694_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_691_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_691_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
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
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_713_; 
lean_inc_ref(v_items_639_);
lean_inc(v_currKey_638_);
lean_inc(v_currArrKey_637_);
lean_inc(v_arrParents_636_);
lean_inc(v_arrKeyTys_635_);
lean_inc(v_keyTys_634_);
lean_dec(v___x_641_);
v_isSharedCheck_713_ = !lean_is_exclusive(v___y_620_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; lean_object* v_unused_719_; 
v_unused_714_ = lean_ctor_get(v___y_620_, 5);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v___y_620_, 4);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v___y_620_, 3);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v___y_620_, 2);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v___y_620_, 1);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v___y_620_, 0);
lean_dec(v_unused_719_);
v___x_705_ = v___y_620_;
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
else
{
lean_dec(v___y_620_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_707_ = 4;
v___x_708_ = lean_box(v___x_707_);
lean_inc(v___x_640_);
v___x_709_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_640_, v___x_708_, v_keyTys_634_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_709_);
v___x_711_ = v___x_705_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_arrKeyTys_635_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_arrParents_636_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_currArrKey_637_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v_currKey_638_);
lean_ctor_set(v_reuseFailAlloc_712_, 5, v_items_639_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
v_fst_625_ = v___x_640_;
v_snd_626_ = v___x_711_;
goto v___jp_624_;
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v___y_620_);
lean_dec(v_b_619_);
v_a_720_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_632_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_632_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_b_619_);
lean_ctor_set(v___x_728_, 1, v___y_620_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
v___jp_624_:
{
size_t v___x_627_; size_t v___x_628_; 
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_i_617_, v___x_627_);
v_i_617_ = v___x_628_;
v_b_619_ = v_fst_625_;
v___y_620_ = v_snd_626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_730_, lean_object* v_i_731_, lean_object* v_stop_732_, lean_object* v_b_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
size_t v_i_boxed_738_; size_t v_stop_boxed_739_; lean_object* v_res_740_; 
v_i_boxed_738_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_stop_boxed_739_ = lean_unbox_usize(v_stop_732_);
lean_dec(v_stop_732_);
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_730_, v_i_boxed_738_, v_stop_boxed_739_, v_b_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec_ref(v_as_730_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_741_, lean_object* v_k_742_){
_start:
{
if (lean_obj_tag(v_t_741_) == 0)
{
lean_object* v_k_743_; lean_object* v_v_744_; lean_object* v_l_745_; lean_object* v_r_746_; uint8_t v___x_747_; 
v_k_743_ = lean_ctor_get(v_t_741_, 1);
v_v_744_ = lean_ctor_get(v_t_741_, 2);
v_l_745_ = lean_ctor_get(v_t_741_, 3);
v_r_746_ = lean_ctor_get(v_t_741_, 4);
v___x_747_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_742_, v_k_743_);
switch(v___x_747_)
{
case 0:
{
v_t_741_ = v_l_745_;
goto _start;
}
case 1:
{
lean_object* v___x_749_; 
lean_inc(v_v_744_);
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v_v_744_);
return v___x_749_;
}
default: 
{
v_t_741_ = v_r_746_;
goto _start;
}
}
}
else
{
lean_object* v___x_751_; 
v___x_751_ = lean_box(0);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_752_, lean_object* v_k_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_752_, v_k_753_);
lean_dec(v_k_753_);
lean_dec(v_t_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_keyTys_760_; lean_object* v_arrKeyTys_761_; lean_object* v_arrParents_762_; lean_object* v_currArrKey_763_; lean_object* v_currKey_764_; lean_object* v_items_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_793_; 
v_keyTys_760_ = lean_ctor_get(v_a_756_, 0);
v_arrKeyTys_761_ = lean_ctor_get(v_a_756_, 1);
v_arrParents_762_ = lean_ctor_get(v_a_756_, 2);
v_currArrKey_763_ = lean_ctor_get(v_a_756_, 3);
v_currKey_764_ = lean_ctor_get(v_a_756_, 4);
v_items_765_ = lean_ctor_get(v_a_756_, 5);
v_isSharedCheck_793_ = !lean_is_exclusive(v_a_756_);
if (v_isSharedCheck_793_ == 0)
{
v___x_767_ = v_a_756_;
v_isShared_768_ = v_isSharedCheck_793_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_items_765_);
lean_inc(v_currKey_764_);
lean_inc(v_currArrKey_763_);
lean_inc(v_arrParents_762_);
lean_inc(v_arrKeyTys_761_);
lean_inc(v_keyTys_760_);
lean_dec(v_a_756_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_793_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_arrKeyTys_769_; lean_object* v___x_770_; lean_object* v___y_772_; lean_object* v___x_790_; 
v_arrKeyTys_769_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_763_, v_keyTys_760_, v_arrKeyTys_761_);
v___x_770_ = lean_box(0);
v___x_790_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_769_, v___x_770_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; 
v___x_791_ = lean_box(1);
v___y_772_ = v___x_791_;
goto v___jp_771_;
}
else
{
lean_object* v_val_792_; 
v_val_792_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_val_792_);
lean_dec_ref(v___x_790_);
v___y_772_ = v_val_792_;
goto v___jp_771_;
}
v___jp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 3, v___x_770_);
lean_ctor_set(v___x_767_, 1, v_arrKeyTys_769_);
lean_ctor_set(v___x_767_, 0, v___y_772_);
v___x_774_ = v___x_767_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___y_772_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_arrKeyTys_769_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_arrParents_762_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v_currKey_764_);
lean_ctor_set(v_reuseFailAlloc_789_, 5, v_items_765_);
v___x_774_ = v_reuseFailAlloc_789_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_array_get_size(v_ks_755_);
v___x_777_ = lean_nat_dec_lt(v___x_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_770_);
lean_ctor_set(v___x_778_, 1, v___x_774_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
else
{
uint8_t v___x_780_; 
v___x_780_ = lean_nat_dec_le(v___x_776_, v___x_776_);
if (v___x_780_ == 0)
{
if (v___x_777_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_770_);
lean_ctor_set(v___x_781_, 1, v___x_774_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
else
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((size_t)0ULL);
v___x_784_ = lean_usize_of_nat(v___x_776_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_755_, v___x_783_, v___x_784_, v___x_770_, v___x_774_, v_a_757_, v_a_758_);
return v___x_785_;
}
}
else
{
size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; 
v___x_786_ = ((size_t)0ULL);
v___x_787_ = lean_usize_of_nat(v___x_776_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_755_, v___x_786_, v___x_787_, v___x_770_, v___x_774_, v_a_757_, v_a_758_);
return v___x_788_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec_ref(v_ks_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_800_, lean_object* v_t_801_, lean_object* v_k_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_801_, v_k_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_804_, lean_object* v_t_805_, lean_object* v_k_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_804_, v_t_805_, v_k_806_);
lean_dec(v_k_806_);
lean_dec(v_t_805_);
return v_res_807_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
v___x_810_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4));
v___x_818_ = l_Lean_stringToMessageData(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___y_825_; lean_object* v_keyTys_826_; lean_object* v_arrKeyTys_827_; lean_object* v_arrParents_828_; lean_object* v_currArrKey_829_; lean_object* v_items_830_; lean_object* v_fileName_842_; lean_object* v_fileMap_843_; lean_object* v_options_844_; lean_object* v_currRecDepth_845_; lean_object* v_maxRecDepth_846_; lean_object* v_ref_847_; lean_object* v_currNamespace_848_; lean_object* v_openDecls_849_; lean_object* v_initHeartbeats_850_; lean_object* v_maxHeartbeats_851_; lean_object* v_quotContext_852_; lean_object* v_currMacroScope_853_; uint8_t v_diag_854_; lean_object* v_cancelTk_x3f_855_; uint8_t v_suppressElabErrors_856_; lean_object* v_inheritedTraceOptions_857_; lean_object* v___x_858_; uint8_t v___x_859_; lean_object* v_ref_860_; lean_object* v___x_861_; 
v_fileName_842_ = lean_ctor_get(v_a_821_, 0);
v_fileMap_843_ = lean_ctor_get(v_a_821_, 1);
v_options_844_ = lean_ctor_get(v_a_821_, 2);
v_currRecDepth_845_ = lean_ctor_get(v_a_821_, 3);
v_maxRecDepth_846_ = lean_ctor_get(v_a_821_, 4);
v_ref_847_ = lean_ctor_get(v_a_821_, 5);
v_currNamespace_848_ = lean_ctor_get(v_a_821_, 6);
v_openDecls_849_ = lean_ctor_get(v_a_821_, 7);
v_initHeartbeats_850_ = lean_ctor_get(v_a_821_, 8);
v_maxHeartbeats_851_ = lean_ctor_get(v_a_821_, 9);
v_quotContext_852_ = lean_ctor_get(v_a_821_, 10);
v_currMacroScope_853_ = lean_ctor_get(v_a_821_, 11);
v_diag_854_ = lean_ctor_get_uint8(v_a_821_, sizeof(void*)*14);
v_cancelTk_x3f_855_ = lean_ctor_get(v_a_821_, 12);
v_suppressElabErrors_856_ = lean_ctor_get_uint8(v_a_821_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_857_ = lean_ctor_get(v_a_821_, 13);
v___x_858_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_819_);
v___x_859_ = l_Lean_Syntax_isOfKind(v_x_819_, v___x_858_);
v_ref_860_ = l_Lean_replaceRef(v_x_819_, v_ref_847_);
lean_inc_ref(v_inheritedTraceOptions_857_);
lean_inc(v_cancelTk_x3f_855_);
lean_inc(v_currMacroScope_853_);
lean_inc(v_quotContext_852_);
lean_inc(v_maxHeartbeats_851_);
lean_inc(v_initHeartbeats_850_);
lean_inc(v_openDecls_849_);
lean_inc(v_currNamespace_848_);
lean_inc(v_maxRecDepth_846_);
lean_inc(v_currRecDepth_845_);
lean_inc_ref(v_options_844_);
lean_inc_ref(v_fileMap_843_);
lean_inc_ref(v_fileName_842_);
v___x_861_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_861_, 0, v_fileName_842_);
lean_ctor_set(v___x_861_, 1, v_fileMap_843_);
lean_ctor_set(v___x_861_, 2, v_options_844_);
lean_ctor_set(v___x_861_, 3, v_currRecDepth_845_);
lean_ctor_set(v___x_861_, 4, v_maxRecDepth_846_);
lean_ctor_set(v___x_861_, 5, v_ref_860_);
lean_ctor_set(v___x_861_, 6, v_currNamespace_848_);
lean_ctor_set(v___x_861_, 7, v_openDecls_849_);
lean_ctor_set(v___x_861_, 8, v_initHeartbeats_850_);
lean_ctor_set(v___x_861_, 9, v_maxHeartbeats_851_);
lean_ctor_set(v___x_861_, 10, v_quotContext_852_);
lean_ctor_set(v___x_861_, 11, v_currMacroScope_853_);
lean_ctor_set(v___x_861_, 12, v_cancelTk_x3f_855_);
lean_ctor_set(v___x_861_, 13, v_inheritedTraceOptions_857_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*14, v_diag_854_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*14 + 1, v_suppressElabErrors_856_);
if (v___x_859_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5);
v___x_863_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_819_, v___x_862_, v_a_820_, v___x_861_, v_a_822_);
lean_dec_ref(v___x_861_);
lean_dec_ref(v_a_820_);
lean_dec(v_x_819_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___y_867_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = l_Lean_Syntax_getArg(v_x_819_, v___x_864_);
v___x_935_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_865_);
v___x_936_ = l_Lean_Syntax_isOfKind(v___x_865_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_x_819_);
v___x_937_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_938_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_865_, v___x_937_, v_a_820_, v___x_861_, v_a_822_);
lean_dec_ref(v___x_861_);
lean_dec_ref(v_a_820_);
lean_dec(v___x_865_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = l_Lean_Syntax_getArg(v___x_865_, v___x_939_);
v___x_941_ = l_Lean_Syntax_getArgs(v___x_940_);
lean_dec(v___x_940_);
v___x_942_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_943_ = lean_array_get_size(v___x_941_);
v___x_944_ = lean_nat_dec_lt(v___x_939_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec_ref(v___x_941_);
v___y_867_ = v___x_942_;
goto v___jp_866_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_945_ = lean_box(v___x_936_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_942_);
v___x_947_ = lean_nat_dec_le(v___x_943_, v___x_943_);
if (v___x_947_ == 0)
{
if (v___x_944_ == 0)
{
lean_dec_ref(v___x_946_);
lean_dec_ref(v___x_941_);
v___y_867_ = v___x_942_;
goto v___jp_866_;
}
else
{
size_t v___x_948_; size_t v___x_949_; lean_object* v___x_950_; lean_object* v_snd_951_; 
v___x_948_ = ((size_t)0ULL);
v___x_949_ = lean_usize_of_nat(v___x_943_);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_936_, v___x_941_, v___x_948_, v___x_949_, v___x_946_);
lean_dec_ref(v___x_941_);
v_snd_951_ = lean_ctor_get(v___x_950_, 1);
lean_inc(v_snd_951_);
lean_dec_ref(v___x_950_);
v___y_867_ = v_snd_951_;
goto v___jp_866_;
}
}
else
{
size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; lean_object* v_snd_955_; 
v___x_952_ = ((size_t)0ULL);
v___x_953_ = lean_usize_of_nat(v___x_943_);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_936_, v___x_941_, v___x_952_, v___x_953_, v___x_946_);
lean_dec_ref(v___x_941_);
v_snd_955_ = lean_ctor_get(v___x_954_, 1);
lean_inc(v_snd_955_);
lean_dec_ref(v___x_954_);
v___y_867_ = v_snd_955_;
goto v___jp_866_;
}
}
}
v___jp_866_:
{
size_t v_sz_868_; size_t v___x_869_; lean_object* v___x_870_; 
v_sz_868_ = lean_array_size(v___y_867_);
v___x_869_ = ((size_t)0ULL);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_868_, v___x_869_, v___y_867_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v_x_819_);
v___x_871_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_872_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_865_, v___x_871_, v_a_820_, v___x_861_, v_a_822_);
lean_dec_ref(v___x_861_);
lean_dec_ref(v_a_820_);
lean_dec(v___x_865_);
return v___x_872_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_tailKey_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v___x_865_);
v_val_873_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_val_873_);
lean_dec_ref(v___x_870_);
v___x_874_ = lean_box(0);
v___x_875_ = lean_array_get_size(v_val_873_);
v___x_876_ = lean_nat_sub(v___x_875_, v___x_864_);
v_tailKey_877_ = lean_array_get(v___x_874_, v_val_873_, v___x_876_);
lean_dec(v___x_876_);
v___x_878_ = lean_array_pop(v_val_873_);
v___x_879_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_878_, v_a_820_, v___x_861_, v_a_822_);
lean_dec_ref(v___x_878_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v_fst_881_; lean_object* v_snd_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_926_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref(v___x_879_);
v_fst_881_ = lean_ctor_get(v_a_880_, 0);
v_snd_882_ = lean_ctor_get(v_a_880_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_a_880_);
if (v_isSharedCheck_926_ == 0)
{
v___x_884_ = v_a_880_;
v_isShared_885_ = v_isSharedCheck_926_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_snd_882_);
lean_inc(v_fst_881_);
lean_dec(v_a_880_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_926_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; 
lean_inc(v_tailKey_877_);
v___x_886_ = l_Lake_Toml_elabSimpleKey(v_tailKey_877_, v___x_861_, v_a_822_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v_keyTys_888_; lean_object* v_arrKeyTys_889_; lean_object* v_arrParents_890_; lean_object* v_currArrKey_891_; lean_object* v_items_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v___x_886_);
v_keyTys_888_ = lean_ctor_get(v_snd_882_, 0);
v_arrKeyTys_889_ = lean_ctor_get(v_snd_882_, 1);
v_arrParents_890_ = lean_ctor_get(v_snd_882_, 2);
v_currArrKey_891_ = lean_ctor_get(v_snd_882_, 3);
v_items_892_ = lean_ctor_get(v_snd_882_, 5);
v___x_893_ = l_Lean_Name_str___override(v_fst_881_, v_a_887_);
v___x_894_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_888_, v___x_893_);
if (lean_obj_tag(v___x_894_) == 1)
{
lean_object* v_val_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_917_; 
v_val_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_917_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_917_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_val_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_917_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
uint8_t v___x_899_; 
v___x_899_ = lean_unbox(v_val_895_);
if (v___x_899_ == 4)
{
lean_inc_ref(v_items_892_);
lean_inc(v_currArrKey_891_);
lean_inc(v_arrParents_890_);
lean_inc(v_arrKeyTys_889_);
lean_inc(v_keyTys_888_);
lean_del_object(v___x_897_);
lean_dec(v_val_895_);
lean_del_object(v___x_884_);
lean_dec(v_snd_882_);
lean_dec(v_tailKey_877_);
lean_dec_ref(v___x_861_);
v___y_825_ = v___x_893_;
v_keyTys_826_ = v_keyTys_888_;
v_arrKeyTys_827_ = v_arrKeyTys_889_;
v_arrParents_828_ = v_arrParents_890_;
v_currArrKey_829_ = v_currArrKey_891_;
v_items_830_ = v_items_892_;
goto v___jp_824_;
}
else
{
lean_object* v___x_900_; uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec(v_x_819_);
v___x_900_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_901_ = lean_unbox(v_val_895_);
lean_dec(v_val_895_);
v___x_902_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_901_);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 3);
lean_ctor_set(v___x_897_, 0, v___x_902_);
v___x_904_ = v___x_897_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_916_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = l_Lean_MessageData_ofFormat(v___x_904_);
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 7);
lean_ctor_set(v___x_884_, 1, v___x_905_);
lean_ctor_set(v___x_884_, 0, v___x_900_);
v___x_907_ = v___x_884_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_905_);
v___x_907_ = v_reuseFailAlloc_915_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_MessageData_ofName(v___x_893_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_877_, v___x_913_, v_snd_882_, v___x_861_, v_a_822_);
lean_dec_ref(v___x_861_);
lean_dec(v_snd_882_);
lean_dec(v_tailKey_877_);
return v___x_914_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_892_);
lean_inc(v_currArrKey_891_);
lean_inc(v_arrParents_890_);
lean_inc(v_arrKeyTys_889_);
lean_inc(v_keyTys_888_);
lean_dec(v___x_894_);
lean_del_object(v___x_884_);
lean_dec(v_snd_882_);
lean_dec(v_tailKey_877_);
lean_dec_ref(v___x_861_);
v___y_825_ = v___x_893_;
v_keyTys_826_ = v_keyTys_888_;
v_arrKeyTys_827_ = v_arrKeyTys_889_;
v_arrParents_828_ = v_arrParents_890_;
v_currArrKey_829_ = v_currArrKey_891_;
v_items_830_ = v_items_892_;
goto v___jp_824_;
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_del_object(v___x_884_);
lean_dec(v_snd_882_);
lean_dec(v_fst_881_);
lean_dec(v_tailKey_877_);
lean_dec_ref(v___x_861_);
lean_dec(v_x_819_);
v_a_918_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_886_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_886_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_tailKey_877_);
lean_dec_ref(v___x_861_);
lean_dec(v_x_819_);
v_a_927_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_879_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_879_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
v___jp_824_:
{
lean_object* v___x_831_; uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_831_ = lean_box(0);
v___x_832_ = 1;
v___x_833_ = lean_box(v___x_832_);
lean_inc_n(v___y_825_, 2);
v___x_834_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_825_, v___x_833_, v_keyTys_826_);
v___x_835_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc(v_x_819_);
v___x_836_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_836_, 0, v_x_819_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_837_, 0, v_x_819_);
lean_ctor_set(v___x_837_, 1, v___y_825_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
v___x_838_ = lean_array_push(v_items_830_, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_839_, 0, v___x_834_);
lean_ctor_set(v___x_839_, 1, v_arrKeyTys_827_);
lean_ctor_set(v___x_839_, 2, v_arrParents_828_);
lean_ctor_set(v___x_839_, 3, v_currArrKey_829_);
lean_ctor_set(v___x_839_, 4, v___y_825_);
lean_ctor_set(v___x_839_, 5, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_831_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_961_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_969_ = l_Lean_stringToMessageData(v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_fileName_975_; lean_object* v_fileMap_976_; lean_object* v_options_977_; lean_object* v_currRecDepth_978_; lean_object* v_maxRecDepth_979_; lean_object* v_ref_980_; lean_object* v_currNamespace_981_; lean_object* v_openDecls_982_; lean_object* v_initHeartbeats_983_; lean_object* v_maxHeartbeats_984_; lean_object* v_quotContext_985_; lean_object* v_currMacroScope_986_; uint8_t v_diag_987_; lean_object* v_cancelTk_x3f_988_; uint8_t v_suppressElabErrors_989_; lean_object* v_inheritedTraceOptions_990_; lean_object* v___x_991_; uint8_t v___x_992_; lean_object* v_ref_993_; lean_object* v___x_994_; lean_object* v___y_996_; 
v_fileName_975_ = lean_ctor_get(v_a_972_, 0);
v_fileMap_976_ = lean_ctor_get(v_a_972_, 1);
v_options_977_ = lean_ctor_get(v_a_972_, 2);
v_currRecDepth_978_ = lean_ctor_get(v_a_972_, 3);
v_maxRecDepth_979_ = lean_ctor_get(v_a_972_, 4);
v_ref_980_ = lean_ctor_get(v_a_972_, 5);
v_currNamespace_981_ = lean_ctor_get(v_a_972_, 6);
v_openDecls_982_ = lean_ctor_get(v_a_972_, 7);
v_initHeartbeats_983_ = lean_ctor_get(v_a_972_, 8);
v_maxHeartbeats_984_ = lean_ctor_get(v_a_972_, 9);
v_quotContext_985_ = lean_ctor_get(v_a_972_, 10);
v_currMacroScope_986_ = lean_ctor_get(v_a_972_, 11);
v_diag_987_ = lean_ctor_get_uint8(v_a_972_, sizeof(void*)*14);
v_cancelTk_x3f_988_ = lean_ctor_get(v_a_972_, 12);
v_suppressElabErrors_989_ = lean_ctor_get_uint8(v_a_972_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_990_ = lean_ctor_get(v_a_972_, 13);
v___x_991_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_970_);
v___x_992_ = l_Lean_Syntax_isOfKind(v_x_970_, v___x_991_);
v_ref_993_ = l_Lean_replaceRef(v_x_970_, v_ref_980_);
lean_inc_ref(v_inheritedTraceOptions_990_);
lean_inc(v_cancelTk_x3f_988_);
lean_inc(v_currMacroScope_986_);
lean_inc(v_quotContext_985_);
lean_inc(v_maxHeartbeats_984_);
lean_inc(v_initHeartbeats_983_);
lean_inc(v_openDecls_982_);
lean_inc(v_currNamespace_981_);
lean_inc(v_maxRecDepth_979_);
lean_inc(v_currRecDepth_978_);
lean_inc_ref(v_options_977_);
lean_inc_ref(v_fileMap_976_);
lean_inc_ref(v_fileName_975_);
v___x_994_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_994_, 0, v_fileName_975_);
lean_ctor_set(v___x_994_, 1, v_fileMap_976_);
lean_ctor_set(v___x_994_, 2, v_options_977_);
lean_ctor_set(v___x_994_, 3, v_currRecDepth_978_);
lean_ctor_set(v___x_994_, 4, v_maxRecDepth_979_);
lean_ctor_set(v___x_994_, 5, v_ref_993_);
lean_ctor_set(v___x_994_, 6, v_currNamespace_981_);
lean_ctor_set(v___x_994_, 7, v_openDecls_982_);
lean_ctor_set(v___x_994_, 8, v_initHeartbeats_983_);
lean_ctor_set(v___x_994_, 9, v_maxHeartbeats_984_);
lean_ctor_set(v___x_994_, 10, v_quotContext_985_);
lean_ctor_set(v___x_994_, 11, v_currMacroScope_986_);
lean_ctor_set(v___x_994_, 12, v_cancelTk_x3f_988_);
lean_ctor_set(v___x_994_, 13, v_inheritedTraceOptions_990_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*14, v_diag_987_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*14 + 1, v_suppressElabErrors_989_);
if (v___x_992_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_1004_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_970_, v___x_1003_, v_a_971_, v___x_994_, v_a_973_);
lean_dec_ref(v___x_994_);
lean_dec_ref(v_a_971_);
lean_dec(v_x_970_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___y_1010_; 
v___x_1005_ = lean_unsigned_to_nat(2u);
v___x_1006_ = l_Lean_Syntax_getArg(v_x_970_, v___x_1005_);
v___x_1007_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_1006_);
v___x_1008_ = l_Lean_Syntax_isOfKind(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v___x_1006_);
v___x_1144_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1145_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_970_, v___x_1144_, v_a_971_, v___x_994_, v_a_973_);
lean_dec_ref(v___x_994_);
lean_dec_ref(v_a_971_);
lean_dec(v_x_970_);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = l_Lean_Syntax_getArg(v___x_1006_, v___x_1146_);
lean_dec(v___x_1006_);
v___x_1148_ = l_Lean_Syntax_getArgs(v___x_1147_);
lean_dec(v___x_1147_);
v___x_1149_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1150_ = lean_array_get_size(v___x_1148_);
v___x_1151_ = lean_nat_dec_lt(v___x_1146_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_dec_ref(v___x_1148_);
v___y_1010_ = v___x_1149_;
goto v___jp_1009_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1152_ = lean_box(v___x_1008_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v___x_1149_);
v___x_1154_ = lean_nat_dec_le(v___x_1150_, v___x_1150_);
if (v___x_1154_ == 0)
{
if (v___x_1151_ == 0)
{
lean_dec_ref(v___x_1153_);
lean_dec_ref(v___x_1148_);
v___y_1010_ = v___x_1149_;
goto v___jp_1009_;
}
else
{
size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; lean_object* v_snd_1158_; 
v___x_1155_ = ((size_t)0ULL);
v___x_1156_ = lean_usize_of_nat(v___x_1150_);
v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_1008_, v___x_1148_, v___x_1155_, v___x_1156_, v___x_1153_);
lean_dec_ref(v___x_1148_);
v_snd_1158_ = lean_ctor_get(v___x_1157_, 1);
lean_inc(v_snd_1158_);
lean_dec_ref(v___x_1157_);
v___y_1010_ = v_snd_1158_;
goto v___jp_1009_;
}
}
else
{
size_t v___x_1159_; size_t v___x_1160_; lean_object* v___x_1161_; lean_object* v_snd_1162_; 
v___x_1159_ = ((size_t)0ULL);
v___x_1160_ = lean_usize_of_nat(v___x_1150_);
v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_1008_, v___x_1148_, v___x_1159_, v___x_1160_, v___x_1153_);
lean_dec_ref(v___x_1148_);
v_snd_1162_ = lean_ctor_get(v___x_1161_, 1);
lean_inc(v_snd_1162_);
lean_dec_ref(v___x_1161_);
v___y_1010_ = v_snd_1162_;
goto v___jp_1009_;
}
}
}
v___jp_1009_:
{
size_t v_sz_1011_; size_t v___x_1012_; lean_object* v___x_1013_; 
v_sz_1011_ = lean_array_size(v___y_1010_);
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_1011_, v___x_1012_, v___y_1010_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1015_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_970_, v___x_1014_, v_a_971_, v___x_994_, v_a_973_);
lean_dec_ref(v___x_994_);
lean_dec_ref(v_a_971_);
lean_dec(v_x_970_);
return v___x_1015_;
}
else
{
lean_object* v_val_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_tailKey_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_val_1016_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_val_1016_);
lean_dec_ref(v___x_1013_);
v___x_1017_ = lean_box(0);
v___x_1018_ = lean_array_get_size(v_val_1016_);
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_sub(v___x_1018_, v___x_1019_);
v_tailKey_1021_ = lean_array_get(v___x_1017_, v_val_1016_, v___x_1020_);
lean_dec(v___x_1020_);
v___x_1022_ = lean_array_pop(v_val_1016_);
v___x_1023_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_1022_, v_a_971_, v___x_994_, v_a_973_);
lean_dec_ref(v___x_1022_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v_fst_1025_; lean_object* v_snd_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1135_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1023_);
v_fst_1025_ = lean_ctor_get(v_a_1024_, 0);
v_snd_1026_ = lean_ctor_get(v_a_1024_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_a_1024_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1028_ = v_a_1024_;
v_isShared_1029_ = v_isSharedCheck_1135_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_snd_1026_);
lean_inc(v_fst_1025_);
lean_dec(v_a_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1135_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; 
lean_inc(v_tailKey_1021_);
v___x_1030_ = l_Lake_Toml_elabSimpleKey(v_tailKey_1021_, v___x_994_, v_a_973_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1126_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1126_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1126_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_keyTys_1035_; lean_object* v_arrKeyTys_1036_; lean_object* v_arrParents_1037_; lean_object* v_currArrKey_1038_; lean_object* v_items_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_keyTys_1035_ = lean_ctor_get(v_snd_1026_, 0);
v_arrKeyTys_1036_ = lean_ctor_get(v_snd_1026_, 1);
v_arrParents_1037_ = lean_ctor_get(v_snd_1026_, 2);
v_currArrKey_1038_ = lean_ctor_get(v_snd_1026_, 3);
v_items_1039_ = lean_ctor_get(v_snd_1026_, 5);
v___x_1040_ = l_Lean_Name_str___override(v_fst_1025_, v_a_1031_);
v___x_1041_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_1035_, v___x_1040_);
if (lean_obj_tag(v___x_1041_) == 1)
{
lean_object* v_val_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1093_; 
v_val_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1093_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_val_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1093_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_unbox(v_val_1042_);
if (v___x_1046_ == 2)
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1071_; 
lean_inc_ref(v_items_1039_);
lean_inc(v_arrParents_1037_);
lean_inc(v_arrKeyTys_1036_);
lean_del_object(v___x_1044_);
lean_dec(v_val_1042_);
lean_dec(v_tailKey_1021_);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_snd_1026_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; lean_object* v_unused_1073_; lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; 
v_unused_1072_ = lean_ctor_get(v_snd_1026_, 5);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_snd_1026_, 4);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_snd_1026_, 3);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_snd_1026_, 2);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_snd_1026_, 1);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_snd_1026_, 0);
lean_dec(v_unused_1077_);
v___x_1048_ = v_snd_1026_;
v_isShared_1049_ = v_isSharedCheck_1071_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v_snd_1026_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1071_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_1037_, v___x_1040_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_del_object(v___x_1048_);
lean_dec_ref(v_items_1039_);
lean_dec(v_arrParents_1037_);
lean_dec(v_arrKeyTys_1036_);
lean_del_object(v___x_1033_);
lean_del_object(v___x_1028_);
lean_dec(v_x_970_);
v___y_996_ = v___x_1040_;
goto v___jp_995_;
}
else
{
lean_object* v_val_1051_; lean_object* v___x_1052_; 
v_val_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_val_1051_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_1036_, v_val_1051_);
lean_dec(v_val_1051_);
if (lean_obj_tag(v___x_1052_) == 1)
{
lean_object* v_val_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec_ref(v___x_994_);
v_val_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_val_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_970_, 2);
v___x_1056_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_x_970_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_mk_empty_array_with_capacity(v___x_1019_);
v___x_1058_ = lean_array_push(v___x_1057_, v___x_1056_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_x_970_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
lean_inc_n(v___x_1040_, 2);
v___x_1060_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1060_, 0, v_x_970_);
lean_ctor_set(v___x_1060_, 1, v___x_1040_);
lean_ctor_set(v___x_1060_, 2, v___x_1059_);
v___x_1061_ = lean_array_push(v_items_1039_, v___x_1060_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 5, v___x_1061_);
lean_ctor_set(v___x_1048_, 4, v___x_1040_);
lean_ctor_set(v___x_1048_, 3, v___x_1040_);
lean_ctor_set(v___x_1048_, 0, v_val_1053_);
v___x_1063_ = v___x_1048_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_val_1053_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_arrKeyTys_1036_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_arrParents_1037_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1070_, 5, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v___x_1063_);
lean_ctor_set(v___x_1028_, 0, v___x_1054_);
v___x_1065_ = v___x_1028_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1065_);
v___x_1067_ = v___x_1033_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_dec(v___x_1052_);
lean_del_object(v___x_1048_);
lean_dec_ref(v_items_1039_);
lean_dec(v_arrParents_1037_);
lean_dec(v_arrKeyTys_1036_);
lean_del_object(v___x_1033_);
lean_del_object(v___x_1028_);
lean_dec(v_x_970_);
v___y_996_ = v___x_1040_;
goto v___jp_995_;
}
}
}
}
else
{
lean_object* v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_del_object(v___x_1033_);
lean_del_object(v___x_1028_);
lean_dec(v_x_970_);
v___x_1078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1079_ = lean_unbox(v_val_1042_);
lean_dec(v_val_1042_);
v___x_1080_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1079_);
v___x_1081_ = lean_string_append(v___x_1078_, v___x_1080_);
lean_dec_ref(v___x_1080_);
v___x_1082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1083_ = lean_string_append(v___x_1081_, v___x_1082_);
v___x_1084_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1040_, v___x_1008_);
v___x_1085_ = lean_string_append(v___x_1083_, v___x_1084_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1087_ = lean_string_append(v___x_1085_, v___x_1086_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 3);
lean_ctor_set(v___x_1044_, 0, v___x_1087_);
v___x_1089_ = v___x_1044_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = l_Lean_MessageData_ofFormat(v___x_1089_);
v___x_1091_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_1021_, v___x_1090_, v_snd_1026_, v___x_994_, v_a_973_);
lean_dec_ref(v___x_994_);
lean_dec(v_snd_1026_);
lean_dec(v_tailKey_1021_);
return v___x_1091_;
}
}
}
}
else
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1119_; 
lean_inc_ref(v_items_1039_);
lean_inc(v_currArrKey_1038_);
lean_inc(v_arrParents_1037_);
lean_inc(v_arrKeyTys_1036_);
lean_inc(v_keyTys_1035_);
lean_dec(v___x_1041_);
lean_dec(v_tailKey_1021_);
lean_dec_ref(v___x_994_);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_snd_1026_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; lean_object* v_unused_1121_; lean_object* v_unused_1122_; lean_object* v_unused_1123_; lean_object* v_unused_1124_; lean_object* v_unused_1125_; 
v_unused_1120_ = lean_ctor_get(v_snd_1026_, 5);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_snd_1026_, 4);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_snd_1026_, 3);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_snd_1026_, 2);
lean_dec(v_unused_1123_);
v_unused_1124_ = lean_ctor_get(v_snd_1026_, 1);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v_snd_1026_, 0);
lean_dec(v_unused_1125_);
v___x_1095_ = v_snd_1026_;
v_isShared_1096_ = v_isSharedCheck_1119_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v_snd_1026_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1119_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = 2;
v___x_1099_ = lean_box(v___x_1098_);
lean_inc_n(v___x_1040_, 4);
v___x_1100_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1040_, v___x_1099_, v_keyTys_1035_);
lean_inc(v___x_1100_);
lean_inc(v_currArrKey_1038_);
v___x_1101_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_1038_, v___x_1100_, v_arrKeyTys_1036_);
v___x_1102_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1040_, v_currArrKey_1038_, v_arrParents_1037_);
v___x_1103_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc_n(v_x_970_, 2);
v___x_1104_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_x_970_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = lean_mk_empty_array_with_capacity(v___x_1019_);
v___x_1106_ = lean_array_push(v___x_1105_, v___x_1104_);
v___x_1107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_x_970_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1108_, 0, v_x_970_);
lean_ctor_set(v___x_1108_, 1, v___x_1040_);
lean_ctor_set(v___x_1108_, 2, v___x_1107_);
v___x_1109_ = lean_array_push(v_items_1039_, v___x_1108_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 5, v___x_1109_);
lean_ctor_set(v___x_1095_, 4, v___x_1040_);
lean_ctor_set(v___x_1095_, 3, v___x_1040_);
lean_ctor_set(v___x_1095_, 2, v___x_1102_);
lean_ctor_set(v___x_1095_, 1, v___x_1101_);
lean_ctor_set(v___x_1095_, 0, v___x_1100_);
v___x_1111_ = v___x_1095_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1118_, 4, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1118_, 5, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v___x_1111_);
lean_ctor_set(v___x_1028_, 0, v___x_1097_);
v___x_1113_ = v___x_1028_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1113_);
v___x_1115_ = v___x_1033_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_del_object(v___x_1028_);
lean_dec(v_snd_1026_);
lean_dec(v_fst_1025_);
lean_dec(v_tailKey_1021_);
lean_dec_ref(v___x_994_);
lean_dec(v_x_970_);
v_a_1127_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1030_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1030_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_tailKey_1021_);
lean_dec_ref(v___x_994_);
lean_dec(v_x_970_);
v_a_1136_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1023_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1023_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
}
v___jp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_997_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_998_ = l_Lean_MessageData_ofName(v___y_996_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_1001_, v___x_994_, v_a_973_);
lean_dec_ref(v___x_994_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1168_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1172_);
v___x_1178_ = l_Lean_Syntax_isOfKind(v_x_1172_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_1172_);
v___x_1180_ = l_Lean_Syntax_isOfKind(v_x_1172_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1172_);
v___x_1182_ = l_Lean_Syntax_isOfKind(v_x_1172_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1184_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1172_, v___x_1183_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec_ref(v_a_1173_);
lean_dec(v_x_1172_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v___x_1185_;
}
}
else
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v___x_1186_;
}
}
else
{
lean_object* v___x_1187_; 
v___x_1187_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1194_, lean_object* v_as_1195_, size_t v_i_1196_, size_t v_stop_1197_, lean_object* v_b_1198_){
_start:
{
lean_object* v___y_1200_; uint8_t v___x_1204_; 
v___x_1204_ = lean_usize_dec_eq(v_i_1196_, v_stop_1197_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v_fst_1206_; lean_object* v_snd_1207_; lean_object* v___x_1208_; 
v___x_1205_ = lean_array_uget_borrowed(v_as_1195_, v_i_1196_);
v_fst_1206_ = lean_ctor_get(v___x_1205_, 0);
v_snd_1207_ = lean_ctor_get(v___x_1205_, 1);
lean_inc(v_fst_1206_);
v___x_1208_ = l_Lean_Name_components(v_fst_1206_);
if (lean_obj_tag(v___x_1208_) == 0)
{
v___y_1200_ = v_b_1198_;
goto v___jp_1199_;
}
else
{
lean_object* v_head_1209_; lean_object* v_tail_1210_; lean_object* v___x_1211_; 
v_head_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_head_1209_);
v_tail_1210_ = lean_ctor_get(v___x_1208_, 1);
lean_inc(v_tail_1210_);
lean_dec_ref(v___x_1208_);
lean_inc(v_snd_1207_);
lean_inc(v_ref_1194_);
v___x_1211_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1198_, v_ref_1194_, v_head_1209_, v_tail_1210_, v_snd_1207_);
v___y_1200_ = v___x_1211_;
goto v___jp_1199_;
}
}
else
{
lean_dec(v_ref_1194_);
return v_b_1198_;
}
v___jp_1199_:
{
size_t v___x_1201_; size_t v___x_1202_; 
v___x_1201_ = ((size_t)1ULL);
v___x_1202_ = lean_usize_add(v_i_1196_, v___x_1201_);
v_i_1196_ = v___x_1202_;
v_b_1198_ = v___y_1200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1212_, size_t v_i_1213_, lean_object* v_bs_1214_){
_start:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_usize_dec_lt(v_i_1213_, v_sz_1212_);
if (v___x_1215_ == 0)
{
return v_bs_1214_;
}
else
{
lean_object* v_v_1216_; lean_object* v___x_1217_; lean_object* v_bs_x27_1218_; lean_object* v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v_v_1216_ = lean_array_uget(v_bs_1214_, v_i_1213_);
v___x_1217_ = lean_unsigned_to_nat(0u);
v_bs_x27_1218_ = lean_array_uset(v_bs_1214_, v_i_1213_, v___x_1217_);
v___x_1219_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1216_);
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_add(v_i_1213_, v___x_1220_);
v___x_1222_ = lean_array_uset(v_bs_x27_1218_, v_i_1213_, v___x_1219_);
v_i_1213_ = v___x_1221_;
v_bs_1214_ = v___x_1222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1224_){
_start:
{
switch(lean_obj_tag(v_a_1224_))
{
case 6:
{
lean_object* v_xs_1225_; lean_object* v_ref_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1254_; 
v_xs_1225_ = lean_ctor_get(v_a_1224_, 1);
v_ref_1226_ = lean_ctor_get(v_a_1224_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_a_1224_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1228_ = v_a_1224_;
v_isShared_1229_ = v_isSharedCheck_1254_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_xs_1225_);
lean_inc(v_ref_1226_);
lean_dec(v_a_1224_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1254_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_items_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_items_1230_ = lean_ctor_get(v_xs_1225_, 0);
lean_inc_ref(v_items_1230_);
lean_dec_ref(v_xs_1225_);
v___x_1231_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = lean_array_get_size(v_items_1230_);
v___x_1234_ = lean_nat_dec_lt(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref(v_items_1230_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1231_);
v___x_1236_ = v___x_1228_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_ref_1226_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
else
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_nat_dec_le(v___x_1233_, v___x_1233_);
if (v___x_1238_ == 0)
{
if (v___x_1234_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v_items_1230_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1231_);
v___x_1240_ = v___x_1228_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_ref_1226_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1231_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
else
{
size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = lean_usize_of_nat(v___x_1233_);
lean_inc(v_ref_1226_);
v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1226_, v_items_1230_, v___x_1242_, v___x_1243_, v___x_1231_);
lean_dec_ref(v_items_1230_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1244_);
v___x_1246_ = v___x_1228_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_ref_1226_);
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
size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1248_ = ((size_t)0ULL);
v___x_1249_ = lean_usize_of_nat(v___x_1233_);
lean_inc(v_ref_1226_);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1226_, v_items_1230_, v___x_1248_, v___x_1249_, v___x_1231_);
lean_dec_ref(v_items_1230_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1250_);
v___x_1252_ = v___x_1228_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_ref_1226_);
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
}
case 5:
{
lean_object* v_ref_1255_; lean_object* v_xs_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1266_; 
v_ref_1255_ = lean_ctor_get(v_a_1224_, 0);
v_xs_1256_ = lean_ctor_get(v_a_1224_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_a_1224_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1258_ = v_a_1224_;
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_xs_1256_);
lean_inc(v_ref_1255_);
lean_dec(v_a_1224_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
size_t v_sz_1260_; size_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v_sz_1260_ = lean_array_size(v_xs_1256_);
v___x_1261_ = ((size_t)0ULL);
v___x_1262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1260_, v___x_1261_, v_xs_1256_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1262_);
v___x_1264_ = v___x_1258_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_ref_1255_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
default: 
{
return v_a_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1267_, lean_object* v___x_1268_, lean_object* v_v_x3f_1269_){
_start:
{
if (lean_obj_tag(v_v_x3f_1269_) == 1)
{
lean_object* v_val_1270_; 
v_val_1270_ = lean_ctor_get(v_v_x3f_1269_, 0);
lean_inc(v_val_1270_);
lean_dec_ref(v_v_x3f_1269_);
switch(lean_obj_tag(v_val_1270_))
{
case 6:
{
lean_object* v_ref_1271_; lean_object* v_xs_1272_; lean_object* v___x_1273_; 
v_ref_1271_ = lean_ctor_get(v_val_1270_, 0);
lean_inc(v_ref_1271_);
v_xs_1272_ = lean_ctor_get(v_val_1270_, 1);
lean_inc_ref(v_xs_1272_);
lean_dec_ref(v_val_1270_);
v___x_1273_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1267_);
if (lean_obj_tag(v___x_1273_) == 6)
{
lean_object* v_xs_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1283_; 
v_xs_1274_ = lean_ctor_get(v___x_1273_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v___x_1273_, 0);
lean_dec(v_unused_1284_);
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_xs_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_items_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v_items_1278_ = lean_ctor_get(v_xs_1274_, 0);
lean_inc_ref(v_items_1278_);
lean_dec_ref(v_xs_1274_);
v___x_1279_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1268_, v_xs_1272_, v_items_1278_);
lean_dec_ref(v_items_1278_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1279_);
lean_ctor_set(v___x_1276_, 0, v_ref_1271_);
v___x_1281_ = v___x_1276_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_ref_1271_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_dec_ref(v_xs_1272_);
lean_dec(v_ref_1271_);
lean_dec_ref(v___x_1268_);
return v___x_1273_;
}
}
case 5:
{
lean_object* v_ref_1285_; lean_object* v_xs_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v___x_1268_);
v_ref_1285_ = lean_ctor_get(v_val_1270_, 0);
v_xs_1286_ = lean_ctor_get(v_val_1270_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_val_1270_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1288_ = v_val_1270_;
v_isShared_1289_ = v_isSharedCheck_1305_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_xs_1286_);
lean_inc(v_ref_1285_);
lean_dec(v_val_1270_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1305_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; 
v___x_1290_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1267_);
if (lean_obj_tag(v___x_1290_) == 5)
{
lean_object* v_xs_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
lean_del_object(v___x_1288_);
v_xs_1291_ = lean_ctor_get(v___x_1290_, 1);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v___x_1290_, 0);
lean_dec(v_unused_1300_);
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_xs_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = l_Array_append___redArg(v_xs_1286_, v_xs_1291_);
lean_dec_ref(v_xs_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v___x_1295_);
lean_ctor_set(v___x_1293_, 0, v_ref_1285_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_ref_1285_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_array_push(v_xs_1286_, v___x_1290_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___x_1301_);
v___x_1303_ = v___x_1288_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_ref_1285_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
default: 
{
lean_object* v___x_1306_; 
lean_dec(v_val_1270_);
lean_dec_ref(v___x_1268_);
v___x_1306_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1267_);
return v___x_1306_;
}
}
}
else
{
lean_object* v___x_1307_; 
lean_dec(v_v_x3f_1269_);
lean_dec_ref(v___x_1268_);
v___x_1307_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1267_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1308_, lean_object* v_k_1309_, lean_object* v_t_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1310_);
lean_inc(v_k_1309_);
v___x_1312_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1311_, v_k_1309_, v_t_1310_);
if (lean_obj_tag(v___x_1312_) == 1)
{
lean_object* v_val_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v_k_1309_);
v_val_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1348_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_val_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1348_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_items_1317_; lean_object* v_indices_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1347_; 
v_items_1317_ = lean_ctor_get(v_t_1310_, 0);
v_indices_1318_ = lean_ctor_get(v_t_1310_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_t_1310_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1320_ = v_t_1310_;
v_isShared_1321_ = v_isSharedCheck_1347_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_indices_1318_);
lean_inc(v_items_1317_);
lean_dec(v_t_1310_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1347_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_array_get_size(v_items_1317_);
v___x_1323_ = lean_nat_dec_lt(v_val_1313_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1325_; 
lean_del_object(v___x_1315_);
lean_dec(v_val_1313_);
lean_dec_ref(v_newV_1308_);
if (v_isShared_1321_ == 0)
{
v___x_1325_ = v___x_1320_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_items_1317_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_indices_1318_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
else
{
lean_object* v_v_1327_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1346_; 
v_v_1327_ = lean_array_fget(v_items_1317_, v_val_1313_);
v_fst_1328_ = lean_ctor_get(v_v_1327_, 0);
v_snd_1329_ = lean_ctor_get(v_v_1327_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_v_1327_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1331_ = v_v_1327_;
v_isShared_1332_ = v_isSharedCheck_1346_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_snd_1329_);
lean_inc(v_fst_1328_);
lean_dec(v_v_1327_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1346_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v_xs_x27_1334_; lean_object* v___x_1336_; 
v___x_1333_ = lean_box(0);
v_xs_x27_1334_ = lean_array_fset(v_items_1317_, v_val_1313_, v___x_1333_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v_snd_1329_);
v___x_1336_ = v___x_1315_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_snd_1329_);
v___x_1336_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1308_, v___x_1311_, v___x_1336_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___x_1337_);
v___x_1339_ = v___x_1331_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_fst_1328_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = lean_array_fset(v_xs_x27_1334_, v_val_1313_, v___x_1339_);
lean_dec(v_val_1313_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1340_);
v___x_1342_ = v___x_1320_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_indices_1318_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
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
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec(v___x_1312_);
v___x_1349_ = lean_box(0);
v___x_1350_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1308_, v___x_1311_, v___x_1349_);
v___x_1351_ = l_Lake_Toml_RBDict_push___redArg(v___x_1311_, v_k_1309_, v___x_1350_, v_t_1310_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1352_, lean_object* v_head_1353_, lean_object* v_tail_1354_, lean_object* v_newV_1355_, lean_object* v___x_1356_, lean_object* v_v_x3f_1357_){
_start:
{
if (lean_obj_tag(v_v_x3f_1357_) == 1)
{
lean_object* v_val_1358_; 
v_val_1358_ = lean_ctor_get(v_v_x3f_1357_, 0);
lean_inc(v_val_1358_);
lean_dec_ref(v_v_x3f_1357_);
switch(lean_obj_tag(v_val_1358_))
{
case 5:
{
lean_object* v_ref_1359_; lean_object* v_xs_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_ref_1359_ = lean_ctor_get(v_val_1358_, 0);
v_xs_1360_ = lean_ctor_get(v_val_1358_, 1);
v___x_1361_ = lean_array_get_size(v_xs_1360_);
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_nat_sub(v___x_1361_, v___x_1362_);
v___x_1364_ = lean_nat_dec_lt(v___x_1363_, v___x_1361_);
if (v___x_1364_ == 0)
{
lean_dec(v___x_1363_);
lean_dec_ref(v_newV_1355_);
lean_dec(v_tail_1354_);
lean_dec(v_head_1353_);
lean_dec(v_kRef_1352_);
return v_val_1358_;
}
else
{
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1389_; 
lean_inc_ref(v_xs_1360_);
lean_inc(v_ref_1359_);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_val_1358_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; lean_object* v_unused_1391_; 
v_unused_1390_ = lean_ctor_get(v_val_1358_, 1);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_val_1358_, 0);
lean_dec(v_unused_1391_);
v___x_1366_ = v_val_1358_;
v_isShared_1367_ = v_isSharedCheck_1389_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v_val_1358_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1389_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_v_1368_; lean_object* v___x_1369_; lean_object* v_xs_x27_1370_; lean_object* v___y_1372_; 
v_v_1368_ = lean_array_fget(v_xs_1360_, v___x_1363_);
v___x_1369_ = lean_box(0);
v_xs_x27_1370_ = lean_array_fset(v_xs_1360_, v___x_1363_, v___x_1369_);
if (lean_obj_tag(v_v_1368_) == 6)
{
lean_object* v_ref_1377_; lean_object* v_xs_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1386_; 
v_ref_1377_ = lean_ctor_get(v_v_1368_, 0);
v_xs_1378_ = lean_ctor_get(v_v_1368_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_v_1368_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1380_ = v_v_1368_;
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_xs_1378_);
lean_inc(v_ref_1377_);
lean_dec(v_v_1368_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1378_, v_kRef_1352_, v_head_1353_, v_tail_1354_, v_newV_1355_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1382_);
v___x_1384_ = v___x_1380_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_ref_1377_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
v___y_1372_ = v___x_1384_;
goto v___jp_1371_;
}
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v_v_1368_);
lean_dec_ref(v_newV_1355_);
lean_dec(v_tail_1354_);
lean_dec(v_head_1353_);
v___x_1387_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1356_);
v___x_1388_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_kRef_1352_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___y_1372_ = v___x_1388_;
goto v___jp_1371_;
}
v___jp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_array_fset(v_xs_x27_1370_, v___x_1363_, v___y_1372_);
lean_dec(v___x_1363_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v___x_1373_);
v___x_1375_ = v___x_1366_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_ref_1359_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1392_; lean_object* v_xs_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1401_; 
v_ref_1392_ = lean_ctor_get(v_val_1358_, 0);
v_xs_1393_ = lean_ctor_get(v_val_1358_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_val_1358_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1395_ = v_val_1358_;
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_xs_1393_);
lean_inc(v_ref_1392_);
lean_dec(v_val_1358_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1393_, v_kRef_1352_, v_head_1353_, v_tail_1354_, v_newV_1355_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_ref_1392_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
default: 
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_val_1358_);
v___x_1402_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1356_);
lean_inc(v_kRef_1352_);
v___x_1403_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1402_, v_kRef_1352_, v_head_1353_, v_tail_1354_, v_newV_1355_);
v___x_1404_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_kRef_1352_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
return v___x_1404_;
}
}
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec(v_v_x3f_1357_);
v___x_1405_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1356_);
lean_inc(v_kRef_1352_);
v___x_1406_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1405_, v_kRef_1352_, v_head_1353_, v_tail_1354_, v_newV_1355_);
v___x_1407_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_kRef_1352_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1408_, lean_object* v_head_1409_, lean_object* v_tail_1410_, lean_object* v_newV_1411_, lean_object* v_k_1412_, lean_object* v_t_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1413_);
lean_inc(v_k_1412_);
v___x_1415_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1414_, v_k_1412_, v_t_1413_);
if (lean_obj_tag(v___x_1415_) == 1)
{
lean_object* v_val_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_k_1412_);
v_val_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1451_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_val_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1451_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_items_1420_; lean_object* v_indices_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1450_; 
v_items_1420_ = lean_ctor_get(v_t_1413_, 0);
v_indices_1421_ = lean_ctor_get(v_t_1413_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_t_1413_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1423_ = v_t_1413_;
v_isShared_1424_ = v_isSharedCheck_1450_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_indices_1421_);
lean_inc(v_items_1420_);
lean_dec(v_t_1413_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1450_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = lean_array_get_size(v_items_1420_);
v___x_1426_ = lean_nat_dec_lt(v_val_1416_, v___x_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1428_; 
lean_del_object(v___x_1418_);
lean_dec(v_val_1416_);
lean_dec_ref(v_newV_1411_);
lean_dec(v_tail_1410_);
lean_dec(v_head_1409_);
lean_dec(v_kRef_1408_);
if (v_isShared_1424_ == 0)
{
v___x_1428_ = v___x_1423_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_items_1420_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_indices_1421_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
else
{
lean_object* v_v_1430_; lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1449_; 
v_v_1430_ = lean_array_fget(v_items_1420_, v_val_1416_);
v_fst_1431_ = lean_ctor_get(v_v_1430_, 0);
v_snd_1432_ = lean_ctor_get(v_v_1430_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_v_1430_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1434_ = v_v_1430_;
v_isShared_1435_ = v_isSharedCheck_1449_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_inc(v_fst_1431_);
lean_dec(v_v_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1449_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v_xs_x27_1437_; lean_object* v___x_1439_; 
v___x_1436_ = lean_box(0);
v_xs_x27_1437_ = lean_array_fset(v_items_1420_, v_val_1416_, v___x_1436_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v_snd_1432_);
v___x_1439_ = v___x_1418_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_snd_1432_);
v___x_1439_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1408_, v_head_1409_, v_tail_1410_, v_newV_1411_, v___x_1414_, v___x_1439_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v___x_1440_);
v___x_1442_ = v___x_1434_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_fst_1431_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = lean_array_fset(v_xs_x27_1437_, v_val_1416_, v___x_1442_);
lean_dec(v_val_1416_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1443_);
v___x_1445_ = v___x_1423_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_indices_1421_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
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
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec(v___x_1415_);
v___x_1452_ = lean_box(0);
v___x_1453_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1408_, v_head_1409_, v_tail_1410_, v_newV_1411_, v___x_1414_, v___x_1452_);
v___x_1454_ = l_Lake_Toml_RBDict_push___redArg(v___x_1414_, v_k_1412_, v___x_1453_, v_t_1413_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1455_, lean_object* v_kRef_1456_, lean_object* v_k_1457_, lean_object* v_ks_1458_, lean_object* v_newV_1459_){
_start:
{
if (lean_obj_tag(v_ks_1458_) == 0)
{
lean_object* v___x_1460_; 
lean_dec(v_kRef_1456_);
v___x_1460_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1459_, v_k_1457_, v_t_1455_);
return v___x_1460_;
}
else
{
lean_object* v_head_1461_; lean_object* v_tail_1462_; lean_object* v___x_1463_; 
v_head_1461_ = lean_ctor_get(v_ks_1458_, 0);
lean_inc(v_head_1461_);
v_tail_1462_ = lean_ctor_get(v_ks_1458_, 1);
lean_inc(v_tail_1462_);
lean_dec_ref(v_ks_1458_);
v___x_1463_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1456_, v_head_1461_, v_tail_1462_, v_newV_1459_, v_k_1457_, v_t_1455_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1464_, lean_object* v_i_1465_, lean_object* v_bs_1466_){
_start:
{
size_t v_sz_boxed_1467_; size_t v_i_boxed_1468_; lean_object* v_res_1469_; 
v_sz_boxed_1467_ = lean_unbox_usize(v_sz_1464_);
lean_dec(v_sz_1464_);
v_i_boxed_1468_ = lean_unbox_usize(v_i_1465_);
lean_dec(v_i_1465_);
v_res_1469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1467_, v_i_boxed_1468_, v_bs_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1470_, lean_object* v_as_1471_, lean_object* v_i_1472_, lean_object* v_stop_1473_, lean_object* v_b_1474_){
_start:
{
size_t v_i_boxed_1475_; size_t v_stop_boxed_1476_; lean_object* v_res_1477_; 
v_i_boxed_1475_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_stop_boxed_1476_ = lean_unbox_usize(v_stop_1473_);
lean_dec(v_stop_1473_);
v_res_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1470_, v_as_1471_, v_i_boxed_1475_, v_stop_boxed_1476_, v_b_1474_);
lean_dec_ref(v_as_1471_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0___boxed(lean_object* v_kRef_1478_, lean_object* v_head_1479_, lean_object* v_tail_1480_, lean_object* v_newV_1481_, lean_object* v___x_1482_, lean_object* v_v_x3f_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1478_, v_head_1479_, v_tail_1480_, v_newV_1481_, v___x_1482_, v_v_x3f_1483_);
lean_dec_ref(v___x_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1485_, size_t v_i_1486_, size_t v_stop_1487_, lean_object* v_b_1488_){
_start:
{
lean_object* v___y_1490_; uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_eq(v_i_1486_, v_stop_1487_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v_ref_1496_; lean_object* v_key_1497_; lean_object* v_val_1498_; lean_object* v___x_1499_; 
v___x_1495_ = lean_array_uget_borrowed(v_as_1485_, v_i_1486_);
v_ref_1496_ = lean_ctor_get(v___x_1495_, 0);
v_key_1497_ = lean_ctor_get(v___x_1495_, 1);
v_val_1498_ = lean_ctor_get(v___x_1495_, 2);
lean_inc(v_key_1497_);
v___x_1499_ = l_Lean_Name_components(v_key_1497_);
if (lean_obj_tag(v___x_1499_) == 0)
{
v___y_1490_ = v_b_1488_;
goto v___jp_1489_;
}
else
{
lean_object* v_head_1500_; lean_object* v_tail_1501_; lean_object* v___x_1502_; 
v_head_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_head_1500_);
v_tail_1501_ = lean_ctor_get(v___x_1499_, 1);
lean_inc(v_tail_1501_);
lean_dec_ref(v___x_1499_);
lean_inc_ref(v_val_1498_);
lean_inc(v_ref_1496_);
v___x_1502_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1488_, v_ref_1496_, v_head_1500_, v_tail_1501_, v_val_1498_);
v___y_1490_ = v___x_1502_;
goto v___jp_1489_;
}
}
else
{
return v_b_1488_;
}
v___jp_1489_:
{
size_t v___x_1491_; size_t v___x_1492_; 
v___x_1491_ = ((size_t)1ULL);
v___x_1492_ = lean_usize_add(v_i_1486_, v___x_1491_);
v_i_1486_ = v___x_1492_;
v_b_1488_ = v___y_1490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1503_, lean_object* v_i_1504_, lean_object* v_stop_1505_, lean_object* v_b_1506_){
_start:
{
size_t v_i_boxed_1507_; size_t v_stop_boxed_1508_; lean_object* v_res_1509_; 
v_i_boxed_1507_ = lean_unbox_usize(v_i_1504_);
lean_dec(v_i_1504_);
v_stop_boxed_1508_ = lean_unbox_usize(v_stop_1505_);
lean_dec(v_stop_1505_);
v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1503_, v_i_boxed_1507_, v_stop_boxed_1508_, v_b_1506_);
lean_dec_ref(v_as_1503_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1511_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_array_get_size(v_items_1510_);
v___x_1514_ = lean_nat_dec_lt(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
return v___x_1511_;
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_nat_dec_le(v___x_1513_, v___x_1513_);
if (v___x_1515_ == 0)
{
if (v___x_1514_ == 0)
{
return v___x_1511_;
}
else
{
size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = lean_usize_of_nat(v___x_1513_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1510_, v___x_1516_, v___x_1517_, v___x_1511_);
return v___x_1518_;
}
}
else
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = lean_usize_of_nat(v___x_1513_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1510_, v___x_1519_, v___x_1520_, v___x_1511_);
return v___x_1521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1522_);
lean_dec_ref(v_items_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1526_);
lean_inc_ref(v_a_1525_);
v___x_1529_ = lean_apply_4(v_x_1524_, v___x_1528_, v_a_1525_, v_a_1526_, lean_box(0));
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1540_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_snd_1534_; lean_object* v_items_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v_snd_1534_ = lean_ctor_get(v_a_1530_, 1);
lean_inc(v_snd_1534_);
lean_dec(v_a_1530_);
v_items_1535_ = lean_ctor_get(v_snd_1534_, 5);
lean_inc_ref(v_items_1535_);
lean_dec(v_snd_1534_);
v___x_1536_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1535_);
lean_dec_ref(v_items_1535_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1536_);
v___x_1538_ = v___x_1532_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1541_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1529_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1529_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1549_, v_a_1550_, v_a_1551_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
return v_res_1553_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v___y_1562_, uint8_t v_suppressElabErrors_1563_, lean_object* v_x_1564_){
_start:
{
if (lean_obj_tag(v_x_1564_) == 1)
{
lean_object* v_pre_1565_; 
v_pre_1565_ = lean_ctor_get(v_x_1564_, 0);
switch(lean_obj_tag(v_pre_1565_))
{
case 1:
{
lean_object* v_pre_1566_; 
v_pre_1566_ = lean_ctor_get(v_pre_1565_, 0);
switch(lean_obj_tag(v_pre_1566_))
{
case 0:
{
lean_object* v_str_1567_; lean_object* v_str_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_str_1567_ = lean_ctor_get(v_x_1564_, 1);
v_str_1568_ = lean_ctor_get(v_pre_1565_, 1);
v___x_1569_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1570_ = lean_string_dec_eq(v_str_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1572_ = lean_string_dec_eq(v_str_1568_, v___x_1571_);
if (v___x_1572_ == 0)
{
return v___y_1562_;
}
else
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1574_ = lean_string_dec_eq(v_str_1567_, v___x_1573_);
if (v___x_1574_ == 0)
{
return v___y_1562_;
}
else
{
return v_suppressElabErrors_1563_;
}
}
}
else
{
lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1576_ = lean_string_dec_eq(v_str_1567_, v___x_1575_);
if (v___x_1576_ == 0)
{
return v___y_1562_;
}
else
{
return v_suppressElabErrors_1563_;
}
}
}
case 1:
{
lean_object* v_pre_1577_; 
v_pre_1577_ = lean_ctor_get(v_pre_1566_, 0);
if (lean_obj_tag(v_pre_1577_) == 0)
{
lean_object* v_str_1578_; lean_object* v_str_1579_; lean_object* v_str_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v_str_1578_ = lean_ctor_get(v_x_1564_, 1);
v_str_1579_ = lean_ctor_get(v_pre_1565_, 1);
v_str_1580_ = lean_ctor_get(v_pre_1566_, 1);
v___x_1581_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1582_ = lean_string_dec_eq(v_str_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
return v___y_1562_;
}
else
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1584_ = lean_string_dec_eq(v_str_1579_, v___x_1583_);
if (v___x_1584_ == 0)
{
return v___y_1562_;
}
else
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1586_ = lean_string_dec_eq(v_str_1578_, v___x_1585_);
if (v___x_1586_ == 0)
{
return v___y_1562_;
}
else
{
return v_suppressElabErrors_1563_;
}
}
}
}
else
{
return v___y_1562_;
}
}
default: 
{
return v___y_1562_;
}
}
}
case 0:
{
lean_object* v_str_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_str_1587_ = lean_ctor_get(v_x_1564_, 1);
v___x_1588_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1589_ = lean_string_dec_eq(v_str_1587_, v___x_1588_);
if (v___x_1589_ == 0)
{
return v___y_1562_;
}
else
{
return v_suppressElabErrors_1563_;
}
}
default: 
{
return v___y_1562_;
}
}
}
else
{
return v___y_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v___y_1590_, lean_object* v_suppressElabErrors_1591_, lean_object* v_x_1592_){
_start:
{
uint8_t v___y_11739__boxed_1593_; uint8_t v_suppressElabErrors_boxed_1594_; uint8_t v_res_1595_; lean_object* v_r_1596_; 
v___y_11739__boxed_1593_ = lean_unbox(v___y_1590_);
v_suppressElabErrors_boxed_1594_ = lean_unbox(v_suppressElabErrors_1591_);
v_res_1595_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v___y_11739__boxed_1593_, v_suppressElabErrors_boxed_1594_, v_x_1592_);
lean_dec(v_x_1592_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1597_, lean_object* v_opt_1598_){
_start:
{
lean_object* v_name_1599_; lean_object* v_defValue_1600_; lean_object* v_map_1601_; lean_object* v___x_1602_; 
v_name_1599_ = lean_ctor_get(v_opt_1598_, 0);
v_defValue_1600_ = lean_ctor_get(v_opt_1598_, 1);
v_map_1601_ = lean_ctor_get(v_opts_1597_, 0);
v___x_1602_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1601_, v_name_1599_);
if (lean_obj_tag(v___x_1602_) == 0)
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_unbox(v_defValue_1600_);
return v___x_1603_;
}
else
{
lean_object* v_val_1604_; 
v_val_1604_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_val_1604_);
lean_dec_ref(v___x_1602_);
if (lean_obj_tag(v_val_1604_) == 1)
{
uint8_t v_v_1605_; 
v_v_1605_ = lean_ctor_get_uint8(v_val_1604_, 0);
lean_dec_ref(v_val_1604_);
return v_v_1605_;
}
else
{
uint8_t v___x_1606_; 
lean_dec(v_val_1604_);
v___x_1606_ = lean_unbox(v_defValue_1600_);
return v___x_1606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1607_, lean_object* v_opt_1608_){
_start:
{
uint8_t v_res_1609_; lean_object* v_r_1610_; 
v_res_1609_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1607_, v_opt_1608_);
lean_dec_ref(v_opt_1608_);
lean_dec_ref(v_opts_1607_);
v_r_1610_ = lean_box(v_res_1609_);
return v_r_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1612_, lean_object* v_msgData_1613_, uint8_t v_severity_1614_, uint8_t v_isSilent_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_a_1621_; lean_object* v___y_1625_; uint8_t v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; uint8_t v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1660_; uint8_t v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; uint8_t v___y_1665_; uint8_t v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1684_; uint8_t v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; uint8_t v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1695_; uint8_t v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; uint8_t v___y_1700_; uint8_t v___y_1701_; uint8_t v___x_1706_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; uint8_t v___y_1711_; lean_object* v___y_1712_; uint8_t v___y_1713_; uint8_t v___y_1714_; uint8_t v___y_1716_; uint8_t v___x_1732_; 
v___x_1706_ = 2;
v___x_1732_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1614_, v___x_1706_);
if (v___x_1732_ == 0)
{
v___y_1716_ = v___x_1732_;
goto v___jp_1715_;
}
else
{
uint8_t v___x_1733_; 
lean_inc_ref(v_msgData_1613_);
v___x_1733_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1613_);
v___y_1716_ = v___x_1733_;
goto v___jp_1715_;
}
v___jp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v_a_1621_);
lean_ctor_set(v___x_1622_, 1, v___y_1616_);
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
return v___x_1623_;
}
v___jp_1624_:
{
lean_object* v___x_1634_; lean_object* v_currNamespace_1635_; lean_object* v_openDecls_1636_; lean_object* v_env_1637_; lean_object* v_nextMacroScope_1638_; lean_object* v_ngen_1639_; lean_object* v_auxDeclNGen_1640_; lean_object* v_traceState_1641_; lean_object* v_cache_1642_; lean_object* v_messages_1643_; lean_object* v_infoState_1644_; lean_object* v_snapshotTasks_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1658_; 
v___x_1634_ = lean_st_ref_take(v___y_1633_);
v_currNamespace_1635_ = lean_ctor_get(v___y_1632_, 6);
v_openDecls_1636_ = lean_ctor_get(v___y_1632_, 7);
v_env_1637_ = lean_ctor_get(v___x_1634_, 0);
v_nextMacroScope_1638_ = lean_ctor_get(v___x_1634_, 1);
v_ngen_1639_ = lean_ctor_get(v___x_1634_, 2);
v_auxDeclNGen_1640_ = lean_ctor_get(v___x_1634_, 3);
v_traceState_1641_ = lean_ctor_get(v___x_1634_, 4);
v_cache_1642_ = lean_ctor_get(v___x_1634_, 5);
v_messages_1643_ = lean_ctor_get(v___x_1634_, 6);
v_infoState_1644_ = lean_ctor_get(v___x_1634_, 7);
v_snapshotTasks_1645_ = lean_ctor_get(v___x_1634_, 8);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1647_ = v___x_1634_;
v_isShared_1648_ = v_isSharedCheck_1658_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_snapshotTasks_1645_);
lean_inc(v_infoState_1644_);
lean_inc(v_messages_1643_);
lean_inc(v_cache_1642_);
lean_inc(v_traceState_1641_);
lean_inc(v_auxDeclNGen_1640_);
lean_inc(v_ngen_1639_);
lean_inc(v_nextMacroScope_1638_);
lean_inc(v_env_1637_);
lean_dec(v___x_1634_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1658_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
lean_inc(v_openDecls_1636_);
lean_inc(v_currNamespace_1635_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_currNamespace_1635_);
lean_ctor_set(v___x_1649_, 1, v_openDecls_1636_);
v___x_1650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v___y_1629_);
lean_inc_ref(v___y_1627_);
lean_inc_ref(v___y_1630_);
v___x_1651_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1651_, 0, v___y_1630_);
lean_ctor_set(v___x_1651_, 1, v___y_1628_);
lean_ctor_set(v___x_1651_, 2, v___y_1625_);
lean_ctor_set(v___x_1651_, 3, v___y_1627_);
lean_ctor_set(v___x_1651_, 4, v___x_1650_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*5, v___y_1626_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*5 + 1, v___y_1631_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*5 + 2, v_isSilent_1615_);
v___x_1652_ = l_Lean_MessageLog_add(v___x_1651_, v_messages_1643_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 6, v___x_1652_);
v___x_1654_ = v___x_1647_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_env_1637_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_nextMacroScope_1638_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_ngen_1639_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_auxDeclNGen_1640_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_traceState_1641_);
lean_ctor_set(v_reuseFailAlloc_1657_, 5, v_cache_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 6, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1657_, 7, v_infoState_1644_);
lean_ctor_set(v_reuseFailAlloc_1657_, 8, v_snapshotTasks_1645_);
v___x_1654_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_st_ref_set(v___y_1633_, v___x_1654_);
v___x_1656_ = lean_box(0);
v_a_1621_ = v___x_1656_;
goto v___jp_1620_;
}
}
}
v___jp_1659_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1682_; 
v___x_1668_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1613_);
v___x_1669_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1668_, v___y_1617_, v___y_1618_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1682_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1682_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
lean_inc_ref_n(v___y_1663_, 2);
v___x_1674_ = l_Lean_FileMap_toPosition(v___y_1663_, v___y_1662_);
lean_dec(v___y_1662_);
v___x_1675_ = l_Lean_FileMap_toPosition(v___y_1663_, v___y_1667_);
lean_dec(v___y_1667_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 1);
lean_ctor_set(v___x_1672_, 0, v___x_1675_);
v___x_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1666_ == 0)
{
lean_dec_ref(v___y_1660_);
v___y_1625_ = v___x_1677_;
v___y_1626_ = v___y_1661_;
v___y_1627_ = v___x_1678_;
v___y_1628_ = v___x_1674_;
v___y_1629_ = v_a_1670_;
v___y_1630_ = v___y_1664_;
v___y_1631_ = v___y_1665_;
v___y_1632_ = v___y_1617_;
v___y_1633_ = v___y_1618_;
goto v___jp_1624_;
}
else
{
uint8_t v___x_1679_; 
lean_inc(v_a_1670_);
v___x_1679_ = l_Lean_MessageData_hasTag(v___y_1660_, v_a_1670_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
lean_dec_ref(v___x_1677_);
lean_dec_ref(v___x_1674_);
lean_dec(v_a_1670_);
v___x_1680_ = lean_box(0);
v_a_1621_ = v___x_1680_;
goto v___jp_1620_;
}
else
{
v___y_1625_ = v___x_1677_;
v___y_1626_ = v___y_1661_;
v___y_1627_ = v___x_1678_;
v___y_1628_ = v___x_1674_;
v___y_1629_ = v_a_1670_;
v___y_1630_ = v___y_1664_;
v___y_1631_ = v___y_1665_;
v___y_1632_ = v___y_1617_;
v___y_1633_ = v___y_1618_;
goto v___jp_1624_;
}
}
}
}
}
v___jp_1683_:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Syntax_getTailPos_x3f(v___y_1686_, v___y_1685_);
lean_dec(v___y_1686_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_inc(v___y_1691_);
v___y_1660_ = v___y_1684_;
v___y_1661_ = v___y_1685_;
v___y_1662_ = v___y_1691_;
v___y_1663_ = v___y_1687_;
v___y_1664_ = v___y_1688_;
v___y_1665_ = v___y_1689_;
v___y_1666_ = v___y_1690_;
v___y_1667_ = v___y_1691_;
goto v___jp_1659_;
}
else
{
lean_object* v_val_1693_; 
v_val_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_val_1693_);
lean_dec_ref(v___x_1692_);
v___y_1660_ = v___y_1684_;
v___y_1661_ = v___y_1685_;
v___y_1662_ = v___y_1691_;
v___y_1663_ = v___y_1687_;
v___y_1664_ = v___y_1688_;
v___y_1665_ = v___y_1689_;
v___y_1666_ = v___y_1690_;
v___y_1667_ = v_val_1693_;
goto v___jp_1659_;
}
}
v___jp_1694_:
{
lean_object* v_ref_1702_; lean_object* v___x_1703_; 
v_ref_1702_ = l_Lean_replaceRef(v_ref_1612_, v___y_1699_);
v___x_1703_ = l_Lean_Syntax_getPos_x3f(v_ref_1702_, v___y_1696_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_unsigned_to_nat(0u);
v___y_1684_ = v___y_1695_;
v___y_1685_ = v___y_1696_;
v___y_1686_ = v_ref_1702_;
v___y_1687_ = v___y_1697_;
v___y_1688_ = v___y_1698_;
v___y_1689_ = v___y_1701_;
v___y_1690_ = v___y_1700_;
v___y_1691_ = v___x_1704_;
goto v___jp_1683_;
}
else
{
lean_object* v_val_1705_; 
v_val_1705_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_val_1705_);
lean_dec_ref(v___x_1703_);
v___y_1684_ = v___y_1695_;
v___y_1685_ = v___y_1696_;
v___y_1686_ = v_ref_1702_;
v___y_1687_ = v___y_1697_;
v___y_1688_ = v___y_1698_;
v___y_1689_ = v___y_1701_;
v___y_1690_ = v___y_1700_;
v___y_1691_ = v_val_1705_;
goto v___jp_1683_;
}
}
v___jp_1707_:
{
if (v___y_1714_ == 0)
{
v___y_1695_ = v___y_1712_;
v___y_1696_ = v___y_1713_;
v___y_1697_ = v___y_1708_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1709_;
v___y_1700_ = v___y_1711_;
v___y_1701_ = v_severity_1614_;
goto v___jp_1694_;
}
else
{
v___y_1695_ = v___y_1712_;
v___y_1696_ = v___y_1713_;
v___y_1697_ = v___y_1708_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1709_;
v___y_1700_ = v___y_1711_;
v___y_1701_ = v___x_1706_;
goto v___jp_1694_;
}
}
v___jp_1715_:
{
if (v___y_1716_ == 0)
{
lean_object* v_fileName_1717_; lean_object* v_fileMap_1718_; lean_object* v_options_1719_; lean_object* v_ref_1720_; uint8_t v_suppressElabErrors_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___f_1724_; uint8_t v___x_1725_; uint8_t v___x_1726_; 
v_fileName_1717_ = lean_ctor_get(v___y_1617_, 0);
v_fileMap_1718_ = lean_ctor_get(v___y_1617_, 1);
v_options_1719_ = lean_ctor_get(v___y_1617_, 2);
v_ref_1720_ = lean_ctor_get(v___y_1617_, 5);
v_suppressElabErrors_1721_ = lean_ctor_get_uint8(v___y_1617_, sizeof(void*)*14 + 1);
v___x_1722_ = lean_box(v___y_1716_);
v___x_1723_ = lean_box(v_suppressElabErrors_1721_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1724_, 0, v___x_1722_);
lean_closure_set(v___f_1724_, 1, v___x_1723_);
v___x_1725_ = 1;
v___x_1726_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1614_, v___x_1725_);
if (v___x_1726_ == 0)
{
v___y_1708_ = v_fileMap_1718_;
v___y_1709_ = v_ref_1720_;
v___y_1710_ = v_fileName_1717_;
v___y_1711_ = v_suppressElabErrors_1721_;
v___y_1712_ = v___f_1724_;
v___y_1713_ = v___y_1716_;
v___y_1714_ = v___x_1726_;
goto v___jp_1707_;
}
else
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = l_Lean_warningAsError;
v___x_1728_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_options_1719_, v___x_1727_);
v___y_1708_ = v_fileMap_1718_;
v___y_1709_ = v_ref_1720_;
v___y_1710_ = v_fileName_1717_;
v___y_1711_ = v_suppressElabErrors_1721_;
v___y_1712_ = v___f_1724_;
v___y_1713_ = v___y_1716_;
v___y_1714_ = v___x_1728_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v_msgData_1613_);
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v___y_1616_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1734_, lean_object* v_msgData_1735_, lean_object* v_severity_1736_, lean_object* v_isSilent_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v_severity_boxed_1742_; uint8_t v_isSilent_boxed_1743_; lean_object* v_res_1744_; 
v_severity_boxed_1742_ = lean_unbox(v_severity_1736_);
v_isSilent_boxed_1743_ = lean_unbox(v_isSilent_1737_);
v_res_1744_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1734_, v_msgData_1735_, v_severity_boxed_1742_, v_isSilent_boxed_1743_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v_ref_1734_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1745_, lean_object* v_msgData_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
uint8_t v___x_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = 2;
v___x_1752_ = 0;
v___x_1753_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1745_, v_msgData_1746_, v___x_1751_, v___x_1752_, v___y_1747_, v___y_1748_, v___y_1749_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1754_, lean_object* v_msgData_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1754_, v_msgData_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v_ref_1754_);
return v_res_1760_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1764_ = l_Lean_MessageData_ofFormat(v___x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1765_, lean_object* v_as_1766_, size_t v_sz_1767_, size_t v_i_1768_, uint8_t v_b_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_snd_1775_; lean_object* v_snd_1776_; lean_object* v___y_1782_; uint8_t v___y_1783_; lean_object* v_a_1800_; uint8_t v___x_1803_; 
v___x_1803_ = lean_usize_dec_lt(v_i_1768_, v_sz_1767_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_box(v_b_1769_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v___y_1770_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1808_; uint8_t v_recovering_1809_; 
v_a_1807_ = lean_array_uget_borrowed(v_as_1766_, v_i_1768_);
v___x_1808_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1807_);
v_recovering_1809_ = l_Lean_Syntax_isOfKind(v_a_1807_, v___x_1808_);
if (v_recovering_1809_ == 0)
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_a_1807_);
v___x_1811_ = l_Lean_Syntax_isOfKind(v_a_1807_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1807_);
v___x_1813_ = l_Lean_Syntax_isOfKind(v_a_1807_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1770_);
v___x_1815_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1807_, v___x_1814_, v___y_1770_, v___y_1771_, v___y_1772_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v_snd_1817_; lean_object* v___x_1818_; 
lean_dec_ref(v___y_1770_);
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v___x_1815_);
v_snd_1817_ = lean_ctor_get(v_a_1816_, 1);
lean_inc(v_snd_1817_);
lean_dec(v_a_1816_);
v___x_1818_ = lean_box(v_b_1769_);
v_snd_1775_ = v___x_1818_;
v_snd_1776_ = v_snd_1817_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1819_; 
v_a_1819_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1815_);
v_a_1800_ = v_a_1819_;
goto v___jp_1799_;
}
}
else
{
lean_object* v___x_1820_; 
lean_inc_ref(v___y_1770_);
lean_inc(v_a_1807_);
v___x_1820_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1807_, v___y_1770_, v___y_1771_, v___y_1772_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v_snd_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v___y_1770_);
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1820_);
v_snd_1822_ = lean_ctor_get(v_a_1821_, 1);
lean_inc(v_snd_1822_);
lean_dec(v_a_1821_);
v___x_1823_ = lean_box(v_recovering_1809_);
v_snd_1775_ = v___x_1823_;
v_snd_1776_ = v_snd_1822_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1824_; 
v_a_1824_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1820_);
v_a_1800_ = v_a_1824_;
goto v___jp_1799_;
}
}
}
else
{
lean_object* v___x_1825_; 
lean_inc_ref(v___y_1770_);
lean_inc(v_a_1807_);
v___x_1825_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1807_, v___y_1770_, v___y_1771_, v___y_1772_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v_snd_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v___y_1770_);
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref(v___x_1825_);
v_snd_1827_ = lean_ctor_get(v_a_1826_, 1);
lean_inc(v_snd_1827_);
lean_dec(v_a_1826_);
v___x_1828_ = lean_box(v_recovering_1809_);
v_snd_1775_ = v___x_1828_;
v_snd_1776_ = v_snd_1827_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1829_; 
v_a_1829_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v___x_1825_);
v_a_1800_ = v_a_1829_;
goto v___jp_1799_;
}
}
}
else
{
if (v_b_1769_ == 0)
{
lean_object* v___x_1830_; 
lean_inc_ref(v___y_1770_);
lean_inc(v_a_1807_);
v___x_1830_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1807_, v___y_1770_, v___y_1771_, v___y_1772_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v_snd_1832_; lean_object* v___x_1833_; 
lean_dec_ref(v___y_1770_);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1830_);
v_snd_1832_ = lean_ctor_get(v_a_1831_, 1);
lean_inc(v_snd_1832_);
lean_dec(v_a_1831_);
v___x_1833_ = lean_box(v_b_1769_);
v_snd_1775_ = v___x_1833_;
v_snd_1776_ = v_snd_1832_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1834_; 
v_a_1834_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1830_);
v_a_1800_ = v_a_1834_;
goto v___jp_1799_;
}
}
else
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_box(v_b_1769_);
v_snd_1775_ = v___x_1835_;
v_snd_1776_ = v___y_1770_;
goto v___jp_1774_;
}
}
}
v___jp_1774_:
{
size_t v___x_1777_; size_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = ((size_t)1ULL);
v___x_1778_ = lean_usize_add(v_i_1768_, v___x_1777_);
v___x_1779_ = lean_unbox(v_snd_1775_);
lean_dec(v_snd_1775_);
v_i_1768_ = v___x_1778_;
v_b_1769_ = v___x_1779_;
v___y_1770_ = v_snd_1776_;
goto _start;
}
v___jp_1781_:
{
if (v___y_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = l_Lean_Exception_getRef(v___y_1782_);
v___x_1785_ = l_Lean_Exception_toMessageData(v___y_1782_);
v___x_1786_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1784_, v___x_1785_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___x_1784_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v_snd_1788_; lean_object* v___x_1789_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v___x_1786_);
v_snd_1788_ = lean_ctor_get(v_a_1787_, 1);
lean_inc(v_snd_1788_);
lean_dec(v_a_1787_);
v___x_1789_ = lean_box(v_recovering_1765_);
v_snd_1775_ = v___x_1789_;
v_snd_1776_ = v_snd_1788_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_a_1790_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1786_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1786_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
lean_object* v___x_1798_; 
lean_dec_ref(v___y_1770_);
v___x_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___y_1782_);
return v___x_1798_;
}
}
v___jp_1799_:
{
uint8_t v___x_1801_; 
v___x_1801_ = l_Lean_Exception_isInterrupt(v_a_1800_);
if (v___x_1801_ == 0)
{
uint8_t v___x_1802_; 
lean_inc_ref(v_a_1800_);
v___x_1802_ = l_Lean_Exception_isRuntime(v_a_1800_);
v___y_1782_ = v_a_1800_;
v___y_1783_ = v___x_1802_;
goto v___jp_1781_;
}
else
{
v___y_1782_ = v_a_1800_;
v___y_1783_ = v___x_1801_;
goto v___jp_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1836_, lean_object* v_as_1837_, lean_object* v_sz_1838_, lean_object* v_i_1839_, lean_object* v_b_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v_recovering_boxed_1845_; size_t v_sz_boxed_1846_; size_t v_i_boxed_1847_; uint8_t v_b_boxed_1848_; lean_object* v_res_1849_; 
v_recovering_boxed_1845_ = lean_unbox(v_recovering_1836_);
v_sz_boxed_1846_ = lean_unbox_usize(v_sz_1838_);
lean_dec(v_sz_1838_);
v_i_boxed_1847_ = lean_unbox_usize(v_i_1839_);
lean_dec(v_i_1839_);
v_b_boxed_1848_ = lean_unbox(v_b_1840_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1845_, v_as_1837_, v_sz_boxed_1846_, v_i_boxed_1847_, v_b_boxed_1848_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec_ref(v_as_1837_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_ref_1854_; lean_object* v___x_1855_; lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1864_; 
v_ref_1854_ = lean_ctor_get(v___y_1851_, 5);
v___x_1855_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1850_, v___y_1851_, v___y_1852_);
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
lean_inc(v_ref_1854_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v_ref_1854_);
lean_ctor_set(v___x_1860_, 1, v_a_1856_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set_tag(v___x_1858_, 1);
lean_ctor_set(v___x_1858_, 0, v___x_1860_);
v___x_1862_ = v___x_1858_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1870_, lean_object* v_msg_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_fileName_1875_; lean_object* v_fileMap_1876_; lean_object* v_options_1877_; lean_object* v_currRecDepth_1878_; lean_object* v_maxRecDepth_1879_; lean_object* v_ref_1880_; lean_object* v_currNamespace_1881_; lean_object* v_openDecls_1882_; lean_object* v_initHeartbeats_1883_; lean_object* v_maxHeartbeats_1884_; lean_object* v_quotContext_1885_; lean_object* v_currMacroScope_1886_; uint8_t v_diag_1887_; lean_object* v_cancelTk_x3f_1888_; uint8_t v_suppressElabErrors_1889_; lean_object* v_inheritedTraceOptions_1890_; lean_object* v_ref_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_fileName_1875_ = lean_ctor_get(v___y_1872_, 0);
v_fileMap_1876_ = lean_ctor_get(v___y_1872_, 1);
v_options_1877_ = lean_ctor_get(v___y_1872_, 2);
v_currRecDepth_1878_ = lean_ctor_get(v___y_1872_, 3);
v_maxRecDepth_1879_ = lean_ctor_get(v___y_1872_, 4);
v_ref_1880_ = lean_ctor_get(v___y_1872_, 5);
v_currNamespace_1881_ = lean_ctor_get(v___y_1872_, 6);
v_openDecls_1882_ = lean_ctor_get(v___y_1872_, 7);
v_initHeartbeats_1883_ = lean_ctor_get(v___y_1872_, 8);
v_maxHeartbeats_1884_ = lean_ctor_get(v___y_1872_, 9);
v_quotContext_1885_ = lean_ctor_get(v___y_1872_, 10);
v_currMacroScope_1886_ = lean_ctor_get(v___y_1872_, 11);
v_diag_1887_ = lean_ctor_get_uint8(v___y_1872_, sizeof(void*)*14);
v_cancelTk_x3f_1888_ = lean_ctor_get(v___y_1872_, 12);
v_suppressElabErrors_1889_ = lean_ctor_get_uint8(v___y_1872_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1890_ = lean_ctor_get(v___y_1872_, 13);
v_ref_1891_ = l_Lean_replaceRef(v_ref_1870_, v_ref_1880_);
lean_inc_ref(v_inheritedTraceOptions_1890_);
lean_inc(v_cancelTk_x3f_1888_);
lean_inc(v_currMacroScope_1886_);
lean_inc(v_quotContext_1885_);
lean_inc(v_maxHeartbeats_1884_);
lean_inc(v_initHeartbeats_1883_);
lean_inc(v_openDecls_1882_);
lean_inc(v_currNamespace_1881_);
lean_inc(v_maxRecDepth_1879_);
lean_inc(v_currRecDepth_1878_);
lean_inc_ref(v_options_1877_);
lean_inc_ref(v_fileMap_1876_);
lean_inc_ref(v_fileName_1875_);
v___x_1892_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1892_, 0, v_fileName_1875_);
lean_ctor_set(v___x_1892_, 1, v_fileMap_1876_);
lean_ctor_set(v___x_1892_, 2, v_options_1877_);
lean_ctor_set(v___x_1892_, 3, v_currRecDepth_1878_);
lean_ctor_set(v___x_1892_, 4, v_maxRecDepth_1879_);
lean_ctor_set(v___x_1892_, 5, v_ref_1891_);
lean_ctor_set(v___x_1892_, 6, v_currNamespace_1881_);
lean_ctor_set(v___x_1892_, 7, v_openDecls_1882_);
lean_ctor_set(v___x_1892_, 8, v_initHeartbeats_1883_);
lean_ctor_set(v___x_1892_, 9, v_maxHeartbeats_1884_);
lean_ctor_set(v___x_1892_, 10, v_quotContext_1885_);
lean_ctor_set(v___x_1892_, 11, v_currMacroScope_1886_);
lean_ctor_set(v___x_1892_, 12, v_cancelTk_x3f_1888_);
lean_ctor_set(v___x_1892_, 13, v_inheritedTraceOptions_1890_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14, v_diag_1887_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 1, v_suppressElabErrors_1889_);
v___x_1893_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1871_, v___x_1892_, v___y_1873_);
lean_dec_ref(v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1894_, lean_object* v_msg_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1894_, v_msg_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v_ref_1894_);
return v_res_1899_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1907_ = l_Lean_stringToMessageData(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1912_);
v___x_1917_ = l_Lean_Syntax_isOfKind(v_x_1912_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1919_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1912_, v___x_1918_, v_a_1913_, v_a_1914_);
lean_dec(v_x_1912_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v_recovering_1923_; 
v___x_1920_ = lean_unsigned_to_nat(0u);
v___x_1921_ = l_Lean_Syntax_getArg(v_x_1912_, v___x_1920_);
v___x_1922_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1923_ = l_Lean_Syntax_isOfKind(v___x_1921_, v___x_1922_);
if (v_recovering_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1925_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1912_, v___x_1924_, v_a_1913_, v_a_1914_);
lean_dec(v_x_1912_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_xs_1928_; uint8_t v_recovering_1929_; lean_object* v___x_1930_; size_t v_sz_1931_; size_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1926_ = lean_unsigned_to_nat(1u);
v___x_1927_ = l_Lean_Syntax_getArg(v_x_1912_, v___x_1926_);
lean_dec(v_x_1912_);
v_xs_1928_ = l_Lean_Syntax_getArgs(v___x_1927_);
lean_dec(v___x_1927_);
v_recovering_1929_ = 0;
v___x_1930_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1928_);
lean_dec_ref(v_xs_1928_);
v_sz_1931_ = lean_array_size(v___x_1930_);
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1923_, v___x_1930_, v_sz_1931_, v___x_1932_, v_recovering_1929_, v___x_1933_, v_a_1913_, v_a_1914_);
lean_dec_ref(v___x_1930_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1945_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1945_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1945_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_snd_1939_; lean_object* v_items_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
v_snd_1939_ = lean_ctor_get(v_a_1935_, 1);
lean_inc(v_snd_1939_);
lean_dec(v_a_1935_);
v_items_1940_ = lean_ctor_get(v_snd_1939_, 5);
lean_inc_ref(v_items_1940_);
lean_dec(v_snd_1939_);
v___x_1941_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1940_);
lean_dec_ref(v_items_1940_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1941_);
v___x_1943_ = v___x_1937_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1934_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1934_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lake_Toml_elabToml(v_x_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1959_, lean_object* v_ref_1960_, lean_object* v_msg_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1960_, v_msg_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_ref_1967_, lean_object* v_msg_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1966_, v_ref_1967_, v_msg_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_ref_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1973_, lean_object* v_msg_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1974_, v___y_1975_, v___y_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1979_, lean_object* v_msg_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1979_, v_msg_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1984_;
}
}
lean_object* runtime_initialize_Lake_Toml_Elab_Value(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Elab_Expression(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
