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
LEAN_EXPORT uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy_default;
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
static const lean_array_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__0_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__1_value;
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
static uint8_t _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy_default(void){
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
v___x_135_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
lean_ctor_set(v___x_135_, 2, v___x_134_);
lean_ctor_set(v___x_135_, 3, v___x_133_);
lean_ctor_set(v___x_135_, 4, v___x_133_);
lean_ctor_set(v___x_135_, 5, v___x_133_);
lean_ctor_set(v___x_135_, 6, v___x_133_);
lean_ctor_set(v___x_135_, 7, v___x_133_);
lean_ctor_set(v___x_135_, 8, v___x_133_);
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
lean_object* v_fileName_192_; lean_object* v_fileMap_193_; lean_object* v_options_194_; lean_object* v_currRecDepth_195_; lean_object* v_maxRecDepth_196_; lean_object* v_ref_197_; lean_object* v_currNamespace_198_; lean_object* v_openDecls_199_; lean_object* v_initHeartbeats_200_; lean_object* v_maxHeartbeats_201_; lean_object* v_quotContext_202_; lean_object* v_currMacroScope_203_; uint8_t v_diag_204_; lean_object* v_cancelTk_x3f_205_; uint8_t v_suppressElabErrors_206_; lean_object* v_inheritedTraceOptions_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_216_; 
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
v_isSharedCheck_216_ = !lean_is_exclusive(v___y_189_);
if (v_isSharedCheck_216_ == 0)
{
v___x_209_ = v___y_189_;
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_inheritedTraceOptions_207_);
lean_inc(v_cancelTk_x3f_205_);
lean_inc(v_currMacroScope_203_);
lean_inc(v_quotContext_202_);
lean_inc(v_maxHeartbeats_201_);
lean_inc(v_initHeartbeats_200_);
lean_inc(v_openDecls_199_);
lean_inc(v_currNamespace_198_);
lean_inc(v_ref_197_);
lean_inc(v_maxRecDepth_196_);
lean_inc(v_currRecDepth_195_);
lean_inc(v_options_194_);
lean_inc(v_fileMap_193_);
lean_inc(v_fileName_192_);
lean_dec(v___y_189_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_ref_211_; lean_object* v___x_213_; 
v_ref_211_ = l_Lean_replaceRef(v_ref_186_, v_ref_197_);
lean_dec(v_ref_197_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 5, v_ref_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_fileName_192_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_fileMap_193_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_options_194_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_currRecDepth_195_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_maxRecDepth_196_);
lean_ctor_set(v_reuseFailAlloc_215_, 5, v_ref_211_);
lean_ctor_set(v_reuseFailAlloc_215_, 6, v_currNamespace_198_);
lean_ctor_set(v_reuseFailAlloc_215_, 7, v_openDecls_199_);
lean_ctor_set(v_reuseFailAlloc_215_, 8, v_initHeartbeats_200_);
lean_ctor_set(v_reuseFailAlloc_215_, 9, v_maxHeartbeats_201_);
lean_ctor_set(v_reuseFailAlloc_215_, 10, v_quotContext_202_);
lean_ctor_set(v_reuseFailAlloc_215_, 11, v_currMacroScope_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 12, v_cancelTk_x3f_205_);
lean_ctor_set(v_reuseFailAlloc_215_, 13, v_inheritedTraceOptions_207_);
lean_ctor_set_uint8(v_reuseFailAlloc_215_, sizeof(void*)*14, v_diag_204_);
lean_ctor_set_uint8(v_reuseFailAlloc_215_, sizeof(void*)*14 + 1, v_suppressElabErrors_206_);
v___x_213_ = v_reuseFailAlloc_215_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_187_, v___x_213_, v___y_190_);
lean_dec_ref(v___x_213_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object* v_ref_217_, lean_object* v_msg_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_217_, v_msg_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_219_);
lean_dec(v_ref_217_);
return v_res_223_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_226_ = l_Lean_stringToMessageData(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_229_ = l_Lean_stringToMessageData(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object* v_as_233_, size_t v_i_234_, size_t v_stop_235_, lean_object* v_b_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_fst_242_; lean_object* v_snd_243_; uint8_t v___x_247_; 
v___x_247_ = lean_usize_dec_eq(v_i_234_, v_stop_235_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_array_uget_borrowed(v_as_233_, v_i_234_);
lean_inc_ref(v___y_238_);
lean_inc(v___x_248_);
v___x_249_ = l_Lake_Toml_elabSimpleKey(v___x_248_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v_keyTys_251_; lean_object* v_arrKeyTys_252_; lean_object* v_arrParents_253_; lean_object* v_currArrKey_254_; lean_object* v_currKey_255_; lean_object* v_items_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref(v___x_249_);
v_keyTys_251_ = lean_ctor_get(v___y_237_, 0);
v_arrKeyTys_252_ = lean_ctor_get(v___y_237_, 1);
v_arrParents_253_ = lean_ctor_get(v___y_237_, 2);
v_currArrKey_254_ = lean_ctor_get(v___y_237_, 3);
v_currKey_255_ = lean_ctor_get(v___y_237_, 4);
v_items_256_ = lean_ctor_get(v___y_237_, 5);
v___x_257_ = l_Lean_Name_str___override(v_b_236_, v_a_250_);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_251_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 1)
{
lean_object* v_val_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_289_; 
v_val_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_289_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_val_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint8_t v___x_263_; 
v___x_263_ = lean_unbox(v_val_259_);
if (v___x_263_ == 3)
{
lean_del_object(v___x_261_);
lean_dec(v_val_259_);
v_fst_242_ = v___x_257_;
v_snd_243_ = v___y_237_;
goto v___jp_241_;
}
else
{
lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_264_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_265_ = lean_unbox(v_val_259_);
lean_dec(v_val_259_);
v___x_266_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_265_);
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 3);
lean_ctor_set(v___x_261_, 0, v___x_266_);
v___x_268_ = v___x_261_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_288_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_269_ = l_Lean_MessageData_ofFormat(v___x_268_);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_264_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
lean_inc(v___x_257_);
v___x_273_ = l_Lean_MessageData_ofName(v___x_257_);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
lean_inc_ref(v___y_238_);
v___x_277_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_248_, v___x_276_, v___y_237_, v___y_238_, v___y_239_);
lean_dec_ref(v___y_237_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v_snd_279_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref(v___x_277_);
v_snd_279_ = lean_ctor_get(v_a_278_, 1);
lean_inc(v_snd_279_);
lean_dec(v_a_278_);
v_fst_242_ = v___x_257_;
v_snd_243_ = v_snd_279_;
goto v___jp_241_;
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec(v___x_257_);
lean_dec_ref(v___y_238_);
v_a_280_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_277_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_277_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_299_; 
lean_inc_ref(v_items_256_);
lean_inc(v_currKey_255_);
lean_inc(v_currArrKey_254_);
lean_inc(v_arrParents_253_);
lean_inc(v_arrKeyTys_252_);
lean_inc(v_keyTys_251_);
lean_dec(v___x_258_);
v_isSharedCheck_299_ = !lean_is_exclusive(v___y_237_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_300_ = lean_ctor_get(v___y_237_, 5);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v___y_237_, 4);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v___y_237_, 3);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v___y_237_, 2);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v___y_237_, 1);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v___y_237_, 0);
lean_dec(v_unused_305_);
v___x_291_ = v___y_237_;
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
else
{
lean_dec(v___y_237_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_293_ = 3;
v___x_294_ = lean_box(v___x_293_);
lean_inc(v___x_257_);
v___x_295_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_257_, v___x_294_, v_keyTys_251_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_295_);
v___x_297_ = v___x_291_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_arrKeyTys_252_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_arrParents_253_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_currArrKey_254_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_currKey_255_);
lean_ctor_set(v_reuseFailAlloc_298_, 5, v_items_256_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
v_fst_242_ = v___x_257_;
v_snd_243_ = v___x_297_;
goto v___jp_241_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec_ref(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v_b_236_);
v_a_306_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_249_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_249_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
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
else
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec_ref(v___y_238_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v_b_236_);
lean_ctor_set(v___x_314_, 1, v___y_237_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
v___jp_241_:
{
size_t v___x_244_; size_t v___x_245_; 
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_i_234_, v___x_244_);
v_i_234_ = v___x_245_;
v_b_236_ = v_fst_242_;
v___y_237_ = v_snd_243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object* v_as_316_, lean_object* v_i_317_, lean_object* v_stop_318_, lean_object* v_b_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
size_t v_i_boxed_324_; size_t v_stop_boxed_325_; lean_object* v_res_326_; 
v_i_boxed_324_ = lean_unbox_usize(v_i_317_);
lean_dec(v_i_317_);
v_stop_boxed_325_ = lean_unbox_usize(v_stop_318_);
lean_dec(v_stop_318_);
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_316_, v_i_boxed_324_, v_stop_boxed_325_, v_b_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v_as_316_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object* v_ks_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_currKey_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_currKey_332_ = lean_ctor_get(v_a_328_, 4);
lean_inc(v_currKey_332_);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_array_get_size(v_ks_327_);
v___x_335_ = lean_nat_dec_lt(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec_ref(v_a_329_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_currKey_332_);
lean_ctor_set(v___x_336_, 1, v_a_328_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = lean_nat_dec_le(v___x_334_, v___x_334_);
if (v___x_338_ == 0)
{
if (v___x_335_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref(v_a_329_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_currKey_332_);
lean_ctor_set(v___x_339_, 1, v_a_328_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
else
{
size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; 
v___x_341_ = ((size_t)0ULL);
v___x_342_ = lean_usize_of_nat(v___x_334_);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_327_, v___x_341_, v___x_342_, v_currKey_332_, v_a_328_, v_a_329_, v_a_330_);
return v___x_343_;
}
}
else
{
size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; 
v___x_344_ = ((size_t)0ULL);
v___x_345_ = lean_usize_of_nat(v___x_334_);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_327_, v___x_344_, v___x_345_, v_currKey_332_, v_a_328_, v_a_329_, v_a_330_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object* v_ks_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_ks_347_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_353_, lean_object* v_ref_354_, lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_354_, v_msg_355_, v___y_356_, v___y_357_, v___y_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_361_, lean_object* v_ref_362_, lean_object* v_msg_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_361_, v_ref_362_, v_msg_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_364_);
lean_dec(v_ref_362_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_369_, lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_370_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_376_, v_msg_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_383_, lean_object* v_as_384_, size_t v_i_385_, size_t v_stop_386_, lean_object* v_b_387_){
_start:
{
lean_object* v___y_389_; uint8_t v___x_393_; 
v___x_393_ = lean_usize_dec_eq(v_i_385_, v_stop_386_);
if (v___x_393_ == 0)
{
lean_object* v_fst_394_; uint8_t v___x_395_; 
v_fst_394_ = lean_ctor_get(v_b_387_, 0);
v___x_395_ = lean_unbox(v_fst_394_);
if (v___x_395_ == 0)
{
lean_object* v_snd_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_snd_396_ = lean_ctor_get(v_b_387_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_b_387_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; 
v_unused_405_ = lean_ctor_get(v_b_387_, 0);
lean_dec(v_unused_405_);
v___x_398_ = v_b_387_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_snd_396_);
lean_dec(v_b_387_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_box(v___x_383_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_snd_396_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
v___y_389_ = v___x_402_;
goto v___jp_388_;
}
}
}
else
{
lean_object* v_snd_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_416_; 
v_snd_406_ = lean_ctor_get(v_b_387_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_b_387_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; 
v_unused_417_ = lean_ctor_get(v_b_387_, 0);
lean_dec(v_unused_417_);
v___x_408_ = v_b_387_;
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_snd_406_);
lean_dec(v_b_387_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_410_ = lean_array_uget_borrowed(v_as_384_, v_i_385_);
lean_inc(v___x_410_);
v___x_411_ = lean_array_push(v_snd_406_, v___x_410_);
v___x_412_ = lean_box(v___x_393_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_411_);
lean_ctor_set(v___x_408_, 0, v___x_412_);
v___x_414_ = v___x_408_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_411_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
v___y_389_ = v___x_414_;
goto v___jp_388_;
}
}
}
}
else
{
return v_b_387_;
}
v___jp_388_:
{
size_t v___x_390_; size_t v___x_391_; 
v___x_390_ = ((size_t)1ULL);
v___x_391_ = lean_usize_add(v_i_385_, v___x_390_);
v_i_385_ = v___x_391_;
v_b_387_ = v___y_389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_418_, lean_object* v_as_419_, lean_object* v_i_420_, lean_object* v_stop_421_, lean_object* v_b_422_){
_start:
{
uint8_t v___x_4080__boxed_423_; size_t v_i_boxed_424_; size_t v_stop_boxed_425_; lean_object* v_res_426_; 
v___x_4080__boxed_423_ = lean_unbox(v___x_418_);
v_i_boxed_424_ = lean_unbox_usize(v_i_420_);
lean_dec(v_i_420_);
v_stop_boxed_425_ = lean_unbox_usize(v_stop_421_);
lean_dec(v_stop_421_);
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_4080__boxed_423_, v_as_419_, v_i_boxed_424_, v_stop_boxed_425_, v_b_422_);
lean_dec_ref(v_as_419_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_434_, size_t v_i_435_, lean_object* v_bs_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = lean_usize_dec_lt(v_i_435_, v_sz_434_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_438_, 0, v_bs_436_);
return v___x_438_;
}
else
{
lean_object* v_v_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_v_439_ = lean_array_uget(v_bs_436_, v_i_435_);
v___x_440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_439_);
v___x_441_ = l_Lean_Syntax_isOfKind(v_v_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
lean_dec(v_v_439_);
lean_dec_ref(v_bs_436_);
v___x_442_ = lean_box(0);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v_bs_x27_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v_bs_x27_444_ = lean_array_uset(v_bs_436_, v_i_435_, v___x_443_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_435_, v___x_445_);
v___x_447_ = lean_array_uset(v_bs_x27_444_, v_i_435_, v_v_439_);
v_i_435_ = v___x_446_;
v_bs_436_ = v___x_447_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_449_, lean_object* v_i_450_, lean_object* v_bs_451_){
_start:
{
size_t v_sz_boxed_452_; size_t v_i_boxed_453_; lean_object* v_res_454_; 
v_sz_boxed_452_ = lean_unbox_usize(v_sz_449_);
lean_dec(v_sz_449_);
v_i_boxed_453_ = lean_unbox_usize(v_i_450_);
lean_dec(v_i_450_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_452_, v_i_boxed_453_, v_bs_451_);
return v_res_454_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_470_ = l_Lean_stringToMessageData(v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_473_);
v___x_479_ = l_Lean_Syntax_isOfKind(v_kv_473_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_481_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_473_, v___x_480_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_474_);
lean_dec(v_kv_473_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = l_Lean_Syntax_getArg(v_kv_473_, v___x_482_);
v___x_484_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_483_);
v___x_485_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v_kv_473_);
v___x_486_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_487_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_483_, v___x_486_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_474_);
lean_dec(v___x_483_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v_v_489_; lean_object* v___y_491_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_488_ = lean_unsigned_to_nat(2u);
v_v_489_ = l_Lean_Syntax_getArg(v_kv_473_, v___x_488_);
lean_dec(v_kv_473_);
v___x_597_ = l_Lean_Syntax_getArg(v___x_483_, v___x_482_);
v___x_598_ = l_Lean_Syntax_getArgs(v___x_597_);
lean_dec(v___x_597_);
v___x_599_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_600_ = lean_array_get_size(v___x_598_);
v___x_601_ = lean_nat_dec_lt(v___x_482_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec_ref(v___x_598_);
v___y_491_ = v___x_599_;
goto v___jp_490_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = lean_box(v___x_485_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___x_599_);
v___x_604_ = lean_nat_dec_le(v___x_600_, v___x_600_);
if (v___x_604_ == 0)
{
if (v___x_601_ == 0)
{
lean_dec_ref(v___x_603_);
lean_dec_ref(v___x_598_);
v___y_491_ = v___x_599_;
goto v___jp_490_;
}
else
{
size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; lean_object* v_snd_608_; 
v___x_605_ = ((size_t)0ULL);
v___x_606_ = lean_usize_of_nat(v___x_600_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_485_, v___x_598_, v___x_605_, v___x_606_, v___x_603_);
lean_dec_ref(v___x_598_);
v_snd_608_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_snd_608_);
lean_dec_ref(v___x_607_);
v___y_491_ = v_snd_608_;
goto v___jp_490_;
}
}
else
{
size_t v___x_609_; size_t v___x_610_; lean_object* v___x_611_; lean_object* v_snd_612_; 
v___x_609_ = ((size_t)0ULL);
v___x_610_ = lean_usize_of_nat(v___x_600_);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_485_, v___x_598_, v___x_609_, v___x_610_, v___x_603_);
lean_dec_ref(v___x_598_);
v_snd_612_ = lean_ctor_get(v___x_611_, 1);
lean_inc(v_snd_612_);
lean_dec_ref(v___x_611_);
v___y_491_ = v_snd_612_;
goto v___jp_490_;
}
}
v___jp_490_:
{
size_t v_sz_492_; size_t v___x_493_; lean_object* v___x_494_; 
v_sz_492_ = lean_array_size(v___y_491_);
v___x_493_ = ((size_t)0ULL);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_492_, v___x_493_, v___y_491_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v_v_489_);
v___x_495_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_496_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_483_, v___x_495_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_474_);
lean_dec(v___x_483_);
return v___x_496_;
}
else
{
lean_object* v_val_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_tailKeyStx_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_val_497_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_val_497_);
lean_dec_ref(v___x_494_);
v___x_498_ = lean_box(0);
v___x_499_ = lean_array_get_size(v_val_497_);
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_sub(v___x_499_, v___x_500_);
v_tailKeyStx_502_ = lean_array_get(v___x_498_, v_val_497_, v___x_501_);
lean_dec(v___x_501_);
v___x_503_ = lean_array_pop(v_val_497_);
lean_inc_ref(v_a_475_);
v___x_504_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_503_, v_a_474_, v_a_475_, v_a_476_);
lean_dec_ref(v___x_503_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_588_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v_fst_506_ = lean_ctor_get(v_a_505_, 0);
v_snd_507_ = lean_ctor_get(v_a_505_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_a_505_);
if (v_isSharedCheck_588_ == 0)
{
v___x_509_ = v_a_505_;
v_isShared_510_ = v_isSharedCheck_588_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_inc(v_fst_506_);
lean_dec(v_a_505_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_588_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; 
lean_inc_ref(v_a_475_);
lean_inc(v_tailKeyStx_502_);
v___x_511_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_502_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v_keyTys_513_; lean_object* v_arrKeyTys_514_; lean_object* v_arrParents_515_; lean_object* v_currArrKey_516_; lean_object* v_currKey_517_; lean_object* v_items_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref(v___x_511_);
v_keyTys_513_ = lean_ctor_get(v_snd_507_, 0);
v_arrKeyTys_514_ = lean_ctor_get(v_snd_507_, 1);
v_arrParents_515_ = lean_ctor_get(v_snd_507_, 2);
v_currArrKey_516_ = lean_ctor_get(v_snd_507_, 3);
v_currKey_517_ = lean_ctor_get(v_snd_507_, 4);
v_items_518_ = lean_ctor_get(v_snd_507_, 5);
v___x_519_ = l_Lean_Name_str___override(v_fst_506_, v_a_512_);
v___x_520_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_513_, v___x_519_);
if (lean_obj_tag(v___x_520_) == 1)
{
lean_object* v_val_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_540_; 
lean_del_object(v___x_509_);
lean_dec(v_v_489_);
lean_dec(v___x_483_);
v_val_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_540_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_540_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_val_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_540_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_526_ = lean_unbox(v_val_521_);
lean_dec(v_val_521_);
v___x_527_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_526_);
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 3);
lean_ctor_set(v___x_523_, 0, v___x_527_);
v___x_529_ = v___x_523_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_539_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_530_ = l_Lean_MessageData_ofFormat(v___x_529_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_525_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l_Lean_MessageData_ofName(v___x_519_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_502_, v___x_537_, v_snd_507_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec(v_snd_507_);
lean_dec(v_tailKeyStx_502_);
return v___x_538_;
}
}
}
else
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_573_; 
lean_inc_ref(v_items_518_);
lean_inc(v_currKey_517_);
lean_inc(v_currArrKey_516_);
lean_inc(v_arrParents_515_);
lean_inc(v_arrKeyTys_514_);
lean_inc(v_keyTys_513_);
lean_dec(v___x_520_);
lean_dec(v_tailKeyStx_502_);
v_isSharedCheck_573_ = !lean_is_exclusive(v_snd_507_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; lean_object* v_unused_575_; lean_object* v_unused_576_; lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; 
v_unused_574_ = lean_ctor_get(v_snd_507_, 5);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_snd_507_, 4);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_snd_507_, 3);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_snd_507_, 2);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_snd_507_, 1);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_snd_507_, 0);
lean_dec(v_unused_579_);
v___x_542_ = v_snd_507_;
v_isShared_543_ = v_isSharedCheck_573_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_snd_507_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_573_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lake_Toml_elabVal(v_v_489_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_564_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_564_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_564_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_564_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_549_ = lean_box(0);
v___x_550_ = 0;
v___x_551_ = lean_box(v___x_550_);
lean_inc(v___x_519_);
v___x_552_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_519_, v___x_551_, v_keyTys_513_);
v___x_553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_553_, 0, v___x_483_);
lean_ctor_set(v___x_553_, 1, v___x_519_);
lean_ctor_set(v___x_553_, 2, v_a_545_);
v___x_554_ = lean_array_push(v_items_518_, v___x_553_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 5, v___x_554_);
lean_ctor_set(v___x_542_, 0, v___x_552_);
v___x_556_ = v___x_542_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_arrKeyTys_514_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_arrParents_515_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_currArrKey_516_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_currKey_517_);
lean_ctor_set(v_reuseFailAlloc_563_, 5, v___x_554_);
v___x_556_ = v_reuseFailAlloc_563_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_556_);
lean_ctor_set(v___x_509_, 0, v___x_549_);
v___x_558_ = v___x_509_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_558_);
v___x_560_ = v___x_547_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_del_object(v___x_542_);
lean_dec(v___x_519_);
lean_dec_ref(v_items_518_);
lean_dec(v_currKey_517_);
lean_dec(v_currArrKey_516_);
lean_dec(v_arrParents_515_);
lean_dec(v_arrKeyTys_514_);
lean_dec(v_keyTys_513_);
lean_del_object(v___x_509_);
lean_dec(v___x_483_);
v_a_565_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_544_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_544_);
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
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_dec(v_tailKeyStx_502_);
lean_dec(v_v_489_);
lean_dec(v___x_483_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
v_a_580_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_511_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_511_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_tailKeyStx_502_);
lean_dec(v_v_489_);
lean_dec(v___x_483_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
v_a_589_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_504_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_504_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_613_, v_a_614_, v_a_615_, v_a_616_);
return v_res_618_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_621_ = l_Lean_stringToMessageData(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_622_, size_t v_i_623_, size_t v_stop_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_fst_631_; lean_object* v_snd_632_; uint8_t v___x_636_; 
v___x_636_ = lean_usize_dec_eq(v_i_623_, v_stop_624_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_array_uget_borrowed(v_as_622_, v_i_623_);
lean_inc_ref(v___y_627_);
lean_inc(v___x_637_);
v___x_638_ = l_Lake_Toml_elabSimpleKey(v___x_637_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_keyTys_640_; lean_object* v_arrKeyTys_641_; lean_object* v_arrParents_642_; lean_object* v_currArrKey_643_; lean_object* v_currKey_644_; lean_object* v_items_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
v_keyTys_640_ = lean_ctor_get(v___y_626_, 0);
v_arrKeyTys_641_ = lean_ctor_get(v___y_626_, 1);
v_arrParents_642_ = lean_ctor_get(v___y_626_, 2);
v_currArrKey_643_ = lean_ctor_get(v___y_626_, 3);
v_currKey_644_ = lean_ctor_get(v___y_626_, 4);
v_items_645_ = lean_ctor_get(v___y_626_, 5);
v___x_646_ = l_Lean_Name_str___override(v_b_625_, v_a_639_);
v___x_647_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_640_, v___x_646_);
if (lean_obj_tag(v___x_647_) == 1)
{
lean_object* v_val_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_709_; 
v_val_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_709_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_709_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_val_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_709_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
uint8_t v___x_652_; 
v___x_652_ = lean_unbox(v_val_648_);
switch(v___x_652_)
{
case 2:
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_677_; 
lean_inc_ref(v_items_645_);
lean_inc(v_currKey_644_);
lean_inc(v_arrParents_642_);
lean_inc(v_arrKeyTys_641_);
lean_del_object(v___x_650_);
lean_dec(v_val_648_);
v_isSharedCheck_677_ = !lean_is_exclusive(v___y_626_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; lean_object* v_unused_683_; 
v_unused_678_ = lean_ctor_get(v___y_626_, 5);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v___y_626_, 4);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v___y_626_, 3);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v___y_626_, 2);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v___y_626_, 1);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v___y_626_, 0);
lean_dec(v_unused_683_);
v___x_654_ = v___y_626_;
v_isShared_655_ = v_isSharedCheck_677_;
goto v_resetjp_653_;
}
else
{
lean_dec(v___y_626_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_677_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_641_, v___x_646_);
if (lean_obj_tag(v___x_656_) == 1)
{
lean_object* v_val_657_; lean_object* v___x_659_; 
v_val_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_val_657_);
lean_dec_ref(v___x_656_);
lean_inc(v___x_646_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 3, v___x_646_);
lean_ctor_set(v___x_654_, 0, v_val_657_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_val_657_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_arrKeyTys_641_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_arrParents_642_);
lean_ctor_set(v_reuseFailAlloc_660_, 3, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_660_, 4, v_currKey_644_);
lean_ctor_set(v_reuseFailAlloc_660_, 5, v_items_645_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
v_fst_631_ = v___x_646_;
v_snd_632_ = v___x_659_;
goto v___jp_630_;
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v___x_656_);
lean_del_object(v___x_654_);
lean_dec_ref(v_items_645_);
lean_dec(v_currKey_644_);
lean_dec(v_arrParents_642_);
lean_dec(v_arrKeyTys_641_);
v___x_661_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_646_);
v___x_662_ = l_Lean_MessageData_ofName(v___x_646_);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_665_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v_snd_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v_snd_668_ = lean_ctor_get(v_a_667_, 1);
lean_inc(v_snd_668_);
lean_dec(v_a_667_);
v_fst_631_ = v___x_646_;
v_snd_632_ = v_snd_668_;
goto v___jp_630_;
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v___x_646_);
lean_dec_ref(v___y_627_);
v_a_669_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_666_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_666_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
case 1:
{
lean_del_object(v___x_650_);
lean_dec(v_val_648_);
v_fst_631_ = v___x_646_;
v_snd_632_ = v___y_626_;
goto v___jp_630_;
}
case 4:
{
lean_del_object(v___x_650_);
lean_dec(v_val_648_);
v_fst_631_ = v___x_646_;
v_snd_632_ = v___y_626_;
goto v___jp_630_;
}
case 3:
{
lean_del_object(v___x_650_);
lean_dec(v_val_648_);
v_fst_631_ = v___x_646_;
v_snd_632_ = v___y_626_;
goto v___jp_630_;
}
default: 
{
lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_685_ = lean_unbox(v_val_648_);
lean_dec(v_val_648_);
v___x_686_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_685_);
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 3);
lean_ctor_set(v___x_650_, 0, v___x_686_);
v___x_688_ = v___x_650_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_708_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_689_ = l_Lean_MessageData_ofFormat(v___x_688_);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_684_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
lean_inc(v___x_646_);
v___x_693_ = l_Lean_MessageData_ofName(v___x_646_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
lean_inc_ref(v___y_627_);
v___x_697_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_637_, v___x_696_, v___y_626_, v___y_627_, v___y_628_);
lean_dec_ref(v___y_626_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v_snd_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v___x_697_);
v_snd_699_ = lean_ctor_get(v_a_698_, 1);
lean_inc(v_snd_699_);
lean_dec(v_a_698_);
v_fst_631_ = v___x_646_;
v_snd_632_ = v_snd_699_;
goto v___jp_630_;
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v___x_646_);
lean_dec_ref(v___y_627_);
v_a_700_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_697_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_697_);
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
}
}
}
}
else
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_719_; 
lean_inc_ref(v_items_645_);
lean_inc(v_currKey_644_);
lean_inc(v_currArrKey_643_);
lean_inc(v_arrParents_642_);
lean_inc(v_arrKeyTys_641_);
lean_inc(v_keyTys_640_);
lean_dec(v___x_647_);
v_isSharedCheck_719_ = !lean_is_exclusive(v___y_626_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; lean_object* v_unused_725_; 
v_unused_720_ = lean_ctor_get(v___y_626_, 5);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v___y_626_, 4);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v___y_626_, 3);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v___y_626_, 2);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v___y_626_, 1);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v___y_626_, 0);
lean_dec(v_unused_725_);
v___x_711_ = v___y_626_;
v_isShared_712_ = v_isSharedCheck_719_;
goto v_resetjp_710_;
}
else
{
lean_dec(v___y_626_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_719_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_713_ = 4;
v___x_714_ = lean_box(v___x_713_);
lean_inc(v___x_646_);
v___x_715_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_646_, v___x_714_, v_keyTys_640_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_715_);
v___x_717_ = v___x_711_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_arrKeyTys_641_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_arrParents_642_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_currArrKey_643_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_currKey_644_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v_items_645_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v_fst_631_ = v___x_646_;
v_snd_632_ = v___x_717_;
goto v___jp_630_;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v_b_625_);
v_a_726_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_638_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_638_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec_ref(v___y_627_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_b_625_);
lean_ctor_set(v___x_734_, 1, v___y_626_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
v___jp_630_:
{
size_t v___x_633_; size_t v___x_634_; 
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_add(v_i_623_, v___x_633_);
v_i_623_ = v___x_634_;
v_b_625_ = v_fst_631_;
v___y_626_ = v_snd_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_736_, lean_object* v_i_737_, lean_object* v_stop_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
size_t v_i_boxed_744_; size_t v_stop_boxed_745_; lean_object* v_res_746_; 
v_i_boxed_744_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_stop_boxed_745_ = lean_unbox_usize(v_stop_738_);
lean_dec(v_stop_738_);
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_736_, v_i_boxed_744_, v_stop_boxed_745_, v_b_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v_as_736_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_747_, lean_object* v_k_748_){
_start:
{
if (lean_obj_tag(v_t_747_) == 0)
{
lean_object* v_k_749_; lean_object* v_v_750_; lean_object* v_l_751_; lean_object* v_r_752_; uint8_t v___x_753_; 
v_k_749_ = lean_ctor_get(v_t_747_, 1);
v_v_750_ = lean_ctor_get(v_t_747_, 2);
v_l_751_ = lean_ctor_get(v_t_747_, 3);
v_r_752_ = lean_ctor_get(v_t_747_, 4);
v___x_753_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_748_, v_k_749_);
switch(v___x_753_)
{
case 0:
{
v_t_747_ = v_l_751_;
goto _start;
}
case 1:
{
lean_object* v___x_755_; 
lean_inc(v_v_750_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v_v_750_);
return v___x_755_;
}
default: 
{
v_t_747_ = v_r_752_;
goto _start;
}
}
}
else
{
lean_object* v___x_757_; 
v___x_757_ = lean_box(0);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_758_, lean_object* v_k_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_758_, v_k_759_);
lean_dec(v_k_759_);
lean_dec(v_t_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_keyTys_766_; lean_object* v_arrKeyTys_767_; lean_object* v_arrParents_768_; lean_object* v_currArrKey_769_; lean_object* v_currKey_770_; lean_object* v_items_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_799_; 
v_keyTys_766_ = lean_ctor_get(v_a_762_, 0);
v_arrKeyTys_767_ = lean_ctor_get(v_a_762_, 1);
v_arrParents_768_ = lean_ctor_get(v_a_762_, 2);
v_currArrKey_769_ = lean_ctor_get(v_a_762_, 3);
v_currKey_770_ = lean_ctor_get(v_a_762_, 4);
v_items_771_ = lean_ctor_get(v_a_762_, 5);
v_isSharedCheck_799_ = !lean_is_exclusive(v_a_762_);
if (v_isSharedCheck_799_ == 0)
{
v___x_773_ = v_a_762_;
v_isShared_774_ = v_isSharedCheck_799_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_items_771_);
lean_inc(v_currKey_770_);
lean_inc(v_currArrKey_769_);
lean_inc(v_arrParents_768_);
lean_inc(v_arrKeyTys_767_);
lean_inc(v_keyTys_766_);
lean_dec(v_a_762_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_799_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_arrKeyTys_775_; lean_object* v___x_776_; lean_object* v___y_778_; lean_object* v___x_796_; 
v_arrKeyTys_775_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_769_, v_keyTys_766_, v_arrKeyTys_767_);
v___x_776_ = lean_box(0);
v___x_796_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_775_, v___x_776_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_797_; 
v___x_797_ = lean_box(1);
v___y_778_ = v___x_797_;
goto v___jp_777_;
}
else
{
lean_object* v_val_798_; 
v_val_798_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_val_798_);
lean_dec_ref(v___x_796_);
v___y_778_ = v_val_798_;
goto v___jp_777_;
}
v___jp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 3, v___x_776_);
lean_ctor_set(v___x_773_, 1, v_arrKeyTys_775_);
lean_ctor_set(v___x_773_, 0, v___y_778_);
v___x_780_ = v___x_773_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___y_778_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_arrKeyTys_775_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_arrParents_768_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_currKey_770_);
lean_ctor_set(v_reuseFailAlloc_795_, 5, v_items_771_);
v___x_780_ = v_reuseFailAlloc_795_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_array_get_size(v_ks_761_);
v___x_783_ = lean_nat_dec_lt(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec_ref(v_a_763_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_776_);
lean_ctor_set(v___x_784_, 1, v___x_780_);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = lean_nat_dec_le(v___x_782_, v___x_782_);
if (v___x_786_ == 0)
{
if (v___x_783_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v_a_763_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_776_);
lean_ctor_set(v___x_787_, 1, v___x_780_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
else
{
size_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; 
v___x_789_ = ((size_t)0ULL);
v___x_790_ = lean_usize_of_nat(v___x_782_);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_761_, v___x_789_, v___x_790_, v___x_776_, v___x_780_, v_a_763_, v_a_764_);
return v___x_791_;
}
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((size_t)0ULL);
v___x_793_ = lean_usize_of_nat(v___x_782_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_761_, v___x_792_, v___x_793_, v___x_776_, v___x_780_, v_a_763_, v_a_764_);
return v___x_794_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_ks_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_806_, lean_object* v_t_807_, lean_object* v_k_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_807_, v_k_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_810_, lean_object* v_t_811_, lean_object* v_k_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_810_, v_t_811_, v_k_812_);
lean_dec(v_k_812_);
lean_dec(v_t_811_);
return v_res_813_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
v___x_816_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4));
v___x_824_ = l_Lean_stringToMessageData(v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___y_831_; lean_object* v_keyTys_832_; lean_object* v_arrKeyTys_833_; lean_object* v_arrParents_834_; lean_object* v_currArrKey_835_; lean_object* v_items_836_; lean_object* v_fileName_848_; lean_object* v_fileMap_849_; lean_object* v_options_850_; lean_object* v_currRecDepth_851_; lean_object* v_maxRecDepth_852_; lean_object* v_ref_853_; lean_object* v_currNamespace_854_; lean_object* v_openDecls_855_; lean_object* v_initHeartbeats_856_; lean_object* v_maxHeartbeats_857_; lean_object* v_quotContext_858_; lean_object* v_currMacroScope_859_; uint8_t v_diag_860_; lean_object* v_cancelTk_x3f_861_; uint8_t v_suppressElabErrors_862_; lean_object* v_inheritedTraceOptions_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_967_; 
v_fileName_848_ = lean_ctor_get(v_a_827_, 0);
v_fileMap_849_ = lean_ctor_get(v_a_827_, 1);
v_options_850_ = lean_ctor_get(v_a_827_, 2);
v_currRecDepth_851_ = lean_ctor_get(v_a_827_, 3);
v_maxRecDepth_852_ = lean_ctor_get(v_a_827_, 4);
v_ref_853_ = lean_ctor_get(v_a_827_, 5);
v_currNamespace_854_ = lean_ctor_get(v_a_827_, 6);
v_openDecls_855_ = lean_ctor_get(v_a_827_, 7);
v_initHeartbeats_856_ = lean_ctor_get(v_a_827_, 8);
v_maxHeartbeats_857_ = lean_ctor_get(v_a_827_, 9);
v_quotContext_858_ = lean_ctor_get(v_a_827_, 10);
v_currMacroScope_859_ = lean_ctor_get(v_a_827_, 11);
v_diag_860_ = lean_ctor_get_uint8(v_a_827_, sizeof(void*)*14);
v_cancelTk_x3f_861_ = lean_ctor_get(v_a_827_, 12);
v_suppressElabErrors_862_ = lean_ctor_get_uint8(v_a_827_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_863_ = lean_ctor_get(v_a_827_, 13);
v_isSharedCheck_967_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_967_ == 0)
{
v___x_865_ = v_a_827_;
v_isShared_866_ = v_isSharedCheck_967_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_inheritedTraceOptions_863_);
lean_inc(v_cancelTk_x3f_861_);
lean_inc(v_currMacroScope_859_);
lean_inc(v_quotContext_858_);
lean_inc(v_maxHeartbeats_857_);
lean_inc(v_initHeartbeats_856_);
lean_inc(v_openDecls_855_);
lean_inc(v_currNamespace_854_);
lean_inc(v_ref_853_);
lean_inc(v_maxRecDepth_852_);
lean_inc(v_currRecDepth_851_);
lean_inc(v_options_850_);
lean_inc(v_fileMap_849_);
lean_inc(v_fileName_848_);
lean_dec(v_a_827_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_967_;
goto v_resetjp_864_;
}
v___jp_830_:
{
lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_837_ = lean_box(0);
v___x_838_ = 1;
v___x_839_ = lean_box(v___x_838_);
lean_inc(v___y_831_);
v___x_840_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_831_, v___x_839_, v_keyTys_832_);
v___x_841_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc(v_x_825_);
v___x_842_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_842_, 0, v_x_825_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
lean_inc(v___y_831_);
v___x_843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_843_, 0, v_x_825_);
lean_ctor_set(v___x_843_, 1, v___y_831_);
lean_ctor_set(v___x_843_, 2, v___x_842_);
v___x_844_ = lean_array_push(v_items_836_, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_845_, 0, v___x_840_);
lean_ctor_set(v___x_845_, 1, v_arrKeyTys_833_);
lean_ctor_set(v___x_845_, 2, v_arrParents_834_);
lean_ctor_set(v___x_845_, 3, v_currArrKey_835_);
lean_ctor_set(v___x_845_, 4, v___y_831_);
lean_ctor_set(v___x_845_, 5, v___x_844_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_837_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v_ref_869_; lean_object* v___x_871_; 
v___x_867_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_825_);
v___x_868_ = l_Lean_Syntax_isOfKind(v_x_825_, v___x_867_);
v_ref_869_ = l_Lean_replaceRef(v_x_825_, v_ref_853_);
lean_dec(v_ref_853_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 5, v_ref_869_);
v___x_871_ = v___x_865_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_fileName_848_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_fileMap_849_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_options_850_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_currRecDepth_851_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_maxRecDepth_852_);
lean_ctor_set(v_reuseFailAlloc_966_, 5, v_ref_869_);
lean_ctor_set(v_reuseFailAlloc_966_, 6, v_currNamespace_854_);
lean_ctor_set(v_reuseFailAlloc_966_, 7, v_openDecls_855_);
lean_ctor_set(v_reuseFailAlloc_966_, 8, v_initHeartbeats_856_);
lean_ctor_set(v_reuseFailAlloc_966_, 9, v_maxHeartbeats_857_);
lean_ctor_set(v_reuseFailAlloc_966_, 10, v_quotContext_858_);
lean_ctor_set(v_reuseFailAlloc_966_, 11, v_currMacroScope_859_);
lean_ctor_set(v_reuseFailAlloc_966_, 12, v_cancelTk_x3f_861_);
lean_ctor_set(v_reuseFailAlloc_966_, 13, v_inheritedTraceOptions_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*14, v_diag_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*14 + 1, v_suppressElabErrors_862_);
v___x_871_ = v_reuseFailAlloc_966_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
if (v___x_868_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5);
v___x_873_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_825_, v___x_872_, v_a_826_, v___x_871_, v_a_828_);
lean_dec_ref(v_a_826_);
lean_dec(v_x_825_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___y_877_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_874_ = lean_unsigned_to_nat(1u);
v___x_875_ = l_Lean_Syntax_getArg(v_x_825_, v___x_874_);
v___x_945_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_875_);
v___x_946_ = l_Lean_Syntax_isOfKind(v___x_875_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v_x_825_);
v___x_947_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_948_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_875_, v___x_947_, v_a_826_, v___x_871_, v_a_828_);
lean_dec_ref(v_a_826_);
lean_dec(v___x_875_);
return v___x_948_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = l_Lean_Syntax_getArg(v___x_875_, v___x_949_);
v___x_951_ = l_Lean_Syntax_getArgs(v___x_950_);
lean_dec(v___x_950_);
v___x_952_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_953_ = lean_array_get_size(v___x_951_);
v___x_954_ = lean_nat_dec_lt(v___x_949_, v___x_953_);
if (v___x_954_ == 0)
{
lean_dec_ref(v___x_951_);
v___y_877_ = v___x_952_;
goto v___jp_876_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_955_ = lean_box(v___x_946_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_952_);
v___x_957_ = lean_nat_dec_le(v___x_953_, v___x_953_);
if (v___x_957_ == 0)
{
if (v___x_954_ == 0)
{
lean_dec_ref(v___x_956_);
lean_dec_ref(v___x_951_);
v___y_877_ = v___x_952_;
goto v___jp_876_;
}
else
{
size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; lean_object* v_snd_961_; 
v___x_958_ = ((size_t)0ULL);
v___x_959_ = lean_usize_of_nat(v___x_953_);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_946_, v___x_951_, v___x_958_, v___x_959_, v___x_956_);
lean_dec_ref(v___x_951_);
v_snd_961_ = lean_ctor_get(v___x_960_, 1);
lean_inc(v_snd_961_);
lean_dec_ref(v___x_960_);
v___y_877_ = v_snd_961_;
goto v___jp_876_;
}
}
else
{
size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; lean_object* v_snd_965_; 
v___x_962_ = ((size_t)0ULL);
v___x_963_ = lean_usize_of_nat(v___x_953_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_946_, v___x_951_, v___x_962_, v___x_963_, v___x_956_);
lean_dec_ref(v___x_951_);
v_snd_965_ = lean_ctor_get(v___x_964_, 1);
lean_inc(v_snd_965_);
lean_dec_ref(v___x_964_);
v___y_877_ = v_snd_965_;
goto v___jp_876_;
}
}
}
v___jp_876_:
{
size_t v_sz_878_; size_t v___x_879_; lean_object* v___x_880_; 
v_sz_878_ = lean_array_size(v___y_877_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_878_, v___x_879_, v___y_877_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v_x_825_);
v___x_881_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_882_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_875_, v___x_881_, v_a_826_, v___x_871_, v_a_828_);
lean_dec_ref(v_a_826_);
lean_dec(v___x_875_);
return v___x_882_;
}
else
{
lean_object* v_val_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_tailKey_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v___x_875_);
v_val_883_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_val_883_);
lean_dec_ref(v___x_880_);
v___x_884_ = lean_box(0);
v___x_885_ = lean_array_get_size(v_val_883_);
v___x_886_ = lean_nat_sub(v___x_885_, v___x_874_);
v_tailKey_887_ = lean_array_get(v___x_884_, v_val_883_, v___x_886_);
lean_dec(v___x_886_);
v___x_888_ = lean_array_pop(v_val_883_);
lean_inc_ref(v___x_871_);
v___x_889_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_888_, v_a_826_, v___x_871_, v_a_828_);
lean_dec_ref(v___x_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_936_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
v_fst_891_ = lean_ctor_get(v_a_890_, 0);
v_snd_892_ = lean_ctor_get(v_a_890_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_a_890_);
if (v_isSharedCheck_936_ == 0)
{
v___x_894_ = v_a_890_;
v_isShared_895_ = v_isSharedCheck_936_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_snd_892_);
lean_inc(v_fst_891_);
lean_dec(v_a_890_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_936_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; 
lean_inc_ref(v___x_871_);
lean_inc(v_tailKey_887_);
v___x_896_ = l_Lake_Toml_elabSimpleKey(v_tailKey_887_, v___x_871_, v_a_828_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v_keyTys_898_; lean_object* v_arrKeyTys_899_; lean_object* v_arrParents_900_; lean_object* v_currArrKey_901_; lean_object* v_items_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref(v___x_896_);
v_keyTys_898_ = lean_ctor_get(v_snd_892_, 0);
v_arrKeyTys_899_ = lean_ctor_get(v_snd_892_, 1);
v_arrParents_900_ = lean_ctor_get(v_snd_892_, 2);
v_currArrKey_901_ = lean_ctor_get(v_snd_892_, 3);
v_items_902_ = lean_ctor_get(v_snd_892_, 5);
v___x_903_ = l_Lean_Name_str___override(v_fst_891_, v_a_897_);
v___x_904_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_898_, v___x_903_);
if (lean_obj_tag(v___x_904_) == 1)
{
lean_object* v_val_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_927_; 
v_val_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_927_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_927_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_val_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_927_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
uint8_t v___x_909_; 
v___x_909_ = lean_unbox(v_val_905_);
if (v___x_909_ == 4)
{
lean_inc_ref(v_items_902_);
lean_inc(v_currArrKey_901_);
lean_inc(v_arrParents_900_);
lean_inc(v_arrKeyTys_899_);
lean_inc(v_keyTys_898_);
lean_del_object(v___x_907_);
lean_dec(v_val_905_);
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_tailKey_887_);
lean_dec_ref(v___x_871_);
v___y_831_ = v___x_903_;
v_keyTys_832_ = v_keyTys_898_;
v_arrKeyTys_833_ = v_arrKeyTys_899_;
v_arrParents_834_ = v_arrParents_900_;
v_currArrKey_835_ = v_currArrKey_901_;
v_items_836_ = v_items_902_;
goto v___jp_830_;
}
else
{
lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
lean_dec(v_x_825_);
v___x_910_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_911_ = lean_unbox(v_val_905_);
lean_dec(v_val_905_);
v___x_912_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_911_);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 3);
lean_ctor_set(v___x_907_, 0, v___x_912_);
v___x_914_ = v___x_907_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_926_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = l_Lean_MessageData_ofFormat(v___x_914_);
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 7);
lean_ctor_set(v___x_894_, 1, v___x_915_);
lean_ctor_set(v___x_894_, 0, v___x_910_);
v___x_917_ = v___x_894_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_915_);
v___x_917_ = v_reuseFailAlloc_925_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_918_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_MessageData_ofName(v___x_903_);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_887_, v___x_923_, v_snd_892_, v___x_871_, v_a_828_);
lean_dec(v_snd_892_);
lean_dec(v_tailKey_887_);
return v___x_924_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_902_);
lean_inc(v_currArrKey_901_);
lean_inc(v_arrParents_900_);
lean_inc(v_arrKeyTys_899_);
lean_inc(v_keyTys_898_);
lean_dec(v___x_904_);
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_tailKey_887_);
lean_dec_ref(v___x_871_);
v___y_831_ = v___x_903_;
v_keyTys_832_ = v_keyTys_898_;
v_arrKeyTys_833_ = v_arrKeyTys_899_;
v_arrParents_834_ = v_arrParents_900_;
v_currArrKey_835_ = v_currArrKey_901_;
v_items_836_ = v_items_902_;
goto v___jp_830_;
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
lean_dec(v_tailKey_887_);
lean_dec_ref(v___x_871_);
lean_dec(v_x_825_);
v_a_928_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_896_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_896_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_tailKey_887_);
lean_dec_ref(v___x_871_);
lean_dec(v_x_825_);
v_a_937_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_889_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_889_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_968_, v_a_969_, v_a_970_, v_a_971_);
lean_dec(v_a_971_);
return v_res_973_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_fileName_987_; lean_object* v_fileMap_988_; lean_object* v_options_989_; lean_object* v_currRecDepth_990_; lean_object* v_maxRecDepth_991_; lean_object* v_ref_992_; lean_object* v_currNamespace_993_; lean_object* v_openDecls_994_; lean_object* v_initHeartbeats_995_; lean_object* v_maxHeartbeats_996_; lean_object* v_quotContext_997_; lean_object* v_currMacroScope_998_; uint8_t v_diag_999_; lean_object* v_cancelTk_x3f_1000_; uint8_t v_suppressElabErrors_1001_; lean_object* v_inheritedTraceOptions_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1180_; 
v_fileName_987_ = lean_ctor_get(v_a_984_, 0);
v_fileMap_988_ = lean_ctor_get(v_a_984_, 1);
v_options_989_ = lean_ctor_get(v_a_984_, 2);
v_currRecDepth_990_ = lean_ctor_get(v_a_984_, 3);
v_maxRecDepth_991_ = lean_ctor_get(v_a_984_, 4);
v_ref_992_ = lean_ctor_get(v_a_984_, 5);
v_currNamespace_993_ = lean_ctor_get(v_a_984_, 6);
v_openDecls_994_ = lean_ctor_get(v_a_984_, 7);
v_initHeartbeats_995_ = lean_ctor_get(v_a_984_, 8);
v_maxHeartbeats_996_ = lean_ctor_get(v_a_984_, 9);
v_quotContext_997_ = lean_ctor_get(v_a_984_, 10);
v_currMacroScope_998_ = lean_ctor_get(v_a_984_, 11);
v_diag_999_ = lean_ctor_get_uint8(v_a_984_, sizeof(void*)*14);
v_cancelTk_x3f_1000_ = lean_ctor_get(v_a_984_, 12);
v_suppressElabErrors_1001_ = lean_ctor_get_uint8(v_a_984_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1002_ = lean_ctor_get(v_a_984_, 13);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_a_984_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1004_ = v_a_984_;
v_isShared_1005_ = v_isSharedCheck_1180_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_inheritedTraceOptions_1002_);
lean_inc(v_cancelTk_x3f_1000_);
lean_inc(v_currMacroScope_998_);
lean_inc(v_quotContext_997_);
lean_inc(v_maxHeartbeats_996_);
lean_inc(v_initHeartbeats_995_);
lean_inc(v_openDecls_994_);
lean_inc(v_currNamespace_993_);
lean_inc(v_ref_992_);
lean_inc(v_maxRecDepth_991_);
lean_inc(v_currRecDepth_990_);
lean_inc(v_options_989_);
lean_inc(v_fileMap_988_);
lean_inc(v_fileName_987_);
lean_dec(v_a_984_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1180_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v_ref_1008_; lean_object* v___x_1010_; 
v___x_1006_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_982_);
v___x_1007_ = l_Lean_Syntax_isOfKind(v_x_982_, v___x_1006_);
v_ref_1008_ = l_Lean_replaceRef(v_x_982_, v_ref_992_);
lean_dec(v_ref_992_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 5, v_ref_1008_);
v___x_1010_ = v___x_1004_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_fileName_987_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_fileMap_988_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_options_989_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_currRecDepth_990_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_maxRecDepth_991_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v_ref_1008_);
lean_ctor_set(v_reuseFailAlloc_1179_, 6, v_currNamespace_993_);
lean_ctor_set(v_reuseFailAlloc_1179_, 7, v_openDecls_994_);
lean_ctor_set(v_reuseFailAlloc_1179_, 8, v_initHeartbeats_995_);
lean_ctor_set(v_reuseFailAlloc_1179_, 9, v_maxHeartbeats_996_);
lean_ctor_set(v_reuseFailAlloc_1179_, 10, v_quotContext_997_);
lean_ctor_set(v_reuseFailAlloc_1179_, 11, v_currMacroScope_998_);
lean_ctor_set(v_reuseFailAlloc_1179_, 12, v_cancelTk_x3f_1000_);
lean_ctor_set(v_reuseFailAlloc_1179_, 13, v_inheritedTraceOptions_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1179_, sizeof(void*)*14, v_diag_999_);
lean_ctor_set_uint8(v_reuseFailAlloc_1179_, sizeof(void*)*14 + 1, v_suppressElabErrors_1001_);
v___x_1010_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___y_1012_; 
if (v___x_1007_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_1020_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_982_, v___x_1019_, v_a_983_, v___x_1010_, v_a_985_);
lean_dec_ref(v_a_983_);
lean_dec(v_x_982_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; lean_object* v___y_1026_; 
v___x_1021_ = lean_unsigned_to_nat(2u);
v___x_1022_ = l_Lean_Syntax_getArg(v_x_982_, v___x_1021_);
v___x_1023_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_1022_);
v___x_1024_ = l_Lean_Syntax_isOfKind(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v___x_1022_);
v___x_1160_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1161_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_982_, v___x_1160_, v_a_983_, v___x_1010_, v_a_985_);
lean_dec_ref(v_a_983_);
lean_dec(v_x_982_);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = l_Lean_Syntax_getArg(v___x_1022_, v___x_1162_);
lean_dec(v___x_1022_);
v___x_1164_ = l_Lean_Syntax_getArgs(v___x_1163_);
lean_dec(v___x_1163_);
v___x_1165_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1166_ = lean_array_get_size(v___x_1164_);
v___x_1167_ = lean_nat_dec_lt(v___x_1162_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_dec_ref(v___x_1164_);
v___y_1026_ = v___x_1165_;
goto v___jp_1025_;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1168_ = lean_box(v___x_1024_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___x_1165_);
v___x_1170_ = lean_nat_dec_le(v___x_1166_, v___x_1166_);
if (v___x_1170_ == 0)
{
if (v___x_1167_ == 0)
{
lean_dec_ref(v___x_1169_);
lean_dec_ref(v___x_1164_);
v___y_1026_ = v___x_1165_;
goto v___jp_1025_;
}
else
{
size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; lean_object* v_snd_1174_; 
v___x_1171_ = ((size_t)0ULL);
v___x_1172_ = lean_usize_of_nat(v___x_1166_);
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_1024_, v___x_1164_, v___x_1171_, v___x_1172_, v___x_1169_);
lean_dec_ref(v___x_1164_);
v_snd_1174_ = lean_ctor_get(v___x_1173_, 1);
lean_inc(v_snd_1174_);
lean_dec_ref(v___x_1173_);
v___y_1026_ = v_snd_1174_;
goto v___jp_1025_;
}
}
else
{
size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; lean_object* v_snd_1178_; 
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = lean_usize_of_nat(v___x_1166_);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_1024_, v___x_1164_, v___x_1175_, v___x_1176_, v___x_1169_);
lean_dec_ref(v___x_1164_);
v_snd_1178_ = lean_ctor_get(v___x_1177_, 1);
lean_inc(v_snd_1178_);
lean_dec_ref(v___x_1177_);
v___y_1026_ = v_snd_1178_;
goto v___jp_1025_;
}
}
}
v___jp_1025_:
{
size_t v_sz_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v_sz_1027_ = lean_array_size(v___y_1026_);
v___x_1028_ = ((size_t)0ULL);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_1027_, v___x_1028_, v___y_1026_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1031_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_982_, v___x_1030_, v_a_983_, v___x_1010_, v_a_985_);
lean_dec_ref(v_a_983_);
lean_dec(v_x_982_);
return v___x_1031_;
}
else
{
lean_object* v_val_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_tailKey_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_val_1032_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_val_1032_);
lean_dec_ref(v___x_1029_);
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_array_get_size(v_val_1032_);
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_sub(v___x_1034_, v___x_1035_);
v_tailKey_1037_ = lean_array_get(v___x_1033_, v_val_1032_, v___x_1036_);
lean_dec(v___x_1036_);
v___x_1038_ = lean_array_pop(v_val_1032_);
lean_inc_ref(v___x_1010_);
v___x_1039_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_1038_, v_a_983_, v___x_1010_, v_a_985_);
lean_dec_ref(v___x_1038_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v_fst_1041_; lean_object* v_snd_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1151_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v_fst_1041_ = lean_ctor_get(v_a_1040_, 0);
v_snd_1042_ = lean_ctor_get(v_a_1040_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_a_1040_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1044_ = v_a_1040_;
v_isShared_1045_ = v_isSharedCheck_1151_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_snd_1042_);
lean_inc(v_fst_1041_);
lean_dec(v_a_1040_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1151_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; 
lean_inc_ref(v___x_1010_);
lean_inc(v_tailKey_1037_);
v___x_1046_ = l_Lake_Toml_elabSimpleKey(v_tailKey_1037_, v___x_1010_, v_a_985_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1142_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1142_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1142_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_keyTys_1051_; lean_object* v_arrKeyTys_1052_; lean_object* v_arrParents_1053_; lean_object* v_currArrKey_1054_; lean_object* v_items_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_keyTys_1051_ = lean_ctor_get(v_snd_1042_, 0);
v_arrKeyTys_1052_ = lean_ctor_get(v_snd_1042_, 1);
v_arrParents_1053_ = lean_ctor_get(v_snd_1042_, 2);
v_currArrKey_1054_ = lean_ctor_get(v_snd_1042_, 3);
v_items_1055_ = lean_ctor_get(v_snd_1042_, 5);
v___x_1056_ = l_Lean_Name_str___override(v_fst_1041_, v_a_1047_);
v___x_1057_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_1051_, v___x_1056_);
if (lean_obj_tag(v___x_1057_) == 1)
{
lean_object* v_val_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1109_; 
v_val_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1109_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_val_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1109_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_unbox(v_val_1058_);
if (v___x_1062_ == 2)
{
lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1087_; 
lean_inc_ref(v_items_1055_);
lean_inc(v_arrParents_1053_);
lean_inc(v_arrKeyTys_1052_);
lean_del_object(v___x_1060_);
lean_dec(v_val_1058_);
lean_dec(v_tailKey_1037_);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_snd_1042_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; 
v_unused_1088_ = lean_ctor_get(v_snd_1042_, 5);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_snd_1042_, 4);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_snd_1042_, 3);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_snd_1042_, 2);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_snd_1042_, 1);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_snd_1042_, 0);
lean_dec(v_unused_1093_);
v___x_1064_ = v_snd_1042_;
v_isShared_1065_ = v_isSharedCheck_1087_;
goto v_resetjp_1063_;
}
else
{
lean_dec(v_snd_1042_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1087_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_1053_, v___x_1056_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_del_object(v___x_1064_);
lean_dec_ref(v_items_1055_);
lean_dec(v_arrParents_1053_);
lean_dec(v_arrKeyTys_1052_);
lean_del_object(v___x_1049_);
lean_del_object(v___x_1044_);
lean_dec(v_x_982_);
v___y_1012_ = v___x_1056_;
goto v___jp_1011_;
}
else
{
lean_object* v_val_1067_; lean_object* v___x_1068_; 
v_val_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_val_1067_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_1052_, v_val_1067_);
lean_dec(v_val_1067_);
if (lean_obj_tag(v___x_1068_) == 1)
{
lean_object* v_val_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_dec_ref(v___x_1010_);
v_val_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_val_1069_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc(v_x_982_);
v___x_1072_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_x_982_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_mk_empty_array_with_capacity(v___x_1035_);
v___x_1074_ = lean_array_push(v___x_1073_, v___x_1072_);
lean_inc(v_x_982_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_x_982_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
lean_inc(v___x_1056_);
v___x_1076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1076_, 0, v_x_982_);
lean_ctor_set(v___x_1076_, 1, v___x_1056_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
v___x_1077_ = lean_array_push(v_items_1055_, v___x_1076_);
lean_inc(v___x_1056_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 5, v___x_1077_);
lean_ctor_set(v___x_1064_, 4, v___x_1056_);
lean_ctor_set(v___x_1064_, 3, v___x_1056_);
lean_ctor_set(v___x_1064_, 0, v_val_1069_);
v___x_1079_ = v___x_1064_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_val_1069_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_arrKeyTys_1052_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_arrParents_1053_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1086_, 5, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v___x_1079_);
lean_ctor_set(v___x_1044_, 0, v___x_1070_);
v___x_1081_ = v___x_1044_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1081_);
v___x_1083_ = v___x_1049_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
lean_dec(v___x_1068_);
lean_del_object(v___x_1064_);
lean_dec_ref(v_items_1055_);
lean_dec(v_arrParents_1053_);
lean_dec(v_arrKeyTys_1052_);
lean_del_object(v___x_1049_);
lean_del_object(v___x_1044_);
lean_dec(v_x_982_);
v___y_1012_ = v___x_1056_;
goto v___jp_1011_;
}
}
}
}
else
{
lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_del_object(v___x_1049_);
lean_del_object(v___x_1044_);
lean_dec(v_x_982_);
v___x_1094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1095_ = lean_unbox(v_val_1058_);
lean_dec(v_val_1058_);
v___x_1096_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1095_);
v___x_1097_ = lean_string_append(v___x_1094_, v___x_1096_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1099_ = lean_string_append(v___x_1097_, v___x_1098_);
v___x_1100_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1056_, v___x_1024_);
v___x_1101_ = lean_string_append(v___x_1099_, v___x_1100_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1103_ = lean_string_append(v___x_1101_, v___x_1102_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 3);
lean_ctor_set(v___x_1060_, 0, v___x_1103_);
v___x_1105_ = v___x_1060_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = l_Lean_MessageData_ofFormat(v___x_1105_);
v___x_1107_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_1037_, v___x_1106_, v_snd_1042_, v___x_1010_, v_a_985_);
lean_dec(v_snd_1042_);
lean_dec(v_tailKey_1037_);
return v___x_1107_;
}
}
}
}
else
{
lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1135_; 
lean_inc_ref(v_items_1055_);
lean_inc(v_currArrKey_1054_);
lean_inc(v_arrParents_1053_);
lean_inc(v_arrKeyTys_1052_);
lean_inc(v_keyTys_1051_);
lean_dec(v___x_1057_);
lean_dec(v_tailKey_1037_);
lean_dec_ref(v___x_1010_);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_snd_1042_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; lean_object* v_unused_1137_; lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; lean_object* v_unused_1141_; 
v_unused_1136_ = lean_ctor_get(v_snd_1042_, 5);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_snd_1042_, 4);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_snd_1042_, 3);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_snd_1042_, 2);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_snd_1042_, 1);
lean_dec(v_unused_1140_);
v_unused_1141_ = lean_ctor_get(v_snd_1042_, 0);
lean_dec(v_unused_1141_);
v___x_1111_ = v_snd_1042_;
v_isShared_1112_ = v_isSharedCheck_1135_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v_snd_1042_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1135_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = 2;
v___x_1115_ = lean_box(v___x_1114_);
lean_inc(v___x_1056_);
v___x_1116_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1056_, v___x_1115_, v_keyTys_1051_);
lean_inc(v___x_1116_);
lean_inc(v_currArrKey_1054_);
v___x_1117_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_1054_, v___x_1116_, v_arrKeyTys_1052_);
lean_inc(v___x_1056_);
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1056_, v_currArrKey_1054_, v_arrParents_1053_);
v___x_1119_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
lean_inc(v_x_982_);
v___x_1120_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_x_982_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_mk_empty_array_with_capacity(v___x_1035_);
v___x_1122_ = lean_array_push(v___x_1121_, v___x_1120_);
lean_inc(v_x_982_);
v___x_1123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_x_982_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
lean_inc(v___x_1056_);
v___x_1124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1124_, 0, v_x_982_);
lean_ctor_set(v___x_1124_, 1, v___x_1056_);
lean_ctor_set(v___x_1124_, 2, v___x_1123_);
v___x_1125_ = lean_array_push(v_items_1055_, v___x_1124_);
lean_inc(v___x_1056_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 5, v___x_1125_);
lean_ctor_set(v___x_1111_, 4, v___x_1056_);
lean_ctor_set(v___x_1111_, 3, v___x_1056_);
lean_ctor_set(v___x_1111_, 2, v___x_1118_);
lean_ctor_set(v___x_1111_, 1, v___x_1117_);
lean_ctor_set(v___x_1111_, 0, v___x_1116_);
v___x_1127_ = v___x_1111_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1134_, 5, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v___x_1127_);
lean_ctor_set(v___x_1044_, 0, v___x_1113_);
v___x_1129_ = v___x_1044_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1129_);
v___x_1131_ = v___x_1049_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_del_object(v___x_1044_);
lean_dec(v_snd_1042_);
lean_dec(v_fst_1041_);
lean_dec(v_tailKey_1037_);
lean_dec_ref(v___x_1010_);
lean_dec(v_x_982_);
v_a_1143_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1046_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1046_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_tailKey_1037_);
lean_dec_ref(v___x_1010_);
lean_dec(v_x_982_);
v_a_1152_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1039_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1039_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
v___jp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1013_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_1014_ = l_Lean_MessageData_ofName(v___y_1012_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_1017_, v___x_1010_, v_a_985_);
lean_dec_ref(v___x_1010_);
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
return v_res_1186_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1189_ = l_Lean_stringToMessageData(v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1190_);
v___x_1196_ = l_Lean_Syntax_isOfKind(v_x_1190_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_x_1190_);
v___x_1198_ = l_Lean_Syntax_isOfKind(v_x_1190_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1190_);
v___x_1200_ = l_Lean_Syntax_isOfKind(v_x_1190_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1202_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1190_, v___x_1201_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1191_);
lean_dec(v_x_1190_);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; 
v___x_1203_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
return v___x_1203_;
}
}
else
{
lean_object* v___x_1204_; 
v___x_1204_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
return v___x_1204_;
}
}
else
{
lean_object* v___x_1205_; 
v___x_1205_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1212_, lean_object* v_as_1213_, size_t v_i_1214_, size_t v_stop_1215_, lean_object* v_b_1216_){
_start:
{
lean_object* v___y_1218_; uint8_t v___x_1222_; 
v___x_1222_ = lean_usize_dec_eq(v_i_1214_, v_stop_1215_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v_fst_1224_; lean_object* v_snd_1225_; lean_object* v___x_1226_; 
v___x_1223_ = lean_array_uget_borrowed(v_as_1213_, v_i_1214_);
v_fst_1224_ = lean_ctor_get(v___x_1223_, 0);
v_snd_1225_ = lean_ctor_get(v___x_1223_, 1);
lean_inc(v_fst_1224_);
v___x_1226_ = l_Lean_Name_components(v_fst_1224_);
if (lean_obj_tag(v___x_1226_) == 0)
{
v___y_1218_ = v_b_1216_;
goto v___jp_1217_;
}
else
{
lean_object* v_head_1227_; lean_object* v_tail_1228_; lean_object* v___x_1229_; 
v_head_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_head_1227_);
v_tail_1228_ = lean_ctor_get(v___x_1226_, 1);
lean_inc(v_tail_1228_);
lean_dec_ref(v___x_1226_);
lean_inc(v_snd_1225_);
lean_inc(v_ref_1212_);
v___x_1229_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1216_, v_ref_1212_, v_head_1227_, v_tail_1228_, v_snd_1225_);
v___y_1218_ = v___x_1229_;
goto v___jp_1217_;
}
}
else
{
lean_dec(v_ref_1212_);
return v_b_1216_;
}
v___jp_1217_:
{
size_t v___x_1219_; size_t v___x_1220_; 
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_add(v_i_1214_, v___x_1219_);
v_i_1214_ = v___x_1220_;
v_b_1216_ = v___y_1218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1230_, size_t v_i_1231_, lean_object* v_bs_1232_){
_start:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_usize_dec_lt(v_i_1231_, v_sz_1230_);
if (v___x_1233_ == 0)
{
return v_bs_1232_;
}
else
{
lean_object* v_v_1234_; lean_object* v___x_1235_; lean_object* v_bs_x27_1236_; lean_object* v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v_v_1234_ = lean_array_uget(v_bs_1232_, v_i_1231_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v_bs_x27_1236_ = lean_array_uset(v_bs_1232_, v_i_1231_, v___x_1235_);
v___x_1237_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1234_);
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1231_, v___x_1238_);
v___x_1240_ = lean_array_uset(v_bs_x27_1236_, v_i_1231_, v___x_1237_);
v_i_1231_ = v___x_1239_;
v_bs_1232_ = v___x_1240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1242_){
_start:
{
switch(lean_obj_tag(v_a_1242_))
{
case 6:
{
lean_object* v_xs_1243_; lean_object* v_ref_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1272_; 
v_xs_1243_ = lean_ctor_get(v_a_1242_, 1);
v_ref_1244_ = lean_ctor_get(v_a_1242_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_a_1242_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1246_ = v_a_1242_;
v_isShared_1247_ = v_isSharedCheck_1272_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_xs_1243_);
lean_inc(v_ref_1244_);
lean_dec(v_a_1242_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1272_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_items_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_items_1248_ = lean_ctor_get(v_xs_1243_, 0);
lean_inc_ref(v_items_1248_);
lean_dec_ref(v_xs_1243_);
v___x_1249_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_array_get_size(v_items_1248_);
v___x_1252_ = lean_nat_dec_lt(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1254_; 
lean_dec_ref(v_items_1248_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1249_);
v___x_1254_ = v___x_1246_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_ref_1244_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
else
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_nat_dec_le(v___x_1251_, v___x_1251_);
if (v___x_1256_ == 0)
{
if (v___x_1252_ == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref(v_items_1248_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1249_);
v___x_1258_ = v___x_1246_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_ref_1244_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1249_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
else
{
size_t v___x_1260_; size_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1260_ = ((size_t)0ULL);
v___x_1261_ = lean_usize_of_nat(v___x_1251_);
lean_inc(v_ref_1244_);
v___x_1262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1244_, v_items_1248_, v___x_1260_, v___x_1261_, v___x_1249_);
lean_dec_ref(v_items_1248_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1262_);
v___x_1264_ = v___x_1246_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_ref_1244_);
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
else
{
size_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1266_ = ((size_t)0ULL);
v___x_1267_ = lean_usize_of_nat(v___x_1251_);
lean_inc(v_ref_1244_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1244_, v_items_1248_, v___x_1266_, v___x_1267_, v___x_1249_);
lean_dec_ref(v_items_1248_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1268_);
v___x_1270_ = v___x_1246_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_ref_1244_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
case 5:
{
lean_object* v_ref_1273_; lean_object* v_xs_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1284_; 
v_ref_1273_ = lean_ctor_get(v_a_1242_, 0);
v_xs_1274_ = lean_ctor_get(v_a_1242_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_a_1242_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1276_ = v_a_1242_;
v_isShared_1277_ = v_isSharedCheck_1284_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_xs_1274_);
lean_inc(v_ref_1273_);
lean_dec(v_a_1242_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1284_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
size_t v_sz_1278_; size_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v_sz_1278_ = lean_array_size(v_xs_1274_);
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1278_, v___x_1279_, v_xs_1274_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1280_);
v___x_1282_ = v___x_1276_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_ref_1273_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
default: 
{
return v_a_1242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1285_, lean_object* v___x_1286_, lean_object* v_v_x3f_1287_){
_start:
{
if (lean_obj_tag(v_v_x3f_1287_) == 1)
{
lean_object* v_val_1288_; 
v_val_1288_ = lean_ctor_get(v_v_x3f_1287_, 0);
lean_inc(v_val_1288_);
lean_dec_ref(v_v_x3f_1287_);
switch(lean_obj_tag(v_val_1288_))
{
case 6:
{
lean_object* v_ref_1289_; lean_object* v_xs_1290_; lean_object* v___x_1291_; 
v_ref_1289_ = lean_ctor_get(v_val_1288_, 0);
lean_inc(v_ref_1289_);
v_xs_1290_ = lean_ctor_get(v_val_1288_, 1);
lean_inc_ref(v_xs_1290_);
lean_dec_ref(v_val_1288_);
v___x_1291_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1285_);
if (lean_obj_tag(v___x_1291_) == 6)
{
lean_object* v_xs_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1301_; 
v_xs_1292_ = lean_ctor_get(v___x_1291_, 1);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v___x_1291_, 0);
lean_dec(v_unused_1302_);
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1301_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_xs_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1301_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v_items_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v_items_1296_ = lean_ctor_get(v_xs_1292_, 0);
lean_inc_ref(v_items_1296_);
lean_dec_ref(v_xs_1292_);
v___x_1297_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1286_, v_xs_1290_, v_items_1296_);
lean_dec_ref(v_items_1296_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 1, v___x_1297_);
lean_ctor_set(v___x_1294_, 0, v_ref_1289_);
v___x_1299_ = v___x_1294_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_ref_1289_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_dec_ref(v_xs_1290_);
lean_dec(v_ref_1289_);
lean_dec_ref(v___x_1286_);
return v___x_1291_;
}
}
case 5:
{
lean_object* v_ref_1303_; lean_object* v_xs_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v___x_1286_);
v_ref_1303_ = lean_ctor_get(v_val_1288_, 0);
v_xs_1304_ = lean_ctor_get(v_val_1288_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_val_1288_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1306_ = v_val_1288_;
v_isShared_1307_ = v_isSharedCheck_1323_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_xs_1304_);
lean_inc(v_ref_1303_);
lean_dec(v_val_1288_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1323_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; 
v___x_1308_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1285_);
if (lean_obj_tag(v___x_1308_) == 5)
{
lean_object* v_xs_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
lean_del_object(v___x_1306_);
v_xs_1309_ = lean_ctor_get(v___x_1308_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1308_, 0);
lean_dec(v_unused_1318_);
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_xs_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = l_Array_append___redArg(v_xs_1304_, v_xs_1309_);
lean_dec_ref(v_xs_1309_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v___x_1313_);
lean_ctor_set(v___x_1311_, 0, v_ref_1303_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_ref_1303_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_array_push(v_xs_1304_, v___x_1308_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___x_1319_);
v___x_1321_ = v___x_1306_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_ref_1303_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
default: 
{
lean_object* v___x_1324_; 
lean_dec(v_val_1288_);
lean_dec_ref(v___x_1286_);
v___x_1324_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1285_);
return v___x_1324_;
}
}
}
else
{
lean_object* v___x_1325_; 
lean_dec(v_v_x3f_1287_);
lean_dec_ref(v___x_1286_);
v___x_1325_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1285_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1326_, lean_object* v_k_1327_, lean_object* v_t_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1328_);
lean_inc(v_k_1327_);
v___x_1330_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1329_, v_k_1327_, v_t_1328_);
if (lean_obj_tag(v___x_1330_) == 1)
{
lean_object* v_val_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_k_1327_);
v_val_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1366_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_val_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1366_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_items_1335_; lean_object* v_indices_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1365_; 
v_items_1335_ = lean_ctor_get(v_t_1328_, 0);
v_indices_1336_ = lean_ctor_get(v_t_1328_, 1);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_t_1328_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1338_ = v_t_1328_;
v_isShared_1339_ = v_isSharedCheck_1365_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_indices_1336_);
lean_inc(v_items_1335_);
lean_dec(v_t_1328_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1365_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = lean_array_get_size(v_items_1335_);
v___x_1341_ = lean_nat_dec_lt(v_val_1331_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1343_; 
lean_del_object(v___x_1333_);
lean_dec(v_val_1331_);
lean_dec_ref(v_newV_1326_);
if (v_isShared_1339_ == 0)
{
v___x_1343_ = v___x_1338_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_items_1335_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_indices_1336_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
else
{
lean_object* v_v_1345_; lean_object* v_fst_1346_; lean_object* v_snd_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1364_; 
v_v_1345_ = lean_array_fget(v_items_1335_, v_val_1331_);
v_fst_1346_ = lean_ctor_get(v_v_1345_, 0);
v_snd_1347_ = lean_ctor_get(v_v_1345_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_v_1345_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1349_ = v_v_1345_;
v_isShared_1350_ = v_isSharedCheck_1364_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snd_1347_);
lean_inc(v_fst_1346_);
lean_dec(v_v_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1364_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v_xs_x27_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_box(0);
v_xs_x27_1352_ = lean_array_fset(v_items_1335_, v_val_1331_, v___x_1351_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v_snd_1347_);
v___x_1354_ = v___x_1333_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_snd_1347_);
v___x_1354_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1326_, v___x_1329_, v___x_1354_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v___x_1355_);
v___x_1357_ = v___x_1349_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_fst_1346_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_array_fset(v_xs_x27_1352_, v_val_1331_, v___x_1357_);
lean_dec(v_val_1331_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1358_);
v___x_1360_ = v___x_1338_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_indices_1336_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
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
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v___x_1330_);
v___x_1367_ = lean_box(0);
v___x_1368_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1326_, v___x_1329_, v___x_1367_);
v___x_1369_ = l_Lake_Toml_RBDict_push___redArg(v___x_1329_, v_k_1327_, v___x_1368_, v_t_1328_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1370_, lean_object* v_head_1371_, lean_object* v_tail_1372_, lean_object* v_newV_1373_, lean_object* v___x_1374_, lean_object* v_v_x3f_1375_){
_start:
{
if (lean_obj_tag(v_v_x3f_1375_) == 1)
{
lean_object* v_val_1376_; 
v_val_1376_ = lean_ctor_get(v_v_x3f_1375_, 0);
lean_inc(v_val_1376_);
lean_dec_ref(v_v_x3f_1375_);
switch(lean_obj_tag(v_val_1376_))
{
case 5:
{
lean_object* v_ref_1377_; lean_object* v_xs_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_ref_1377_ = lean_ctor_get(v_val_1376_, 0);
v_xs_1378_ = lean_ctor_get(v_val_1376_, 1);
v___x_1379_ = lean_array_get_size(v_xs_1378_);
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_nat_sub(v___x_1379_, v___x_1380_);
v___x_1382_ = lean_nat_dec_lt(v___x_1381_, v___x_1379_);
if (v___x_1382_ == 0)
{
lean_dec(v___x_1381_);
lean_dec_ref(v_newV_1373_);
lean_dec(v_tail_1372_);
lean_dec(v_head_1371_);
lean_dec(v_kRef_1370_);
return v_val_1376_;
}
else
{
lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1407_; 
lean_inc_ref(v_xs_1378_);
lean_inc(v_ref_1377_);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_val_1376_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; lean_object* v_unused_1409_; 
v_unused_1408_ = lean_ctor_get(v_val_1376_, 1);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_val_1376_, 0);
lean_dec(v_unused_1409_);
v___x_1384_ = v_val_1376_;
v_isShared_1385_ = v_isSharedCheck_1407_;
goto v_resetjp_1383_;
}
else
{
lean_dec(v_val_1376_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1407_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v_v_1386_; lean_object* v___x_1387_; lean_object* v_xs_x27_1388_; lean_object* v___y_1390_; 
v_v_1386_ = lean_array_fget(v_xs_1378_, v___x_1381_);
v___x_1387_ = lean_box(0);
v_xs_x27_1388_ = lean_array_fset(v_xs_1378_, v___x_1381_, v___x_1387_);
if (lean_obj_tag(v_v_1386_) == 6)
{
lean_object* v_ref_1395_; lean_object* v_xs_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1404_; 
v_ref_1395_ = lean_ctor_get(v_v_1386_, 0);
v_xs_1396_ = lean_ctor_get(v_v_1386_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_v_1386_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1398_ = v_v_1386_;
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_xs_1396_);
lean_inc(v_ref_1395_);
lean_dec(v_v_1386_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1396_, v_kRef_1370_, v_head_1371_, v_tail_1372_, v_newV_1373_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_ref_1395_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
v___y_1390_ = v___x_1402_;
goto v___jp_1389_;
}
}
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec(v_v_1386_);
lean_dec_ref(v_newV_1373_);
lean_dec(v_tail_1372_);
lean_dec(v_head_1371_);
v___x_1405_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1374_);
v___x_1406_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_kRef_1370_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___y_1390_ = v___x_1406_;
goto v___jp_1389_;
}
v___jp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_array_fset(v_xs_x27_1388_, v___x_1381_, v___y_1390_);
lean_dec(v___x_1381_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v___x_1391_);
v___x_1393_ = v___x_1384_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_ref_1377_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1391_);
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
case 6:
{
lean_object* v_ref_1410_; lean_object* v_xs_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1419_; 
v_ref_1410_ = lean_ctor_get(v_val_1376_, 0);
v_xs_1411_ = lean_ctor_get(v_val_1376_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_val_1376_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1413_ = v_val_1376_;
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_xs_1411_);
lean_inc(v_ref_1410_);
lean_dec(v_val_1376_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1411_, v_kRef_1370_, v_head_1371_, v_tail_1372_, v_newV_1373_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v___x_1415_);
v___x_1417_ = v___x_1413_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_ref_1410_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
default: 
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec(v_val_1376_);
v___x_1420_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1374_);
lean_inc(v_kRef_1370_);
v___x_1421_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1420_, v_kRef_1370_, v_head_1371_, v_tail_1372_, v_newV_1373_);
v___x_1422_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_kRef_1370_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
return v___x_1422_;
}
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v_v_x3f_1375_);
v___x_1423_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1374_);
lean_inc(v_kRef_1370_);
v___x_1424_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1423_, v_kRef_1370_, v_head_1371_, v_tail_1372_, v_newV_1373_);
v___x_1425_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_kRef_1370_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
return v___x_1425_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1426_, lean_object* v_head_1427_, lean_object* v_tail_1428_, lean_object* v_newV_1429_, lean_object* v_k_1430_, lean_object* v_t_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0));
lean_inc_ref(v_t_1431_);
lean_inc(v_k_1430_);
v___x_1433_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1432_, v_k_1430_, v_t_1431_);
if (lean_obj_tag(v___x_1433_) == 1)
{
lean_object* v_val_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v_k_1430_);
v_val_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1469_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_val_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1469_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_items_1438_; lean_object* v_indices_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1468_; 
v_items_1438_ = lean_ctor_get(v_t_1431_, 0);
v_indices_1439_ = lean_ctor_get(v_t_1431_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_t_1431_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1441_ = v_t_1431_;
v_isShared_1442_ = v_isSharedCheck_1468_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_indices_1439_);
lean_inc(v_items_1438_);
lean_dec(v_t_1431_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1468_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = lean_array_get_size(v_items_1438_);
v___x_1444_ = lean_nat_dec_lt(v_val_1434_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1446_; 
lean_del_object(v___x_1436_);
lean_dec(v_val_1434_);
lean_dec_ref(v_newV_1429_);
lean_dec(v_tail_1428_);
lean_dec(v_head_1427_);
lean_dec(v_kRef_1426_);
if (v_isShared_1442_ == 0)
{
v___x_1446_ = v___x_1441_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_items_1438_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_indices_1439_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
else
{
lean_object* v_v_1448_; lean_object* v_fst_1449_; lean_object* v_snd_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1467_; 
v_v_1448_ = lean_array_fget(v_items_1438_, v_val_1434_);
v_fst_1449_ = lean_ctor_get(v_v_1448_, 0);
v_snd_1450_ = lean_ctor_get(v_v_1448_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_v_1448_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1452_ = v_v_1448_;
v_isShared_1453_ = v_isSharedCheck_1467_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_snd_1450_);
lean_inc(v_fst_1449_);
lean_dec(v_v_1448_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1467_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v_xs_x27_1455_; lean_object* v___x_1457_; 
v___x_1454_ = lean_box(0);
v_xs_x27_1455_ = lean_array_fset(v_items_1438_, v_val_1434_, v___x_1454_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v_snd_1450_);
v___x_1457_ = v___x_1436_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_snd_1450_);
v___x_1457_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1426_, v_head_1427_, v_tail_1428_, v_newV_1429_, v___x_1432_, v___x_1457_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 1, v___x_1458_);
v___x_1460_ = v___x_1452_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_fst_1449_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = lean_array_fset(v_xs_x27_1455_, v_val_1434_, v___x_1460_);
lean_dec(v_val_1434_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1461_);
v___x_1463_ = v___x_1441_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_indices_1439_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
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
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec(v___x_1433_);
v___x_1470_ = lean_box(0);
v___x_1471_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1426_, v_head_1427_, v_tail_1428_, v_newV_1429_, v___x_1432_, v___x_1470_);
v___x_1472_ = l_Lake_Toml_RBDict_push___redArg(v___x_1432_, v_k_1430_, v___x_1471_, v_t_1431_);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1473_, lean_object* v_kRef_1474_, lean_object* v_k_1475_, lean_object* v_ks_1476_, lean_object* v_newV_1477_){
_start:
{
if (lean_obj_tag(v_ks_1476_) == 0)
{
lean_object* v___x_1478_; 
lean_dec(v_kRef_1474_);
v___x_1478_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1477_, v_k_1475_, v_t_1473_);
return v___x_1478_;
}
else
{
lean_object* v_head_1479_; lean_object* v_tail_1480_; lean_object* v___x_1481_; 
v_head_1479_ = lean_ctor_get(v_ks_1476_, 0);
lean_inc(v_head_1479_);
v_tail_1480_ = lean_ctor_get(v_ks_1476_, 1);
lean_inc(v_tail_1480_);
lean_dec_ref(v_ks_1476_);
v___x_1481_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1474_, v_head_1479_, v_tail_1480_, v_newV_1477_, v_k_1475_, v_t_1473_);
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1482_, lean_object* v_i_1483_, lean_object* v_bs_1484_){
_start:
{
size_t v_sz_boxed_1485_; size_t v_i_boxed_1486_; lean_object* v_res_1487_; 
v_sz_boxed_1485_ = lean_unbox_usize(v_sz_1482_);
lean_dec(v_sz_1482_);
v_i_boxed_1486_ = lean_unbox_usize(v_i_1483_);
lean_dec(v_i_1483_);
v_res_1487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1485_, v_i_boxed_1486_, v_bs_1484_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1488_, lean_object* v_as_1489_, lean_object* v_i_1490_, lean_object* v_stop_1491_, lean_object* v_b_1492_){
_start:
{
size_t v_i_boxed_1493_; size_t v_stop_boxed_1494_; lean_object* v_res_1495_; 
v_i_boxed_1493_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_stop_boxed_1494_ = lean_unbox_usize(v_stop_1491_);
lean_dec(v_stop_1491_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1488_, v_as_1489_, v_i_boxed_1493_, v_stop_boxed_1494_, v_b_1492_);
lean_dec_ref(v_as_1489_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0___boxed(lean_object* v_kRef_1496_, lean_object* v_head_1497_, lean_object* v_tail_1498_, lean_object* v_newV_1499_, lean_object* v___x_1500_, lean_object* v_v_x3f_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1496_, v_head_1497_, v_tail_1498_, v_newV_1499_, v___x_1500_, v_v_x3f_1501_);
lean_dec_ref(v___x_1500_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1503_, size_t v_i_1504_, size_t v_stop_1505_, lean_object* v_b_1506_){
_start:
{
lean_object* v___y_1508_; uint8_t v___x_1512_; 
v___x_1512_ = lean_usize_dec_eq(v_i_1504_, v_stop_1505_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v_ref_1514_; lean_object* v_key_1515_; lean_object* v_val_1516_; lean_object* v___x_1517_; 
v___x_1513_ = lean_array_uget_borrowed(v_as_1503_, v_i_1504_);
v_ref_1514_ = lean_ctor_get(v___x_1513_, 0);
v_key_1515_ = lean_ctor_get(v___x_1513_, 1);
v_val_1516_ = lean_ctor_get(v___x_1513_, 2);
lean_inc(v_key_1515_);
v___x_1517_ = l_Lean_Name_components(v_key_1515_);
if (lean_obj_tag(v___x_1517_) == 0)
{
v___y_1508_ = v_b_1506_;
goto v___jp_1507_;
}
else
{
lean_object* v_head_1518_; lean_object* v_tail_1519_; lean_object* v___x_1520_; 
v_head_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_head_1518_);
v_tail_1519_ = lean_ctor_get(v___x_1517_, 1);
lean_inc(v_tail_1519_);
lean_dec_ref(v___x_1517_);
lean_inc_ref(v_val_1516_);
lean_inc(v_ref_1514_);
v___x_1520_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1506_, v_ref_1514_, v_head_1518_, v_tail_1519_, v_val_1516_);
v___y_1508_ = v___x_1520_;
goto v___jp_1507_;
}
}
else
{
return v_b_1506_;
}
v___jp_1507_:
{
size_t v___x_1509_; size_t v___x_1510_; 
v___x_1509_ = ((size_t)1ULL);
v___x_1510_ = lean_usize_add(v_i_1504_, v___x_1509_);
v_i_1504_ = v___x_1510_;
v_b_1506_ = v___y_1508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1521_, lean_object* v_i_1522_, lean_object* v_stop_1523_, lean_object* v_b_1524_){
_start:
{
size_t v_i_boxed_1525_; size_t v_stop_boxed_1526_; lean_object* v_res_1527_; 
v_i_boxed_1525_ = lean_unbox_usize(v_i_1522_);
lean_dec(v_i_1522_);
v_stop_boxed_1526_ = lean_unbox_usize(v_stop_1523_);
lean_dec(v_stop_1523_);
v_res_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1521_, v_i_boxed_1525_, v_stop_boxed_1526_, v_b_1524_);
lean_dec_ref(v_as_1521_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1529_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = lean_array_get_size(v_items_1528_);
v___x_1532_ = lean_nat_dec_lt(v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
return v___x_1529_;
}
else
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_nat_dec_le(v___x_1531_, v___x_1531_);
if (v___x_1533_ == 0)
{
if (v___x_1532_ == 0)
{
return v___x_1529_;
}
else
{
size_t v___x_1534_; size_t v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = ((size_t)0ULL);
v___x_1535_ = lean_usize_of_nat(v___x_1531_);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1528_, v___x_1534_, v___x_1535_, v___x_1529_);
return v___x_1536_;
}
}
else
{
size_t v___x_1537_; size_t v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = ((size_t)0ULL);
v___x_1538_ = lean_usize_of_nat(v___x_1531_);
v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1528_, v___x_1537_, v___x_1538_, v___x_1529_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1540_);
lean_dec_ref(v_items_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1547_ = lean_apply_4(v_x_1542_, v___x_1546_, v_a_1543_, v_a_1544_, lean_box(0));
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1558_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_snd_1552_; lean_object* v_items_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v_snd_1552_ = lean_ctor_get(v_a_1548_, 1);
lean_inc(v_snd_1552_);
lean_dec(v_a_1548_);
v_items_1553_ = lean_ctor_get(v_snd_1552_, 5);
lean_inc_ref(v_items_1553_);
lean_dec(v_snd_1552_);
v___x_1554_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1553_);
lean_dec_ref(v_items_1553_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1554_);
v___x_1556_ = v___x_1550_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
v_a_1559_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1547_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1547_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1567_, v_a_1568_, v_a_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v___y_1580_, uint8_t v_suppressElabErrors_1581_, lean_object* v_x_1582_){
_start:
{
if (lean_obj_tag(v_x_1582_) == 1)
{
lean_object* v_pre_1583_; 
v_pre_1583_ = lean_ctor_get(v_x_1582_, 0);
switch(lean_obj_tag(v_pre_1583_))
{
case 1:
{
lean_object* v_pre_1584_; 
v_pre_1584_ = lean_ctor_get(v_pre_1583_, 0);
switch(lean_obj_tag(v_pre_1584_))
{
case 0:
{
lean_object* v_str_1585_; lean_object* v_str_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_str_1585_ = lean_ctor_get(v_x_1582_, 1);
v_str_1586_ = lean_ctor_get(v_pre_1583_, 1);
v___x_1587_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1588_ = lean_string_dec_eq(v_str_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1590_ = lean_string_dec_eq(v_str_1586_, v___x_1589_);
if (v___x_1590_ == 0)
{
return v___y_1580_;
}
else
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1592_ = lean_string_dec_eq(v_str_1585_, v___x_1591_);
if (v___x_1592_ == 0)
{
return v___y_1580_;
}
else
{
return v_suppressElabErrors_1581_;
}
}
}
else
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1594_ = lean_string_dec_eq(v_str_1585_, v___x_1593_);
if (v___x_1594_ == 0)
{
return v___y_1580_;
}
else
{
return v_suppressElabErrors_1581_;
}
}
}
case 1:
{
lean_object* v_pre_1595_; 
v_pre_1595_ = lean_ctor_get(v_pre_1584_, 0);
if (lean_obj_tag(v_pre_1595_) == 0)
{
lean_object* v_str_1596_; lean_object* v_str_1597_; lean_object* v_str_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v_str_1596_ = lean_ctor_get(v_x_1582_, 1);
v_str_1597_ = lean_ctor_get(v_pre_1583_, 1);
v_str_1598_ = lean_ctor_get(v_pre_1584_, 1);
v___x_1599_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1600_ = lean_string_dec_eq(v_str_1598_, v___x_1599_);
if (v___x_1600_ == 0)
{
return v___y_1580_;
}
else
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1602_ = lean_string_dec_eq(v_str_1597_, v___x_1601_);
if (v___x_1602_ == 0)
{
return v___y_1580_;
}
else
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1604_ = lean_string_dec_eq(v_str_1596_, v___x_1603_);
if (v___x_1604_ == 0)
{
return v___y_1580_;
}
else
{
return v_suppressElabErrors_1581_;
}
}
}
}
else
{
return v___y_1580_;
}
}
default: 
{
return v___y_1580_;
}
}
}
case 0:
{
lean_object* v_str_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v_str_1605_ = lean_ctor_get(v_x_1582_, 1);
v___x_1606_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1607_ = lean_string_dec_eq(v_str_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
return v___y_1580_;
}
else
{
return v_suppressElabErrors_1581_;
}
}
default: 
{
return v___y_1580_;
}
}
}
else
{
return v___y_1580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v___y_1608_, lean_object* v_suppressElabErrors_1609_, lean_object* v_x_1610_){
_start:
{
uint8_t v___y_11734__boxed_1611_; uint8_t v_suppressElabErrors_boxed_1612_; uint8_t v_res_1613_; lean_object* v_r_1614_; 
v___y_11734__boxed_1611_ = lean_unbox(v___y_1608_);
v_suppressElabErrors_boxed_1612_ = lean_unbox(v_suppressElabErrors_1609_);
v_res_1613_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v___y_11734__boxed_1611_, v_suppressElabErrors_boxed_1612_, v_x_1610_);
lean_dec(v_x_1610_);
v_r_1614_ = lean_box(v_res_1613_);
return v_r_1614_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1615_, lean_object* v_opt_1616_){
_start:
{
lean_object* v_name_1617_; lean_object* v_defValue_1618_; lean_object* v_map_1619_; lean_object* v___x_1620_; 
v_name_1617_ = lean_ctor_get(v_opt_1616_, 0);
v_defValue_1618_ = lean_ctor_get(v_opt_1616_, 1);
v_map_1619_ = lean_ctor_get(v_opts_1615_, 0);
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1619_, v_name_1617_);
if (lean_obj_tag(v___x_1620_) == 0)
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_unbox(v_defValue_1618_);
return v___x_1621_;
}
else
{
lean_object* v_val_1622_; 
v_val_1622_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_val_1622_);
lean_dec_ref(v___x_1620_);
if (lean_obj_tag(v_val_1622_) == 1)
{
uint8_t v_v_1623_; 
v_v_1623_ = lean_ctor_get_uint8(v_val_1622_, 0);
lean_dec_ref(v_val_1622_);
return v_v_1623_;
}
else
{
uint8_t v___x_1624_; 
lean_dec(v_val_1622_);
v___x_1624_ = lean_unbox(v_defValue_1618_);
return v___x_1624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1625_, lean_object* v_opt_1626_){
_start:
{
uint8_t v_res_1627_; lean_object* v_r_1628_; 
v_res_1627_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1625_, v_opt_1626_);
lean_dec_ref(v_opt_1626_);
lean_dec_ref(v_opts_1625_);
v_r_1628_ = lean_box(v_res_1627_);
return v_r_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1630_, lean_object* v_msgData_1631_, uint8_t v_severity_1632_, uint8_t v_isSilent_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_a_1639_; uint8_t v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; uint8_t v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1678_; uint8_t v___y_1679_; lean_object* v___y_1680_; uint8_t v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1702_; uint8_t v___y_1703_; lean_object* v___y_1704_; uint8_t v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1713_; lean_object* v___y_1714_; uint8_t v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; uint8_t v___y_1718_; uint8_t v___y_1719_; uint8_t v___x_1724_; lean_object* v___y_1726_; lean_object* v___y_1727_; uint8_t v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; uint8_t v___y_1731_; uint8_t v___y_1732_; uint8_t v___y_1734_; uint8_t v___x_1750_; 
v___x_1724_ = 2;
v___x_1750_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1632_, v___x_1724_);
if (v___x_1750_ == 0)
{
v___y_1734_ = v___x_1750_;
goto v___jp_1733_;
}
else
{
uint8_t v___x_1751_; 
lean_inc_ref(v_msgData_1631_);
v___x_1751_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1631_);
v___y_1734_ = v___x_1751_;
goto v___jp_1733_;
}
v___jp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_a_1639_);
lean_ctor_set(v___x_1640_, 1, v___y_1634_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
v___jp_1642_:
{
lean_object* v___x_1652_; lean_object* v_currNamespace_1653_; lean_object* v_openDecls_1654_; lean_object* v_env_1655_; lean_object* v_nextMacroScope_1656_; lean_object* v_ngen_1657_; lean_object* v_auxDeclNGen_1658_; lean_object* v_traceState_1659_; lean_object* v_cache_1660_; lean_object* v_messages_1661_; lean_object* v_infoState_1662_; lean_object* v_snapshotTasks_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1676_; 
v___x_1652_ = lean_st_ref_take(v___y_1651_);
v_currNamespace_1653_ = lean_ctor_get(v___y_1650_, 6);
lean_inc(v_currNamespace_1653_);
v_openDecls_1654_ = lean_ctor_get(v___y_1650_, 7);
lean_inc(v_openDecls_1654_);
lean_dec_ref(v___y_1650_);
v_env_1655_ = lean_ctor_get(v___x_1652_, 0);
v_nextMacroScope_1656_ = lean_ctor_get(v___x_1652_, 1);
v_ngen_1657_ = lean_ctor_get(v___x_1652_, 2);
v_auxDeclNGen_1658_ = lean_ctor_get(v___x_1652_, 3);
v_traceState_1659_ = lean_ctor_get(v___x_1652_, 4);
v_cache_1660_ = lean_ctor_get(v___x_1652_, 5);
v_messages_1661_ = lean_ctor_get(v___x_1652_, 6);
v_infoState_1662_ = lean_ctor_get(v___x_1652_, 7);
v_snapshotTasks_1663_ = lean_ctor_get(v___x_1652_, 8);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1665_ = v___x_1652_;
v_isShared_1666_ = v_isSharedCheck_1676_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_snapshotTasks_1663_);
lean_inc(v_infoState_1662_);
lean_inc(v_messages_1661_);
lean_inc(v_cache_1660_);
lean_inc(v_traceState_1659_);
lean_inc(v_auxDeclNGen_1658_);
lean_inc(v_ngen_1657_);
lean_inc(v_nextMacroScope_1656_);
lean_inc(v_env_1655_);
lean_dec(v___x_1652_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1676_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_currNamespace_1653_);
lean_ctor_set(v___x_1667_, 1, v_openDecls_1654_);
v___x_1668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___y_1645_);
v___x_1669_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1669_, 0, v___y_1644_);
lean_ctor_set(v___x_1669_, 1, v___y_1646_);
lean_ctor_set(v___x_1669_, 2, v___y_1647_);
lean_ctor_set(v___x_1669_, 3, v___y_1648_);
lean_ctor_set(v___x_1669_, 4, v___x_1668_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*5, v___y_1649_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*5 + 1, v___y_1643_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*5 + 2, v_isSilent_1633_);
v___x_1670_ = l_Lean_MessageLog_add(v___x_1669_, v_messages_1661_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 6, v___x_1670_);
v___x_1672_ = v___x_1665_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_env_1655_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_nextMacroScope_1656_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_ngen_1657_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_auxDeclNGen_1658_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v_traceState_1659_);
lean_ctor_set(v_reuseFailAlloc_1675_, 5, v_cache_1660_);
lean_ctor_set(v_reuseFailAlloc_1675_, 6, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1675_, 7, v_infoState_1662_);
lean_ctor_set(v_reuseFailAlloc_1675_, 8, v_snapshotTasks_1663_);
v___x_1672_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_st_ref_set(v___y_1651_, v___x_1672_);
v___x_1674_ = lean_box(0);
v_a_1639_ = v___x_1674_;
goto v___jp_1638_;
}
}
}
v___jp_1677_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1700_; 
v___x_1686_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1631_);
v___x_1687_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1686_, v___y_1635_, v___y_1636_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1700_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1700_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_inc_ref(v___y_1682_);
v___x_1692_ = l_Lean_FileMap_toPosition(v___y_1682_, v___y_1684_);
lean_dec(v___y_1684_);
v___x_1693_ = l_Lean_FileMap_toPosition(v___y_1682_, v___y_1685_);
lean_dec(v___y_1685_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 1);
lean_ctor_set(v___x_1690_, 0, v___x_1693_);
v___x_1695_ = v___x_1690_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; 
v___x_1696_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1681_ == 0)
{
lean_dec_ref(v___y_1678_);
v___y_1643_ = v___y_1679_;
v___y_1644_ = v___y_1680_;
v___y_1645_ = v_a_1688_;
v___y_1646_ = v___x_1692_;
v___y_1647_ = v___x_1695_;
v___y_1648_ = v___x_1696_;
v___y_1649_ = v___y_1683_;
v___y_1650_ = v___y_1635_;
v___y_1651_ = v___y_1636_;
goto v___jp_1642_;
}
else
{
uint8_t v___x_1697_; 
lean_inc(v_a_1688_);
v___x_1697_ = l_Lean_MessageData_hasTag(v___y_1678_, v_a_1688_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_dec_ref(v___x_1695_);
lean_dec_ref(v___x_1692_);
lean_dec(v_a_1688_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1635_);
v___x_1698_ = lean_box(0);
v_a_1639_ = v___x_1698_;
goto v___jp_1638_;
}
else
{
v___y_1643_ = v___y_1679_;
v___y_1644_ = v___y_1680_;
v___y_1645_ = v_a_1688_;
v___y_1646_ = v___x_1692_;
v___y_1647_ = v___x_1695_;
v___y_1648_ = v___x_1696_;
v___y_1649_ = v___y_1683_;
v___y_1650_ = v___y_1635_;
v___y_1651_ = v___y_1636_;
goto v___jp_1642_;
}
}
}
}
}
v___jp_1701_:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_Syntax_getTailPos_x3f(v___y_1706_, v___y_1708_);
lean_dec(v___y_1706_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_inc(v___y_1709_);
v___y_1678_ = v___y_1702_;
v___y_1679_ = v___y_1703_;
v___y_1680_ = v___y_1704_;
v___y_1681_ = v___y_1705_;
v___y_1682_ = v___y_1707_;
v___y_1683_ = v___y_1708_;
v___y_1684_ = v___y_1709_;
v___y_1685_ = v___y_1709_;
goto v___jp_1677_;
}
else
{
lean_object* v_val_1711_; 
v_val_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_val_1711_);
lean_dec_ref(v___x_1710_);
v___y_1678_ = v___y_1702_;
v___y_1679_ = v___y_1703_;
v___y_1680_ = v___y_1704_;
v___y_1681_ = v___y_1705_;
v___y_1682_ = v___y_1707_;
v___y_1683_ = v___y_1708_;
v___y_1684_ = v___y_1709_;
v___y_1685_ = v_val_1711_;
goto v___jp_1677_;
}
}
v___jp_1712_:
{
lean_object* v_ref_1720_; lean_object* v___x_1721_; 
v_ref_1720_ = l_Lean_replaceRef(v_ref_1630_, v___y_1716_);
lean_dec(v___y_1716_);
v___x_1721_ = l_Lean_Syntax_getPos_x3f(v_ref_1720_, v___y_1718_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_unsigned_to_nat(0u);
v___y_1702_ = v___y_1713_;
v___y_1703_ = v___y_1719_;
v___y_1704_ = v___y_1714_;
v___y_1705_ = v___y_1715_;
v___y_1706_ = v_ref_1720_;
v___y_1707_ = v___y_1717_;
v___y_1708_ = v___y_1718_;
v___y_1709_ = v___x_1722_;
goto v___jp_1701_;
}
else
{
lean_object* v_val_1723_; 
v_val_1723_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_val_1723_);
lean_dec_ref(v___x_1721_);
v___y_1702_ = v___y_1713_;
v___y_1703_ = v___y_1719_;
v___y_1704_ = v___y_1714_;
v___y_1705_ = v___y_1715_;
v___y_1706_ = v_ref_1720_;
v___y_1707_ = v___y_1717_;
v___y_1708_ = v___y_1718_;
v___y_1709_ = v_val_1723_;
goto v___jp_1701_;
}
}
v___jp_1725_:
{
if (v___y_1732_ == 0)
{
v___y_1713_ = v___y_1727_;
v___y_1714_ = v___y_1726_;
v___y_1715_ = v___y_1728_;
v___y_1716_ = v___y_1729_;
v___y_1717_ = v___y_1730_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v_severity_1632_;
goto v___jp_1712_;
}
else
{
v___y_1713_ = v___y_1727_;
v___y_1714_ = v___y_1726_;
v___y_1715_ = v___y_1728_;
v___y_1716_ = v___y_1729_;
v___y_1717_ = v___y_1730_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___x_1724_;
goto v___jp_1712_;
}
}
v___jp_1733_:
{
if (v___y_1734_ == 0)
{
lean_object* v_fileName_1735_; lean_object* v_fileMap_1736_; lean_object* v_options_1737_; lean_object* v_ref_1738_; uint8_t v_suppressElabErrors_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___f_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; 
v_fileName_1735_ = lean_ctor_get(v___y_1635_, 0);
v_fileMap_1736_ = lean_ctor_get(v___y_1635_, 1);
v_options_1737_ = lean_ctor_get(v___y_1635_, 2);
v_ref_1738_ = lean_ctor_get(v___y_1635_, 5);
v_suppressElabErrors_1739_ = lean_ctor_get_uint8(v___y_1635_, sizeof(void*)*14 + 1);
v___x_1740_ = lean_box(v___y_1734_);
v___x_1741_ = lean_box(v_suppressElabErrors_1739_);
v___f_1742_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1742_, 0, v___x_1740_);
lean_closure_set(v___f_1742_, 1, v___x_1741_);
v___x_1743_ = 1;
v___x_1744_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1632_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_inc_ref(v_fileMap_1736_);
lean_inc(v_ref_1738_);
lean_inc_ref(v_fileName_1735_);
v___y_1726_ = v_fileName_1735_;
v___y_1727_ = v___f_1742_;
v___y_1728_ = v_suppressElabErrors_1739_;
v___y_1729_ = v_ref_1738_;
v___y_1730_ = v_fileMap_1736_;
v___y_1731_ = v___y_1734_;
v___y_1732_ = v___x_1744_;
goto v___jp_1725_;
}
else
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = l_Lean_warningAsError;
v___x_1746_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_options_1737_, v___x_1745_);
lean_inc_ref(v_fileMap_1736_);
lean_inc(v_ref_1738_);
lean_inc_ref(v_fileName_1735_);
v___y_1726_ = v_fileName_1735_;
v___y_1727_ = v___f_1742_;
v___y_1728_ = v_suppressElabErrors_1739_;
v___y_1729_ = v_ref_1738_;
v___y_1730_ = v_fileMap_1736_;
v___y_1731_ = v___y_1734_;
v___y_1732_ = v___x_1746_;
goto v___jp_1725_;
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec_ref(v___y_1635_);
lean_dec_ref(v_msgData_1631_);
v___x_1747_ = lean_box(0);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v___y_1634_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1752_, lean_object* v_msgData_1753_, lean_object* v_severity_1754_, lean_object* v_isSilent_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v_severity_boxed_1760_; uint8_t v_isSilent_boxed_1761_; lean_object* v_res_1762_; 
v_severity_boxed_1760_ = lean_unbox(v_severity_1754_);
v_isSilent_boxed_1761_ = lean_unbox(v_isSilent_1755_);
v_res_1762_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1752_, v_msgData_1753_, v_severity_boxed_1760_, v_isSilent_boxed_1761_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec(v_ref_1752_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1763_, lean_object* v_msgData_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = 2;
v___x_1770_ = 0;
v___x_1771_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1763_, v_msgData_1764_, v___x_1769_, v___x_1770_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1772_, lean_object* v_msgData_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1772_, v_msgData_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec(v_ref_1772_);
return v_res_1778_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1782_ = l_Lean_MessageData_ofFormat(v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1783_, lean_object* v_as_1784_, size_t v_sz_1785_, size_t v_i_1786_, uint8_t v_b_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_snd_1793_; lean_object* v_snd_1794_; lean_object* v___y_1800_; uint8_t v___y_1801_; lean_object* v_a_1818_; uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_lt(v_i_1786_, v_sz_1785_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
v___x_1822_ = lean_box(v_b_1787_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___y_1788_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1826_; uint8_t v_recovering_1827_; 
v_a_1825_ = lean_array_uget_borrowed(v_as_1784_, v_i_1786_);
v___x_1826_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1825_);
v_recovering_1827_ = l_Lean_Syntax_isOfKind(v_a_1825_, v___x_1826_);
if (v_recovering_1827_ == 0)
{
lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
lean_inc(v_a_1825_);
v___x_1829_ = l_Lean_Syntax_isOfKind(v_a_1825_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1825_);
v___x_1831_ = l_Lean_Syntax_isOfKind(v_a_1825_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1789_);
lean_inc_ref(v___y_1788_);
v___x_1833_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1825_, v___x_1832_, v___y_1788_, v___y_1789_, v___y_1790_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v_snd_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v___y_1788_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1833_);
v_snd_1835_ = lean_ctor_get(v_a_1834_, 1);
lean_inc(v_snd_1835_);
lean_dec(v_a_1834_);
v___x_1836_ = lean_box(v_b_1787_);
v_snd_1793_ = v___x_1836_;
v_snd_1794_ = v_snd_1835_;
goto v___jp_1792_;
}
else
{
lean_object* v_a_1837_; 
v_a_1837_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1833_);
v_a_1818_ = v_a_1837_;
goto v___jp_1817_;
}
}
else
{
lean_object* v___x_1838_; 
lean_inc_ref(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc(v_a_1825_);
v___x_1838_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1825_, v___y_1788_, v___y_1789_, v___y_1790_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v_snd_1840_; lean_object* v___x_1841_; 
lean_dec_ref(v___y_1788_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref(v___x_1838_);
v_snd_1840_ = lean_ctor_get(v_a_1839_, 1);
lean_inc(v_snd_1840_);
lean_dec(v_a_1839_);
v___x_1841_ = lean_box(v_recovering_1827_);
v_snd_1793_ = v___x_1841_;
v_snd_1794_ = v_snd_1840_;
goto v___jp_1792_;
}
else
{
lean_object* v_a_1842_; 
v_a_1842_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1838_);
v_a_1818_ = v_a_1842_;
goto v___jp_1817_;
}
}
}
else
{
lean_object* v___x_1843_; 
lean_inc_ref(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc(v_a_1825_);
v___x_1843_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1825_, v___y_1788_, v___y_1789_, v___y_1790_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v_snd_1845_; lean_object* v___x_1846_; 
lean_dec_ref(v___y_1788_);
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v_snd_1845_ = lean_ctor_get(v_a_1844_, 1);
lean_inc(v_snd_1845_);
lean_dec(v_a_1844_);
v___x_1846_ = lean_box(v_recovering_1827_);
v_snd_1793_ = v___x_1846_;
v_snd_1794_ = v_snd_1845_;
goto v___jp_1792_;
}
else
{
lean_object* v_a_1847_; 
v_a_1847_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1843_);
v_a_1818_ = v_a_1847_;
goto v___jp_1817_;
}
}
}
else
{
if (v_b_1787_ == 0)
{
lean_object* v___x_1848_; 
lean_inc(v___y_1790_);
lean_inc_ref(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc(v_a_1825_);
v___x_1848_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1825_, v___y_1788_, v___y_1789_, v___y_1790_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v_snd_1850_; lean_object* v___x_1851_; 
lean_dec_ref(v___y_1788_);
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
v_snd_1850_ = lean_ctor_get(v_a_1849_, 1);
lean_inc(v_snd_1850_);
lean_dec(v_a_1849_);
v___x_1851_ = lean_box(v_b_1787_);
v_snd_1793_ = v___x_1851_;
v_snd_1794_ = v_snd_1850_;
goto v___jp_1792_;
}
else
{
lean_object* v_a_1852_; 
v_a_1852_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1848_);
v_a_1818_ = v_a_1852_;
goto v___jp_1817_;
}
}
else
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_box(v_b_1787_);
v_snd_1793_ = v___x_1853_;
v_snd_1794_ = v___y_1788_;
goto v___jp_1792_;
}
}
}
v___jp_1792_:
{
size_t v___x_1795_; size_t v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = ((size_t)1ULL);
v___x_1796_ = lean_usize_add(v_i_1786_, v___x_1795_);
v___x_1797_ = lean_unbox(v_snd_1793_);
lean_dec(v_snd_1793_);
v_i_1786_ = v___x_1796_;
v_b_1787_ = v___x_1797_;
v___y_1788_ = v_snd_1794_;
goto _start;
}
v___jp_1799_:
{
if (v___y_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = l_Lean_Exception_getRef(v___y_1800_);
v___x_1803_ = l_Lean_Exception_toMessageData(v___y_1800_);
lean_inc_ref(v___y_1789_);
v___x_1804_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1802_, v___x_1803_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___x_1802_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v_snd_1806_; lean_object* v___x_1807_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref(v___x_1804_);
v_snd_1806_ = lean_ctor_get(v_a_1805_, 1);
lean_inc(v_snd_1806_);
lean_dec(v_a_1805_);
v___x_1807_ = lean_box(v_recovering_1783_);
v_snd_1793_ = v___x_1807_;
v_snd_1794_ = v_snd_1806_;
goto v___jp_1792_;
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
v_a_1808_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1804_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1804_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v___x_1816_; 
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec_ref(v___y_1788_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1800_);
return v___x_1816_;
}
}
v___jp_1817_:
{
uint8_t v___x_1819_; 
v___x_1819_ = l_Lean_Exception_isInterrupt(v_a_1818_);
if (v___x_1819_ == 0)
{
uint8_t v___x_1820_; 
lean_inc_ref(v_a_1818_);
v___x_1820_ = l_Lean_Exception_isRuntime(v_a_1818_);
v___y_1800_ = v_a_1818_;
v___y_1801_ = v___x_1820_;
goto v___jp_1799_;
}
else
{
v___y_1800_ = v_a_1818_;
v___y_1801_ = v___x_1819_;
goto v___jp_1799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1854_, lean_object* v_as_1855_, lean_object* v_sz_1856_, lean_object* v_i_1857_, lean_object* v_b_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v_recovering_boxed_1863_; size_t v_sz_boxed_1864_; size_t v_i_boxed_1865_; uint8_t v_b_boxed_1866_; lean_object* v_res_1867_; 
v_recovering_boxed_1863_ = lean_unbox(v_recovering_1854_);
v_sz_boxed_1864_ = lean_unbox_usize(v_sz_1856_);
lean_dec(v_sz_1856_);
v_i_boxed_1865_ = lean_unbox_usize(v_i_1857_);
lean_dec(v_i_1857_);
v_b_boxed_1866_ = lean_unbox(v_b_1858_);
v_res_1867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1863_, v_as_1855_, v_sz_boxed_1864_, v_i_boxed_1865_, v_b_boxed_1866_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec_ref(v_as_1855_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_ref_1872_; lean_object* v___x_1873_; lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
v_ref_1872_ = lean_ctor_get(v___y_1869_, 5);
v___x_1873_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1868_, v___y_1869_, v___y_1870_);
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
lean_inc(v_ref_1872_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v_ref_1872_);
lean_ctor_set(v___x_1878_, 1, v_a_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set_tag(v___x_1876_, 1);
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1888_, lean_object* v_msg_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_fileName_1893_; lean_object* v_fileMap_1894_; lean_object* v_options_1895_; lean_object* v_currRecDepth_1896_; lean_object* v_maxRecDepth_1897_; lean_object* v_ref_1898_; lean_object* v_currNamespace_1899_; lean_object* v_openDecls_1900_; lean_object* v_initHeartbeats_1901_; lean_object* v_maxHeartbeats_1902_; lean_object* v_quotContext_1903_; lean_object* v_currMacroScope_1904_; uint8_t v_diag_1905_; lean_object* v_cancelTk_x3f_1906_; uint8_t v_suppressElabErrors_1907_; lean_object* v_inheritedTraceOptions_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1917_; 
v_fileName_1893_ = lean_ctor_get(v___y_1890_, 0);
v_fileMap_1894_ = lean_ctor_get(v___y_1890_, 1);
v_options_1895_ = lean_ctor_get(v___y_1890_, 2);
v_currRecDepth_1896_ = lean_ctor_get(v___y_1890_, 3);
v_maxRecDepth_1897_ = lean_ctor_get(v___y_1890_, 4);
v_ref_1898_ = lean_ctor_get(v___y_1890_, 5);
v_currNamespace_1899_ = lean_ctor_get(v___y_1890_, 6);
v_openDecls_1900_ = lean_ctor_get(v___y_1890_, 7);
v_initHeartbeats_1901_ = lean_ctor_get(v___y_1890_, 8);
v_maxHeartbeats_1902_ = lean_ctor_get(v___y_1890_, 9);
v_quotContext_1903_ = lean_ctor_get(v___y_1890_, 10);
v_currMacroScope_1904_ = lean_ctor_get(v___y_1890_, 11);
v_diag_1905_ = lean_ctor_get_uint8(v___y_1890_, sizeof(void*)*14);
v_cancelTk_x3f_1906_ = lean_ctor_get(v___y_1890_, 12);
v_suppressElabErrors_1907_ = lean_ctor_get_uint8(v___y_1890_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1908_ = lean_ctor_get(v___y_1890_, 13);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___y_1890_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1910_ = v___y_1890_;
v_isShared_1911_ = v_isSharedCheck_1917_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_inheritedTraceOptions_1908_);
lean_inc(v_cancelTk_x3f_1906_);
lean_inc(v_currMacroScope_1904_);
lean_inc(v_quotContext_1903_);
lean_inc(v_maxHeartbeats_1902_);
lean_inc(v_initHeartbeats_1901_);
lean_inc(v_openDecls_1900_);
lean_inc(v_currNamespace_1899_);
lean_inc(v_ref_1898_);
lean_inc(v_maxRecDepth_1897_);
lean_inc(v_currRecDepth_1896_);
lean_inc(v_options_1895_);
lean_inc(v_fileMap_1894_);
lean_inc(v_fileName_1893_);
lean_dec(v___y_1890_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1917_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v_ref_1912_; lean_object* v___x_1914_; 
v_ref_1912_ = l_Lean_replaceRef(v_ref_1888_, v_ref_1898_);
lean_dec(v_ref_1898_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 5, v_ref_1912_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_fileName_1893_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_fileMap_1894_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_options_1895_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v_currRecDepth_1896_);
lean_ctor_set(v_reuseFailAlloc_1916_, 4, v_maxRecDepth_1897_);
lean_ctor_set(v_reuseFailAlloc_1916_, 5, v_ref_1912_);
lean_ctor_set(v_reuseFailAlloc_1916_, 6, v_currNamespace_1899_);
lean_ctor_set(v_reuseFailAlloc_1916_, 7, v_openDecls_1900_);
lean_ctor_set(v_reuseFailAlloc_1916_, 8, v_initHeartbeats_1901_);
lean_ctor_set(v_reuseFailAlloc_1916_, 9, v_maxHeartbeats_1902_);
lean_ctor_set(v_reuseFailAlloc_1916_, 10, v_quotContext_1903_);
lean_ctor_set(v_reuseFailAlloc_1916_, 11, v_currMacroScope_1904_);
lean_ctor_set(v_reuseFailAlloc_1916_, 12, v_cancelTk_x3f_1906_);
lean_ctor_set(v_reuseFailAlloc_1916_, 13, v_inheritedTraceOptions_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*14, v_diag_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*14 + 1, v_suppressElabErrors_1907_);
v___x_1914_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1889_, v___x_1914_, v___y_1891_);
lean_dec_ref(v___x_1914_);
return v___x_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1918_, lean_object* v_msg_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1918_, v_msg_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec(v_ref_1918_);
return v_res_1923_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1936_);
v___x_1941_ = l_Lean_Syntax_isOfKind(v_x_1936_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1943_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1936_, v___x_1942_, v_a_1937_, v_a_1938_);
lean_dec(v_a_1938_);
lean_dec(v_x_1936_);
return v___x_1943_;
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v_recovering_1947_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = l_Lean_Syntax_getArg(v_x_1936_, v___x_1944_);
v___x_1946_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1947_ = l_Lean_Syntax_isOfKind(v___x_1945_, v___x_1946_);
if (v_recovering_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1949_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1936_, v___x_1948_, v_a_1937_, v_a_1938_);
lean_dec(v_a_1938_);
lean_dec(v_x_1936_);
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v_xs_1952_; uint8_t v_recovering_1953_; lean_object* v___x_1954_; size_t v_sz_1955_; size_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = l_Lean_Syntax_getArg(v_x_1936_, v___x_1950_);
lean_dec(v_x_1936_);
v_xs_1952_ = l_Lean_Syntax_getArgs(v___x_1951_);
lean_dec(v___x_1951_);
v_recovering_1953_ = 0;
v___x_1954_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1952_);
lean_dec_ref(v_xs_1952_);
v_sz_1955_ = lean_array_size(v___x_1954_);
v___x_1956_ = ((size_t)0ULL);
v___x_1957_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1947_, v___x_1954_, v_sz_1955_, v___x_1956_, v_recovering_1953_, v___x_1957_, v_a_1937_, v_a_1938_);
lean_dec_ref(v___x_1954_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1969_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1969_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1969_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_snd_1963_; lean_object* v_items_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v_snd_1963_ = lean_ctor_get(v_a_1959_, 1);
lean_inc(v_snd_1963_);
lean_dec(v_a_1959_);
v_items_1964_ = lean_ctor_get(v_snd_1963_, 5);
lean_inc_ref(v_items_1964_);
lean_dec(v_snd_1963_);
v___x_1965_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1964_);
lean_dec_ref(v_items_1964_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1965_);
v___x_1967_ = v___x_1961_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v_a_1970_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1958_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1958_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lake_Toml_elabToml(v_x_1978_, v_a_1979_, v_a_1980_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1983_, lean_object* v_ref_1984_, lean_object* v_msg_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1984_, v_msg_1985_, v___y_1986_, v___y_1987_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_ref_1991_, lean_object* v_msg_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1990_, v_ref_1991_, v_msg_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec(v_ref_1991_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1997_, lean_object* v_msg_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1998_, v___y_1999_, v___y_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_2003_, v_msg_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
return v_res_2008_;
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
l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy_default = _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy_default();
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
