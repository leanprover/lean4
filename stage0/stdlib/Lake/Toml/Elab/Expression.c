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
lean_object* v___y_803_; lean_object* v_keyTys_804_; lean_object* v_arrKeyTys_805_; lean_object* v_arrParents_806_; lean_object* v_currArrKey_807_; lean_object* v_items_808_; lean_object* v_toCold_820_; lean_object* v_currRecDepth_821_; lean_object* v_ref_822_; uint8_t v_diag_823_; uint8_t v_suppressElabErrors_824_; lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v_ref_827_; lean_object* v___x_828_; 
v_toCold_820_ = lean_ctor_get(v_a_799_, 0);
v_currRecDepth_821_ = lean_ctor_get(v_a_799_, 1);
v_ref_822_ = lean_ctor_get(v_a_799_, 2);
v_diag_823_ = lean_ctor_get_uint8(v_a_799_, sizeof(void*)*3);
v_suppressElabErrors_824_ = lean_ctor_get_uint8(v_a_799_, sizeof(void*)*3 + 1);
v___x_825_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_797_);
v___x_826_ = l_Lean_Syntax_isOfKind(v_x_797_, v___x_825_);
v_ref_827_ = l_Lean_replaceRef(v_x_797_, v_ref_822_);
lean_inc(v_currRecDepth_821_);
lean_inc_ref(v_toCold_820_);
v___x_828_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_828_, 0, v_toCold_820_);
lean_ctor_set(v___x_828_, 1, v_currRecDepth_821_);
lean_ctor_set(v___x_828_, 2, v_ref_827_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*3, v_diag_823_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*3 + 1, v_suppressElabErrors_824_);
if (v___x_826_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4);
v___x_830_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_797_, v___x_829_, v_a_798_, v___x_828_, v_a_800_);
lean_dec_ref_known(v___x_828_, 3);
lean_dec_ref(v_a_798_);
lean_dec(v_x_797_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___y_834_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = l_Lean_Syntax_getArg(v_x_797_, v___x_831_);
v___x_902_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_832_);
v___x_903_ = l_Lean_Syntax_isOfKind(v___x_832_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v_x_797_);
v___x_904_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_905_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_832_, v___x_904_, v_a_798_, v___x_828_, v_a_800_);
lean_dec_ref_known(v___x_828_, 3);
lean_dec_ref(v_a_798_);
lean_dec(v___x_832_);
return v___x_905_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = l_Lean_Syntax_getArg(v___x_832_, v___x_906_);
v___x_908_ = l_Lean_Syntax_getArgs(v___x_907_);
lean_dec(v___x_907_);
v___x_909_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_910_ = lean_array_get_size(v___x_908_);
v___x_911_ = lean_nat_dec_lt(v___x_906_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec_ref(v___x_908_);
v___y_834_ = v___x_909_;
goto v___jp_833_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; lean_object* v_snd_917_; 
v___x_912_ = lean_box(v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_909_);
v___x_914_ = ((size_t)0ULL);
v___x_915_ = lean_usize_of_nat(v___x_910_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_903_, v___x_908_, v___x_914_, v___x_915_, v___x_913_);
lean_dec_ref(v___x_908_);
v_snd_917_ = lean_ctor_get(v___x_916_, 1);
lean_inc(v_snd_917_);
lean_dec_ref(v___x_916_);
v___y_834_ = v_snd_917_;
goto v___jp_833_;
}
}
v___jp_833_:
{
size_t v_sz_835_; size_t v___x_836_; lean_object* v___x_837_; 
v_sz_835_ = lean_array_size(v___y_834_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_835_, v___x_836_, v___y_834_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_x_797_);
v___x_838_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_839_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_832_, v___x_838_, v_a_798_, v___x_828_, v_a_800_);
lean_dec_ref_known(v___x_828_, 3);
lean_dec_ref(v_a_798_);
lean_dec(v___x_832_);
return v___x_839_;
}
else
{
lean_object* v_val_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_tailKey_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v___x_832_);
v_val_840_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_val_840_);
lean_dec_ref_known(v___x_837_, 1);
v___x_841_ = lean_box(0);
v___x_842_ = lean_array_get_size(v_val_840_);
v___x_843_ = lean_nat_sub(v___x_842_, v___x_831_);
v_tailKey_844_ = lean_array_get(v___x_841_, v_val_840_, v___x_843_);
lean_dec(v___x_843_);
v___x_845_ = lean_array_pop(v_val_840_);
v___x_846_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_845_, v_a_798_, v___x_828_, v_a_800_);
lean_dec_ref(v___x_845_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_893_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v_fst_848_ = lean_ctor_get(v_a_847_, 0);
v_snd_849_ = lean_ctor_get(v_a_847_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_a_847_);
if (v_isSharedCheck_893_ == 0)
{
v___x_851_ = v_a_847_;
v_isShared_852_ = v_isSharedCheck_893_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_inc(v_fst_848_);
lean_dec(v_a_847_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_893_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; 
lean_inc(v_tailKey_844_);
v___x_853_ = l_Lake_Toml_elabSimpleKey(v_tailKey_844_, v___x_828_, v_a_800_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v_keyTys_855_; lean_object* v_arrKeyTys_856_; lean_object* v_arrParents_857_; lean_object* v_currArrKey_858_; lean_object* v_items_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v_keyTys_855_ = lean_ctor_get(v_snd_849_, 0);
v_arrKeyTys_856_ = lean_ctor_get(v_snd_849_, 1);
v_arrParents_857_ = lean_ctor_get(v_snd_849_, 2);
v_currArrKey_858_ = lean_ctor_get(v_snd_849_, 3);
v_items_859_ = lean_ctor_get(v_snd_849_, 5);
v___x_860_ = l_Lean_Name_str___override(v_fst_848_, v_a_854_);
v___x_861_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_855_, v___x_860_);
if (lean_obj_tag(v___x_861_) == 1)
{
lean_object* v_val_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_884_; 
v_val_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_884_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_884_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_val_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_884_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint8_t v___x_866_; 
v___x_866_ = lean_unbox(v_val_862_);
if (v___x_866_ == 4)
{
lean_inc_ref(v_items_859_);
lean_inc(v_currArrKey_858_);
lean_inc(v_arrParents_857_);
lean_inc(v_arrKeyTys_856_);
lean_inc(v_keyTys_855_);
lean_del_object(v___x_864_);
lean_dec(v_val_862_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_tailKey_844_);
lean_dec_ref_known(v___x_828_, 3);
v___y_803_ = v___x_860_;
v_keyTys_804_ = v_keyTys_855_;
v_arrKeyTys_805_ = v_arrKeyTys_856_;
v_arrParents_806_ = v_arrParents_857_;
v_currArrKey_807_ = v_currArrKey_858_;
v_items_808_ = v_items_859_;
goto v___jp_802_;
}
else
{
lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_dec(v_x_797_);
v___x_867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_868_ = lean_unbox(v_val_862_);
lean_dec(v_val_862_);
v___x_869_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_868_);
if (v_isShared_865_ == 0)
{
lean_ctor_set_tag(v___x_864_, 3);
lean_ctor_set(v___x_864_, 0, v___x_869_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_883_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = l_Lean_MessageData_ofFormat(v___x_871_);
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 7);
lean_ctor_set(v___x_851_, 1, v___x_872_);
lean_ctor_set(v___x_851_, 0, v___x_867_);
v___x_874_ = v___x_851_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_882_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Lean_MessageData_ofName(v___x_860_);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_844_, v___x_880_, v_snd_849_, v___x_828_, v_a_800_);
lean_dec_ref_known(v___x_828_, 3);
lean_dec(v_snd_849_);
lean_dec(v_tailKey_844_);
return v___x_881_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_859_);
lean_inc(v_currArrKey_858_);
lean_inc(v_arrParents_857_);
lean_inc(v_arrKeyTys_856_);
lean_inc(v_keyTys_855_);
lean_dec(v___x_861_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_tailKey_844_);
lean_dec_ref_known(v___x_828_, 3);
v___y_803_ = v___x_860_;
v_keyTys_804_ = v_keyTys_855_;
v_arrKeyTys_805_ = v_arrKeyTys_856_;
v_arrParents_806_ = v_arrParents_857_;
v_currArrKey_807_ = v_currArrKey_858_;
v_items_808_ = v_items_859_;
goto v___jp_802_;
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_fst_848_);
lean_dec(v_tailKey_844_);
lean_dec_ref_known(v___x_828_, 3);
lean_dec(v_x_797_);
v_a_885_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_853_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_853_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_tailKey_844_);
lean_dec_ref_known(v___x_828_, 3);
lean_dec(v_x_797_);
v_a_894_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_846_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_846_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
return v_res_923_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_toCold_937_; lean_object* v_currRecDepth_938_; lean_object* v_ref_939_; uint8_t v_diag_940_; uint8_t v_suppressElabErrors_941_; lean_object* v___x_942_; uint8_t v___x_943_; lean_object* v_ref_944_; lean_object* v___x_945_; lean_object* v___y_947_; 
v_toCold_937_ = lean_ctor_get(v_a_934_, 0);
v_currRecDepth_938_ = lean_ctor_get(v_a_934_, 1);
v_ref_939_ = lean_ctor_get(v_a_934_, 2);
v_diag_940_ = lean_ctor_get_uint8(v_a_934_, sizeof(void*)*3);
v_suppressElabErrors_941_ = lean_ctor_get_uint8(v_a_934_, sizeof(void*)*3 + 1);
v___x_942_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_932_);
v___x_943_ = l_Lean_Syntax_isOfKind(v_x_932_, v___x_942_);
v_ref_944_ = l_Lean_replaceRef(v_x_932_, v_ref_939_);
lean_inc(v_currRecDepth_938_);
lean_inc_ref(v_toCold_937_);
v___x_945_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_945_, 0, v_toCold_937_);
lean_ctor_set(v___x_945_, 1, v_currRecDepth_938_);
lean_ctor_set(v___x_945_, 2, v_ref_944_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*3, v_diag_940_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*3 + 1, v_suppressElabErrors_941_);
if (v___x_943_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_955_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_932_, v___x_954_, v_a_933_, v___x_945_, v_a_935_);
lean_dec_ref_known(v___x_945_, 3);
lean_dec_ref(v_a_933_);
lean_dec(v_x_932_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; lean_object* v___y_961_; 
v___x_956_ = lean_unsigned_to_nat(2u);
v___x_957_ = l_Lean_Syntax_getArg(v_x_932_, v___x_956_);
v___x_958_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_957_);
v___x_959_ = l_Lean_Syntax_isOfKind(v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v___x_957_);
v___x_1095_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1096_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_932_, v___x_1095_, v_a_933_, v___x_945_, v_a_935_);
lean_dec_ref_known(v___x_945_, 3);
lean_dec_ref(v_a_933_);
lean_dec(v_x_932_);
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = l_Lean_Syntax_getArg(v___x_957_, v___x_1097_);
lean_dec(v___x_957_);
v___x_1099_ = l_Lean_Syntax_getArgs(v___x_1098_);
lean_dec(v___x_1098_);
v___x_1100_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1101_ = lean_array_get_size(v___x_1099_);
v___x_1102_ = lean_nat_dec_lt(v___x_1097_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_dec_ref(v___x_1099_);
v___y_961_ = v___x_1100_;
goto v___jp_960_;
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; lean_object* v___x_1107_; lean_object* v_snd_1108_; 
v___x_1103_ = lean_box(v___x_1102_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v___x_1100_);
v___x_1105_ = ((size_t)0ULL);
v___x_1106_ = lean_usize_of_nat(v___x_1101_);
v___x_1107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_959_, v___x_1099_, v___x_1105_, v___x_1106_, v___x_1104_);
lean_dec_ref(v___x_1099_);
v_snd_1108_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_snd_1108_);
lean_dec_ref(v___x_1107_);
v___y_961_ = v_snd_1108_;
goto v___jp_960_;
}
}
v___jp_960_:
{
size_t v_sz_962_; size_t v___x_963_; lean_object* v___x_964_; 
v_sz_962_ = lean_array_size(v___y_961_);
v___x_963_ = ((size_t)0ULL);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_962_, v___x_963_, v___y_961_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_966_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_932_, v___x_965_, v_a_933_, v___x_945_, v_a_935_);
lean_dec_ref_known(v___x_945_, 3);
lean_dec_ref(v_a_933_);
lean_dec(v_x_932_);
return v___x_966_;
}
else
{
lean_object* v_val_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_tailKey_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_val_967_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_val_967_);
lean_dec_ref_known(v___x_964_, 1);
v___x_968_ = lean_box(0);
v___x_969_ = lean_array_get_size(v_val_967_);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_sub(v___x_969_, v___x_970_);
v_tailKey_972_ = lean_array_get(v___x_968_, v_val_967_, v___x_971_);
lean_dec(v___x_971_);
v___x_973_ = lean_array_pop(v_val_967_);
v___x_974_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_973_, v_a_933_, v___x_945_, v_a_935_);
lean_dec_ref(v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v_fst_976_; lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1086_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v_fst_976_ = lean_ctor_get(v_a_975_, 0);
v_snd_977_ = lean_ctor_get(v_a_975_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_a_975_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_979_ = v_a_975_;
v_isShared_980_ = v_isSharedCheck_1086_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_inc(v_fst_976_);
lean_dec(v_a_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1086_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; 
lean_inc(v_tailKey_972_);
v___x_981_ = l_Lake_Toml_elabSimpleKey(v_tailKey_972_, v___x_945_, v_a_935_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1077_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1077_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1077_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_keyTys_986_; lean_object* v_arrKeyTys_987_; lean_object* v_arrParents_988_; lean_object* v_currArrKey_989_; lean_object* v_items_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_keyTys_986_ = lean_ctor_get(v_snd_977_, 0);
v_arrKeyTys_987_ = lean_ctor_get(v_snd_977_, 1);
v_arrParents_988_ = lean_ctor_get(v_snd_977_, 2);
v_currArrKey_989_ = lean_ctor_get(v_snd_977_, 3);
v_items_990_ = lean_ctor_get(v_snd_977_, 5);
v___x_991_ = l_Lean_Name_str___override(v_fst_976_, v_a_982_);
v___x_992_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_986_, v___x_991_);
if (lean_obj_tag(v___x_992_) == 1)
{
lean_object* v_val_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1044_; 
v_val_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1044_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_val_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1044_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint8_t v___x_997_; 
v___x_997_ = lean_unbox(v_val_993_);
if (v___x_997_ == 2)
{
lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1022_; 
lean_inc_ref(v_items_990_);
lean_inc(v_arrParents_988_);
lean_inc(v_arrKeyTys_987_);
lean_del_object(v___x_995_);
lean_dec(v_val_993_);
lean_dec(v_tailKey_972_);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_snd_977_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; lean_object* v_unused_1027_; lean_object* v_unused_1028_; 
v_unused_1023_ = lean_ctor_get(v_snd_977_, 5);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_snd_977_, 4);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_snd_977_, 3);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_snd_977_, 2);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_snd_977_, 1);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_snd_977_, 0);
lean_dec(v_unused_1028_);
v___x_999_ = v_snd_977_;
v_isShared_1000_ = v_isSharedCheck_1022_;
goto v_resetjp_998_;
}
else
{
lean_dec(v_snd_977_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1022_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_988_, v___x_991_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_del_object(v___x_999_);
lean_dec_ref(v_items_990_);
lean_dec(v_arrParents_988_);
lean_dec(v_arrKeyTys_987_);
lean_del_object(v___x_984_);
lean_del_object(v___x_979_);
lean_dec(v_x_932_);
v___y_947_ = v___x_991_;
goto v___jp_946_;
}
else
{
lean_object* v_val_1002_; lean_object* v___x_1003_; 
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_987_, v_val_1002_);
lean_dec(v_val_1002_);
if (lean_obj_tag(v___x_1003_) == 1)
{
lean_object* v_val_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
lean_dec_ref_known(v___x_945_, 3);
v_val_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_932_, 2);
v___x_1007_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_x_932_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_mk_empty_array_with_capacity(v___x_970_);
v___x_1009_ = lean_array_push(v___x_1008_, v___x_1007_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_x_932_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
lean_inc_n(v___x_991_, 2);
v___x_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1011_, 0, v_x_932_);
lean_ctor_set(v___x_1011_, 1, v___x_991_);
lean_ctor_set(v___x_1011_, 2, v___x_1010_);
v___x_1012_ = lean_array_push(v_items_990_, v___x_1011_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 5, v___x_1012_);
lean_ctor_set(v___x_999_, 4, v___x_991_);
lean_ctor_set(v___x_999_, 3, v___x_991_);
lean_ctor_set(v___x_999_, 0, v_val_1004_);
v___x_1014_ = v___x_999_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_val_1004_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_arrKeyTys_987_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_arrParents_988_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1021_, 5, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_1014_);
lean_ctor_set(v___x_979_, 0, v___x_1005_);
v___x_1016_ = v___x_979_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_1016_);
v___x_1018_ = v___x_984_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_dec(v___x_1003_);
lean_del_object(v___x_999_);
lean_dec_ref(v_items_990_);
lean_dec(v_arrParents_988_);
lean_dec(v_arrKeyTys_987_);
lean_del_object(v___x_984_);
lean_del_object(v___x_979_);
lean_dec(v_x_932_);
v___y_947_ = v___x_991_;
goto v___jp_946_;
}
}
}
}
else
{
lean_object* v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
lean_del_object(v___x_984_);
lean_del_object(v___x_979_);
lean_dec(v_x_932_);
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1030_ = lean_unbox(v_val_993_);
lean_dec(v_val_993_);
v___x_1031_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1030_);
v___x_1032_ = lean_string_append(v___x_1029_, v___x_1031_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1034_ = lean_string_append(v___x_1032_, v___x_1033_);
v___x_1035_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_991_, v___x_959_);
v___x_1036_ = lean_string_append(v___x_1034_, v___x_1035_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1038_ = lean_string_append(v___x_1036_, v___x_1037_);
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 3);
lean_ctor_set(v___x_995_, 0, v___x_1038_);
v___x_1040_ = v___x_995_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = l_Lean_MessageData_ofFormat(v___x_1040_);
v___x_1042_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_972_, v___x_1041_, v_snd_977_, v___x_945_, v_a_935_);
lean_dec_ref_known(v___x_945_, 3);
lean_dec(v_snd_977_);
lean_dec(v_tailKey_972_);
return v___x_1042_;
}
}
}
}
else
{
lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1070_; 
lean_inc_ref(v_items_990_);
lean_inc(v_currArrKey_989_);
lean_inc(v_arrParents_988_);
lean_inc(v_arrKeyTys_987_);
lean_inc(v_keyTys_986_);
lean_dec(v___x_992_);
lean_dec(v_tailKey_972_);
lean_dec_ref_known(v___x_945_, 3);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_snd_977_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; lean_object* v_unused_1072_; lean_object* v_unused_1073_; lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; 
v_unused_1071_ = lean_ctor_get(v_snd_977_, 5);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_snd_977_, 4);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_snd_977_, 3);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_snd_977_, 2);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_snd_977_, 1);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_snd_977_, 0);
lean_dec(v_unused_1076_);
v___x_1046_ = v_snd_977_;
v_isShared_1047_ = v_isSharedCheck_1070_;
goto v_resetjp_1045_;
}
else
{
lean_dec(v_snd_977_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1070_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = 2;
v___x_1050_ = lean_box(v___x_1049_);
lean_inc_n(v___x_991_, 4);
v___x_1051_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_991_, v___x_1050_, v_keyTys_986_);
lean_inc(v___x_1051_);
lean_inc(v_currArrKey_989_);
v___x_1052_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_989_, v___x_1051_, v_arrKeyTys_987_);
v___x_1053_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_991_, v_currArrKey_989_, v_arrParents_988_);
v___x_1054_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_932_, 2);
v___x_1055_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_x_932_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_mk_empty_array_with_capacity(v___x_970_);
v___x_1057_ = lean_array_push(v___x_1056_, v___x_1055_);
v___x_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_x_932_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1059_, 0, v_x_932_);
lean_ctor_set(v___x_1059_, 1, v___x_991_);
lean_ctor_set(v___x_1059_, 2, v___x_1058_);
v___x_1060_ = lean_array_push(v_items_990_, v___x_1059_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 5, v___x_1060_);
lean_ctor_set(v___x_1046_, 4, v___x_991_);
lean_ctor_set(v___x_1046_, 3, v___x_991_);
lean_ctor_set(v___x_1046_, 2, v___x_1053_);
lean_ctor_set(v___x_1046_, 1, v___x_1052_);
lean_ctor_set(v___x_1046_, 0, v___x_1051_);
v___x_1062_ = v___x_1046_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1069_, 5, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1064_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_1062_);
lean_ctor_set(v___x_979_, 0, v___x_1048_);
v___x_1064_ = v___x_979_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_1064_);
v___x_1066_ = v___x_984_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_del_object(v___x_979_);
lean_dec(v_snd_977_);
lean_dec(v_fst_976_);
lean_dec(v_tailKey_972_);
lean_dec_ref_known(v___x_945_, 3);
lean_dec(v_x_932_);
v_a_1078_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_981_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_981_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
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
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v_tailKey_972_);
lean_dec_ref_known(v___x_945_, 3);
lean_dec(v_x_932_);
v_a_1087_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_974_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_974_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
v___jp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_948_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_949_ = l_Lean_MessageData_ofName(v___y_947_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_952_, v___x_945_, v_a_935_);
lean_dec_ref_known(v___x_945_, 3);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
return v_res_1114_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1118_);
v___x_1124_ = l_Lean_Syntax_isOfKind(v_x_1118_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_1118_);
v___x_1126_ = l_Lean_Syntax_isOfKind(v_x_1118_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1118_);
v___x_1128_ = l_Lean_Syntax_isOfKind(v_x_1118_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1130_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1118_, v___x_1129_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec_ref(v_a_1119_);
lean_dec(v_x_1118_);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; 
v___x_1131_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v___x_1131_;
}
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v___x_1132_;
}
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1141_, lean_object* v_as_1142_, size_t v_i_1143_, size_t v_stop_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v___y_1147_; uint8_t v___x_1151_; 
v___x_1151_ = lean_usize_dec_eq(v_i_1143_, v_stop_1144_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v_fst_1153_; lean_object* v_snd_1154_; lean_object* v___x_1155_; 
v___x_1152_ = lean_array_uget_borrowed(v_as_1142_, v_i_1143_);
v_fst_1153_ = lean_ctor_get(v___x_1152_, 0);
v_snd_1154_ = lean_ctor_get(v___x_1152_, 1);
lean_inc(v_fst_1153_);
v___x_1155_ = l_Lean_Name_components(v_fst_1153_);
if (lean_obj_tag(v___x_1155_) == 0)
{
v___y_1147_ = v_b_1145_;
goto v___jp_1146_;
}
else
{
lean_object* v_head_1156_; lean_object* v_tail_1157_; lean_object* v___x_1158_; 
v_head_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_head_1156_);
v_tail_1157_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_tail_1157_);
lean_dec_ref_known(v___x_1155_, 2);
lean_inc(v_snd_1154_);
lean_inc(v_ref_1141_);
v___x_1158_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1145_, v_ref_1141_, v_head_1156_, v_tail_1157_, v_snd_1154_);
v___y_1147_ = v___x_1158_;
goto v___jp_1146_;
}
}
else
{
lean_dec(v_ref_1141_);
return v_b_1145_;
}
v___jp_1146_:
{
size_t v___x_1148_; size_t v___x_1149_; 
v___x_1148_ = ((size_t)1ULL);
v___x_1149_ = lean_usize_add(v_i_1143_, v___x_1148_);
v_i_1143_ = v___x_1149_;
v_b_1145_ = v___y_1147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1159_, size_t v_i_1160_, lean_object* v_bs_1161_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_usize_dec_lt(v_i_1160_, v_sz_1159_);
if (v___x_1162_ == 0)
{
return v_bs_1161_;
}
else
{
lean_object* v_v_1163_; lean_object* v___x_1164_; lean_object* v_bs_x27_1165_; lean_object* v___x_1166_; size_t v___x_1167_; size_t v___x_1168_; lean_object* v___x_1169_; 
v_v_1163_ = lean_array_uget(v_bs_1161_, v_i_1160_);
v___x_1164_ = lean_unsigned_to_nat(0u);
v_bs_x27_1165_ = lean_array_uset(v_bs_1161_, v_i_1160_, v___x_1164_);
v___x_1166_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1163_);
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_add(v_i_1160_, v___x_1167_);
v___x_1169_ = lean_array_uset(v_bs_x27_1165_, v_i_1160_, v___x_1166_);
v_i_1160_ = v___x_1168_;
v_bs_1161_ = v___x_1169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1171_){
_start:
{
switch(lean_obj_tag(v_a_1171_))
{
case 6:
{
lean_object* v_xs_1172_; lean_object* v_ref_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1201_; 
v_xs_1172_ = lean_ctor_get(v_a_1171_, 1);
v_ref_1173_ = lean_ctor_get(v_a_1171_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_a_1171_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1175_ = v_a_1171_;
v_isShared_1176_ = v_isSharedCheck_1201_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_xs_1172_);
lean_inc(v_ref_1173_);
lean_dec(v_a_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1201_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_items_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_items_1177_ = lean_ctor_get(v_xs_1172_, 0);
lean_inc_ref(v_items_1177_);
lean_dec_ref(v_xs_1172_);
v___x_1178_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_array_get_size(v_items_1177_);
v___x_1181_ = lean_nat_dec_lt(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1183_; 
lean_dec_ref(v_items_1177_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1178_);
v___x_1183_ = v___x_1175_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_ref_1173_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
else
{
uint8_t v___x_1185_; 
v___x_1185_ = lean_nat_dec_le(v___x_1180_, v___x_1180_);
if (v___x_1185_ == 0)
{
if (v___x_1181_ == 0)
{
lean_object* v___x_1187_; 
lean_dec_ref(v_items_1177_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1178_);
v___x_1187_ = v___x_1175_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_ref_1173_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1178_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
else
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = lean_usize_of_nat(v___x_1180_);
lean_inc(v_ref_1173_);
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1173_, v_items_1177_, v___x_1189_, v___x_1190_, v___x_1178_);
lean_dec_ref(v_items_1177_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1191_);
v___x_1193_ = v___x_1175_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_ref_1173_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
else
{
size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = lean_usize_of_nat(v___x_1180_);
lean_inc(v_ref_1173_);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1173_, v_items_1177_, v___x_1195_, v___x_1196_, v___x_1178_);
lean_dec_ref(v_items_1177_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1197_);
v___x_1199_ = v___x_1175_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_ref_1173_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
case 5:
{
lean_object* v_ref_1202_; lean_object* v_xs_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1213_; 
v_ref_1202_ = lean_ctor_get(v_a_1171_, 0);
v_xs_1203_ = lean_ctor_get(v_a_1171_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_a_1171_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1205_ = v_a_1171_;
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_xs_1203_);
lean_inc(v_ref_1202_);
lean_dec(v_a_1171_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
size_t v_sz_1207_; size_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v_sz_1207_ = lean_array_size(v_xs_1203_);
v___x_1208_ = ((size_t)0ULL);
v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1207_, v___x_1208_, v_xs_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___x_1209_);
v___x_1211_ = v___x_1205_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_ref_1202_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
default: 
{
return v_a_1171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1214_, lean_object* v___x_1215_, lean_object* v_v_x3f_1216_){
_start:
{
if (lean_obj_tag(v_v_x3f_1216_) == 1)
{
lean_object* v_val_1217_; 
v_val_1217_ = lean_ctor_get(v_v_x3f_1216_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v_v_x3f_1216_, 1);
switch(lean_obj_tag(v_val_1217_))
{
case 6:
{
lean_object* v_ref_1218_; lean_object* v_xs_1219_; lean_object* v___x_1220_; 
v_ref_1218_ = lean_ctor_get(v_val_1217_, 0);
lean_inc(v_ref_1218_);
v_xs_1219_ = lean_ctor_get(v_val_1217_, 1);
lean_inc_ref(v_xs_1219_);
lean_dec_ref_known(v_val_1217_, 2);
v___x_1220_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1214_);
if (lean_obj_tag(v___x_1220_) == 6)
{
lean_object* v_xs_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1230_; 
v_xs_1221_ = lean_ctor_get(v___x_1220_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1220_, 0);
lean_dec(v_unused_1231_);
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_xs_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_items_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v_items_1225_ = lean_ctor_get(v_xs_1221_, 0);
lean_inc_ref(v_items_1225_);
lean_dec_ref(v_xs_1221_);
v___x_1226_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1215_, v_xs_1219_, v_items_1225_);
lean_dec_ref(v_items_1225_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1226_);
lean_ctor_set(v___x_1223_, 0, v_ref_1218_);
v___x_1228_ = v___x_1223_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_ref_1218_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_dec_ref(v_xs_1219_);
lean_dec(v_ref_1218_);
lean_dec_ref(v___x_1215_);
return v___x_1220_;
}
}
case 5:
{
lean_object* v_ref_1232_; lean_object* v_xs_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v___x_1215_);
v_ref_1232_ = lean_ctor_get(v_val_1217_, 0);
v_xs_1233_ = lean_ctor_get(v_val_1217_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_val_1217_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1235_ = v_val_1217_;
v_isShared_1236_ = v_isSharedCheck_1252_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_xs_1233_);
lean_inc(v_ref_1232_);
lean_dec(v_val_1217_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1252_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; 
v___x_1237_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1214_);
if (lean_obj_tag(v___x_1237_) == 5)
{
lean_object* v_xs_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1246_; 
lean_del_object(v___x_1235_);
v_xs_1238_ = lean_ctor_get(v___x_1237_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1237_, 0);
lean_dec(v_unused_1247_);
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_xs_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = l_Array_append___redArg(v_xs_1233_, v_xs_1238_);
lean_dec_ref(v_xs_1238_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 1, v___x_1242_);
lean_ctor_set(v___x_1240_, 0, v_ref_1232_);
v___x_1244_ = v___x_1240_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_ref_1232_);
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
else
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_array_push(v_xs_1233_, v___x_1237_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1248_);
v___x_1250_ = v___x_1235_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_ref_1232_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
default: 
{
lean_object* v___x_1253_; 
lean_dec(v_val_1217_);
lean_dec_ref(v___x_1215_);
v___x_1253_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1214_);
return v___x_1253_;
}
}
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_v_x3f_1216_);
lean_dec_ref(v___x_1215_);
v___x_1254_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1214_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1255_, lean_object* v_k_1256_, lean_object* v_t_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1257_);
lean_inc(v_k_1256_);
v___x_1259_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1258_, v_k_1256_, v_t_1257_);
if (lean_obj_tag(v___x_1259_) == 1)
{
lean_object* v_val_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_k_1256_);
v_val_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1295_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_val_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1295_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_items_1264_; lean_object* v_indices_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1294_; 
v_items_1264_ = lean_ctor_get(v_t_1257_, 0);
v_indices_1265_ = lean_ctor_get(v_t_1257_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_t_1257_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1267_ = v_t_1257_;
v_isShared_1268_ = v_isSharedCheck_1294_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_indices_1265_);
lean_inc(v_items_1264_);
lean_dec(v_t_1257_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1294_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_array_get_size(v_items_1264_);
v___x_1270_ = lean_nat_dec_lt(v_val_1260_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1272_; 
lean_del_object(v___x_1262_);
lean_dec(v_val_1260_);
lean_dec_ref(v_newV_1255_);
if (v_isShared_1268_ == 0)
{
v___x_1272_ = v___x_1267_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_items_1264_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_indices_1265_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
else
{
lean_object* v_v_1274_; lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1293_; 
v_v_1274_ = lean_array_fget(v_items_1264_, v_val_1260_);
v_fst_1275_ = lean_ctor_get(v_v_1274_, 0);
v_snd_1276_ = lean_ctor_get(v_v_1274_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_v_1274_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1278_ = v_v_1274_;
v_isShared_1279_ = v_isSharedCheck_1293_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_snd_1276_);
lean_inc(v_fst_1275_);
lean_dec(v_v_1274_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1293_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v_xs_x27_1281_; lean_object* v___x_1283_; 
v___x_1280_ = lean_box(0);
v_xs_x27_1281_ = lean_array_fset(v_items_1264_, v_val_1260_, v___x_1280_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v_snd_1276_);
v___x_1283_ = v___x_1262_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_snd_1276_);
v___x_1283_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1255_, v___x_1258_, v___x_1283_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___x_1284_);
v___x_1286_ = v___x_1278_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_fst_1275_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_array_fset(v_xs_x27_1281_, v_val_1260_, v___x_1286_);
lean_dec(v_val_1260_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1287_);
v___x_1289_ = v___x_1267_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_indices_1265_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
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
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec(v___x_1259_);
v___x_1296_ = lean_box(0);
v___x_1297_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1255_, v___x_1258_, v___x_1296_);
v___x_1298_ = l_Lake_Toml_RBDict_push___redArg(v___x_1258_, v_k_1256_, v___x_1297_, v_t_1257_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1299_, lean_object* v_head_1300_, lean_object* v_tail_1301_, lean_object* v_newV_1302_, lean_object* v_v_x3f_1303_){
_start:
{
if (lean_obj_tag(v_v_x3f_1303_) == 1)
{
lean_object* v_val_1304_; 
v_val_1304_ = lean_ctor_get(v_v_x3f_1303_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v_v_x3f_1303_, 1);
switch(lean_obj_tag(v_val_1304_))
{
case 5:
{
lean_object* v_ref_1305_; lean_object* v_xs_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_ref_1305_ = lean_ctor_get(v_val_1304_, 0);
v_xs_1306_ = lean_ctor_get(v_val_1304_, 1);
v___x_1307_ = lean_array_get_size(v_xs_1306_);
v___x_1308_ = lean_unsigned_to_nat(1u);
v___x_1309_ = lean_nat_sub(v___x_1307_, v___x_1308_);
v___x_1310_ = lean_nat_dec_lt(v___x_1309_, v___x_1307_);
if (v___x_1310_ == 0)
{
lean_dec(v___x_1309_);
lean_dec_ref(v_newV_1302_);
lean_dec(v_tail_1301_);
lean_dec(v_head_1300_);
lean_dec(v_kRef_1299_);
return v_val_1304_;
}
else
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1335_; 
lean_inc_ref(v_xs_1306_);
lean_inc(v_ref_1305_);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_val_1304_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; lean_object* v_unused_1337_; 
v_unused_1336_ = lean_ctor_get(v_val_1304_, 1);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_val_1304_, 0);
lean_dec(v_unused_1337_);
v___x_1312_ = v_val_1304_;
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v_val_1304_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_v_1314_; lean_object* v___x_1315_; lean_object* v_xs_x27_1316_; lean_object* v___y_1318_; 
v_v_1314_ = lean_array_fget(v_xs_1306_, v___x_1309_);
v___x_1315_ = lean_box(0);
v_xs_x27_1316_ = lean_array_fset(v_xs_1306_, v___x_1309_, v___x_1315_);
if (lean_obj_tag(v_v_1314_) == 6)
{
lean_object* v_ref_1323_; lean_object* v_xs_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1332_; 
v_ref_1323_ = lean_ctor_get(v_v_1314_, 0);
v_xs_1324_ = lean_ctor_get(v_v_1314_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_v_1314_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1326_ = v_v_1314_;
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_xs_1324_);
lean_inc(v_ref_1323_);
lean_dec(v_v_1314_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1324_, v_kRef_1299_, v_head_1300_, v_tail_1301_, v_newV_1302_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v___x_1328_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_ref_1323_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
v___y_1318_ = v___x_1330_;
goto v___jp_1317_;
}
}
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec(v_v_1314_);
lean_dec_ref(v_newV_1302_);
lean_dec(v_tail_1301_);
lean_dec(v_head_1300_);
v___x_1333_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1334_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_kRef_1299_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___y_1318_ = v___x_1334_;
goto v___jp_1317_;
}
v___jp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_array_fset(v_xs_x27_1316_, v___x_1309_, v___y_1318_);
lean_dec(v___x_1309_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___x_1319_);
v___x_1321_ = v___x_1312_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_ref_1305_);
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
}
case 6:
{
lean_object* v_ref_1338_; lean_object* v_xs_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_ref_1338_ = lean_ctor_get(v_val_1304_, 0);
v_xs_1339_ = lean_ctor_get(v_val_1304_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_val_1304_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1341_ = v_val_1304_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_xs_1339_);
lean_inc(v_ref_1338_);
lean_dec(v_val_1304_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1339_, v_kRef_1299_, v_head_1300_, v_tail_1301_, v_newV_1302_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_ref_1338_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
default: 
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_val_1304_);
v___x_1348_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1299_);
v___x_1349_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1348_, v_kRef_1299_, v_head_1300_, v_tail_1301_, v_newV_1302_);
v___x_1350_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_kRef_1299_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
return v___x_1350_;
}
}
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec(v_v_x3f_1303_);
v___x_1351_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1299_);
v___x_1352_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1351_, v_kRef_1299_, v_head_1300_, v_tail_1301_, v_newV_1302_);
v___x_1353_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_kRef_1299_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1354_, lean_object* v_head_1355_, lean_object* v_tail_1356_, lean_object* v_newV_1357_, lean_object* v_k_1358_, lean_object* v_t_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1359_);
lean_inc(v_k_1358_);
v___x_1361_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1360_, v_k_1358_, v_t_1359_);
if (lean_obj_tag(v___x_1361_) == 1)
{
lean_object* v_val_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_k_1358_);
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1397_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_val_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1397_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_items_1366_; lean_object* v_indices_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1396_; 
v_items_1366_ = lean_ctor_get(v_t_1359_, 0);
v_indices_1367_ = lean_ctor_get(v_t_1359_, 1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_t_1359_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1369_ = v_t_1359_;
v_isShared_1370_ = v_isSharedCheck_1396_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_indices_1367_);
lean_inc(v_items_1366_);
lean_dec(v_t_1359_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1396_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = lean_array_get_size(v_items_1366_);
v___x_1372_ = lean_nat_dec_lt(v_val_1362_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1374_; 
lean_del_object(v___x_1364_);
lean_dec(v_val_1362_);
lean_dec_ref(v_newV_1357_);
lean_dec(v_tail_1356_);
lean_dec(v_head_1355_);
lean_dec(v_kRef_1354_);
if (v_isShared_1370_ == 0)
{
v___x_1374_ = v___x_1369_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_items_1366_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_indices_1367_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
else
{
lean_object* v_v_1376_; lean_object* v_fst_1377_; lean_object* v_snd_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1395_; 
v_v_1376_ = lean_array_fget(v_items_1366_, v_val_1362_);
v_fst_1377_ = lean_ctor_get(v_v_1376_, 0);
v_snd_1378_ = lean_ctor_get(v_v_1376_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_v_1376_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1380_ = v_v_1376_;
v_isShared_1381_ = v_isSharedCheck_1395_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_snd_1378_);
lean_inc(v_fst_1377_);
lean_dec(v_v_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1395_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v_xs_x27_1383_; lean_object* v___x_1385_; 
v___x_1382_ = lean_box(0);
v_xs_x27_1383_ = lean_array_fset(v_items_1366_, v_val_1362_, v___x_1382_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v_snd_1378_);
v___x_1385_ = v___x_1364_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_snd_1378_);
v___x_1385_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1354_, v_head_1355_, v_tail_1356_, v_newV_1357_, v___x_1385_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1386_);
v___x_1388_ = v___x_1380_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_fst_1377_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = lean_array_fset(v_xs_x27_1383_, v_val_1362_, v___x_1388_);
lean_dec(v_val_1362_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1389_);
v___x_1391_ = v___x_1369_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_indices_1367_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
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
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec(v___x_1361_);
v___x_1398_ = lean_box(0);
v___x_1399_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1354_, v_head_1355_, v_tail_1356_, v_newV_1357_, v___x_1398_);
v___x_1400_ = l_Lake_Toml_RBDict_push___redArg(v___x_1360_, v_k_1358_, v___x_1399_, v_t_1359_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1401_, lean_object* v_kRef_1402_, lean_object* v_k_1403_, lean_object* v_ks_1404_, lean_object* v_newV_1405_){
_start:
{
if (lean_obj_tag(v_ks_1404_) == 0)
{
lean_object* v___x_1406_; 
lean_dec(v_kRef_1402_);
v___x_1406_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1405_, v_k_1403_, v_t_1401_);
return v___x_1406_;
}
else
{
lean_object* v_head_1407_; lean_object* v_tail_1408_; lean_object* v___x_1409_; 
v_head_1407_ = lean_ctor_get(v_ks_1404_, 0);
lean_inc(v_head_1407_);
v_tail_1408_ = lean_ctor_get(v_ks_1404_, 1);
lean_inc(v_tail_1408_);
lean_dec_ref_known(v_ks_1404_, 2);
v___x_1409_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1402_, v_head_1407_, v_tail_1408_, v_newV_1405_, v_k_1403_, v_t_1401_);
return v___x_1409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1410_, lean_object* v_i_1411_, lean_object* v_bs_1412_){
_start:
{
size_t v_sz_boxed_1413_; size_t v_i_boxed_1414_; lean_object* v_res_1415_; 
v_sz_boxed_1413_ = lean_unbox_usize(v_sz_1410_);
lean_dec(v_sz_1410_);
v_i_boxed_1414_ = lean_unbox_usize(v_i_1411_);
lean_dec(v_i_1411_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1413_, v_i_boxed_1414_, v_bs_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1416_, lean_object* v_as_1417_, lean_object* v_i_1418_, lean_object* v_stop_1419_, lean_object* v_b_1420_){
_start:
{
size_t v_i_boxed_1421_; size_t v_stop_boxed_1422_; lean_object* v_res_1423_; 
v_i_boxed_1421_ = lean_unbox_usize(v_i_1418_);
lean_dec(v_i_1418_);
v_stop_boxed_1422_ = lean_unbox_usize(v_stop_1419_);
lean_dec(v_stop_1419_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1416_, v_as_1417_, v_i_boxed_1421_, v_stop_boxed_1422_, v_b_1420_);
lean_dec_ref(v_as_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1424_, size_t v_i_1425_, size_t v_stop_1426_, lean_object* v_b_1427_){
_start:
{
lean_object* v___y_1429_; uint8_t v___x_1433_; 
v___x_1433_ = lean_usize_dec_eq(v_i_1425_, v_stop_1426_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v_ref_1435_; lean_object* v_key_1436_; lean_object* v_val_1437_; lean_object* v___x_1438_; 
v___x_1434_ = lean_array_uget_borrowed(v_as_1424_, v_i_1425_);
v_ref_1435_ = lean_ctor_get(v___x_1434_, 0);
v_key_1436_ = lean_ctor_get(v___x_1434_, 1);
v_val_1437_ = lean_ctor_get(v___x_1434_, 2);
lean_inc(v_key_1436_);
v___x_1438_ = l_Lean_Name_components(v_key_1436_);
if (lean_obj_tag(v___x_1438_) == 0)
{
v___y_1429_ = v_b_1427_;
goto v___jp_1428_;
}
else
{
lean_object* v_head_1439_; lean_object* v_tail_1440_; lean_object* v___x_1441_; 
v_head_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_head_1439_);
v_tail_1440_ = lean_ctor_get(v___x_1438_, 1);
lean_inc(v_tail_1440_);
lean_dec_ref_known(v___x_1438_, 2);
lean_inc_ref(v_val_1437_);
lean_inc(v_ref_1435_);
v___x_1441_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1427_, v_ref_1435_, v_head_1439_, v_tail_1440_, v_val_1437_);
v___y_1429_ = v___x_1441_;
goto v___jp_1428_;
}
}
else
{
return v_b_1427_;
}
v___jp_1428_:
{
size_t v___x_1430_; size_t v___x_1431_; 
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_add(v_i_1425_, v___x_1430_);
v_i_1425_ = v___x_1431_;
v_b_1427_ = v___y_1429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1442_, lean_object* v_i_1443_, lean_object* v_stop_1444_, lean_object* v_b_1445_){
_start:
{
size_t v_i_boxed_1446_; size_t v_stop_boxed_1447_; lean_object* v_res_1448_; 
v_i_boxed_1446_ = lean_unbox_usize(v_i_1443_);
lean_dec(v_i_1443_);
v_stop_boxed_1447_ = lean_unbox_usize(v_stop_1444_);
lean_dec(v_stop_1444_);
v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1442_, v_i_boxed_1446_, v_stop_boxed_1447_, v_b_1445_);
lean_dec_ref(v_as_1442_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1449_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1450_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = lean_array_get_size(v_items_1449_);
v___x_1453_ = lean_nat_dec_lt(v___x_1451_, v___x_1452_);
if (v___x_1453_ == 0)
{
return v___x_1450_;
}
else
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_nat_dec_le(v___x_1452_, v___x_1452_);
if (v___x_1454_ == 0)
{
if (v___x_1453_ == 0)
{
return v___x_1450_;
}
else
{
size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = ((size_t)0ULL);
v___x_1456_ = lean_usize_of_nat(v___x_1452_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1449_, v___x_1455_, v___x_1456_, v___x_1450_);
return v___x_1457_;
}
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1452_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1449_, v___x_1458_, v___x_1459_, v___x_1450_);
return v___x_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1461_);
lean_dec_ref(v_items_1461_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1465_);
lean_inc_ref(v_a_1464_);
v___x_1468_ = lean_apply_4(v_x_1463_, v___x_1467_, v_a_1464_, v_a_1465_, lean_box(0));
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1479_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_snd_1473_; lean_object* v_items_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v_snd_1473_ = lean_ctor_get(v_a_1469_, 1);
lean_inc(v_snd_1473_);
lean_dec(v_a_1469_);
v_items_1474_ = lean_ctor_get(v_snd_1473_, 5);
lean_inc_ref(v_items_1474_);
lean_dec(v_snd_1473_);
v___x_1475_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1474_);
lean_dec_ref(v_items_1474_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1475_);
v___x_1477_ = v___x_1471_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1468_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1468_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1501_, uint8_t v___y_1502_, lean_object* v_x_1503_){
_start:
{
if (lean_obj_tag(v_x_1503_) == 1)
{
lean_object* v_pre_1504_; 
v_pre_1504_ = lean_ctor_get(v_x_1503_, 0);
switch(lean_obj_tag(v_pre_1504_))
{
case 1:
{
lean_object* v_pre_1505_; 
v_pre_1505_ = lean_ctor_get(v_pre_1504_, 0);
switch(lean_obj_tag(v_pre_1505_))
{
case 0:
{
lean_object* v_str_1506_; lean_object* v_str_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_str_1506_ = lean_ctor_get(v_x_1503_, 1);
v_str_1507_ = lean_ctor_get(v_pre_1504_, 1);
v___x_1508_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1509_ = lean_string_dec_eq(v_str_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1511_ = lean_string_dec_eq(v_str_1507_, v___x_1510_);
if (v___x_1511_ == 0)
{
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1513_ = lean_string_dec_eq(v_str_1506_, v___x_1512_);
if (v___x_1513_ == 0)
{
return v___x_1513_;
}
else
{
return v_suppressElabErrors_1501_;
}
}
}
else
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1515_ = lean_string_dec_eq(v_str_1506_, v___x_1514_);
if (v___x_1515_ == 0)
{
return v___x_1515_;
}
else
{
return v_suppressElabErrors_1501_;
}
}
}
case 1:
{
lean_object* v_pre_1516_; 
v_pre_1516_ = lean_ctor_get(v_pre_1505_, 0);
if (lean_obj_tag(v_pre_1516_) == 0)
{
lean_object* v_str_1517_; lean_object* v_str_1518_; lean_object* v_str_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_str_1517_ = lean_ctor_get(v_x_1503_, 1);
v_str_1518_ = lean_ctor_get(v_pre_1504_, 1);
v_str_1519_ = lean_ctor_get(v_pre_1505_, 1);
v___x_1520_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1521_ = lean_string_dec_eq(v_str_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1523_ = lean_string_dec_eq(v_str_1518_, v___x_1522_);
if (v___x_1523_ == 0)
{
return v___x_1523_;
}
else
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1525_ = lean_string_dec_eq(v_str_1517_, v___x_1524_);
if (v___x_1525_ == 0)
{
return v___x_1525_;
}
else
{
return v_suppressElabErrors_1501_;
}
}
}
}
else
{
return v___y_1502_;
}
}
default: 
{
return v___y_1502_;
}
}
}
case 0:
{
lean_object* v_str_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_str_1526_ = lean_ctor_get(v_x_1503_, 1);
v___x_1527_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1528_ = lean_string_dec_eq(v_str_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
return v___x_1528_;
}
else
{
return v_suppressElabErrors_1501_;
}
}
default: 
{
return v___y_1502_;
}
}
}
else
{
return v___y_1502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1529_, lean_object* v___y_1530_, lean_object* v_x_1531_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1532_; uint8_t v___y_10662__boxed_1533_; uint8_t v_res_1534_; lean_object* v_r_1535_; 
v_suppressElabErrors_boxed_1532_ = lean_unbox(v_suppressElabErrors_1529_);
v___y_10662__boxed_1533_ = lean_unbox(v___y_1530_);
v_res_1534_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1532_, v___y_10662__boxed_1533_, v_x_1531_);
lean_dec(v_x_1531_);
v_r_1535_ = lean_box(v_res_1534_);
return v_r_1535_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1536_, lean_object* v_opt_1537_){
_start:
{
lean_object* v_name_1538_; lean_object* v_defValue_1539_; lean_object* v_map_1540_; lean_object* v___x_1541_; 
v_name_1538_ = lean_ctor_get(v_opt_1537_, 0);
v_defValue_1539_ = lean_ctor_get(v_opt_1537_, 1);
v_map_1540_ = lean_ctor_get(v_opts_1536_, 0);
v___x_1541_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1540_, v_name_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_unbox(v_defValue_1539_);
return v___x_1542_;
}
else
{
lean_object* v_val_1543_; 
v_val_1543_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v___x_1541_, 1);
if (lean_obj_tag(v_val_1543_) == 1)
{
uint8_t v_v_1544_; 
v_v_1544_ = lean_ctor_get_uint8(v_val_1543_, 0);
lean_dec_ref_known(v_val_1543_, 0);
return v_v_1544_;
}
else
{
uint8_t v___x_1545_; 
lean_dec(v_val_1543_);
v___x_1545_ = lean_unbox(v_defValue_1539_);
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1546_, lean_object* v_opt_1547_){
_start:
{
uint8_t v_res_1548_; lean_object* v_r_1549_; 
v_res_1548_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1546_, v_opt_1547_);
lean_dec_ref(v_opt_1547_);
lean_dec_ref(v_opts_1546_);
v_r_1549_ = lean_box(v_res_1548_);
return v_r_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1551_, lean_object* v_msgData_1552_, uint8_t v_severity_1553_, uint8_t v_isSilent_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_a_1560_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; uint8_t v___y_1567_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v_currNamespace_1571_; lean_object* v_openDecls_1572_; lean_object* v___y_1573_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; uint8_t v___y_1603_; uint8_t v___y_1604_; lean_object* v___y_1605_; uint8_t v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; uint8_t v___y_1629_; uint8_t v___y_1630_; lean_object* v___y_1631_; uint8_t v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; uint8_t v___y_1642_; lean_object* v___y_1643_; uint8_t v___y_1644_; uint8_t v___y_1645_; uint8_t v___x_1650_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; uint8_t v___y_1658_; uint8_t v___y_1659_; uint8_t v___y_1660_; uint8_t v___y_1662_; uint8_t v___x_1681_; 
v___x_1650_ = 2;
v___x_1681_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1553_, v___x_1650_);
if (v___x_1681_ == 0)
{
v___y_1662_ = v___x_1681_;
goto v___jp_1661_;
}
else
{
uint8_t v___x_1682_; 
lean_inc_ref(v_msgData_1552_);
v___x_1682_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1552_);
v___y_1662_ = v___x_1682_;
goto v___jp_1661_;
}
v___jp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_a_1560_);
lean_ctor_set(v___x_1561_, 1, v___y_1555_);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
v___jp_1563_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v_env_1578_; lean_object* v_nextMacroScope_1579_; lean_object* v_ngen_1580_; lean_object* v_auxDeclNGen_1581_; lean_object* v_traceState_1582_; lean_object* v_cache_1583_; lean_object* v_messages_1584_; lean_object* v_infoState_1585_; lean_object* v_snapshotTasks_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1596_; 
lean_inc(v_openDecls_1572_);
lean_inc(v_currNamespace_1571_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_currNamespace_1571_);
lean_ctor_set(v___x_1574_, 1, v_openDecls_1572_);
v___x_1575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v___y_1564_);
lean_inc_ref(v___y_1569_);
lean_inc_ref(v___y_1570_);
v___x_1576_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1576_, 0, v___y_1570_);
lean_ctor_set(v___x_1576_, 1, v___y_1565_);
lean_ctor_set(v___x_1576_, 2, v___y_1566_);
lean_ctor_set(v___x_1576_, 3, v___y_1569_);
lean_ctor_set(v___x_1576_, 4, v___x_1575_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*5, v___y_1568_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*5 + 1, v___y_1567_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*5 + 2, v_isSilent_1554_);
v___x_1577_ = lean_st_ref_take(v___y_1573_);
v_env_1578_ = lean_ctor_get(v___x_1577_, 0);
v_nextMacroScope_1579_ = lean_ctor_get(v___x_1577_, 1);
v_ngen_1580_ = lean_ctor_get(v___x_1577_, 2);
v_auxDeclNGen_1581_ = lean_ctor_get(v___x_1577_, 3);
v_traceState_1582_ = lean_ctor_get(v___x_1577_, 4);
v_cache_1583_ = lean_ctor_get(v___x_1577_, 5);
v_messages_1584_ = lean_ctor_get(v___x_1577_, 6);
v_infoState_1585_ = lean_ctor_get(v___x_1577_, 7);
v_snapshotTasks_1586_ = lean_ctor_get(v___x_1577_, 8);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1588_ = v___x_1577_;
v_isShared_1589_ = v_isSharedCheck_1596_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_snapshotTasks_1586_);
lean_inc(v_infoState_1585_);
lean_inc(v_messages_1584_);
lean_inc(v_cache_1583_);
lean_inc(v_traceState_1582_);
lean_inc(v_auxDeclNGen_1581_);
lean_inc(v_ngen_1580_);
lean_inc(v_nextMacroScope_1579_);
lean_inc(v_env_1578_);
lean_dec(v___x_1577_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1596_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = lean_box(0);
v___x_1591_ = l_Lean_MessageLog_add(v___x_1576_, v_messages_1584_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 6, v___x_1591_);
v___x_1593_ = v___x_1588_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_env_1578_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_nextMacroScope_1579_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_ngen_1580_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_auxDeclNGen_1581_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_traceState_1582_);
lean_ctor_set(v_reuseFailAlloc_1595_, 5, v_cache_1583_);
lean_ctor_set(v_reuseFailAlloc_1595_, 6, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1595_, 7, v_infoState_1585_);
lean_ctor_set(v_reuseFailAlloc_1595_, 8, v_snapshotTasks_1586_);
v___x_1593_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_st_ref_put(v___y_1573_, v___x_1593_);
v_a_1560_ = v___x_1590_;
goto v___jp_1559_;
}
}
}
v___jp_1597_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1622_; 
v___x_1608_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1552_);
v___x_1609_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1608_, v___y_1556_, v___y_1557_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1622_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1622_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
lean_inc_ref_n(v___y_1601_, 2);
v___x_1614_ = l_Lean_FileMap_toPosition(v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
v___x_1615_ = l_Lean_FileMap_toPosition(v___y_1601_, v___y_1607_);
lean_dec(v___y_1607_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set_tag(v___x_1612_, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1615_);
v___x_1617_ = v___x_1612_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; 
v___x_1618_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1606_ == 0)
{
lean_dec_ref(v___y_1598_);
v___y_1564_ = v_a_1610_;
v___y_1565_ = v___x_1614_;
v___y_1566_ = v___x_1617_;
v___y_1567_ = v___y_1604_;
v___y_1568_ = v___y_1603_;
v___y_1569_ = v___x_1618_;
v___y_1570_ = v___y_1605_;
v_currNamespace_1571_ = v___y_1599_;
v_openDecls_1572_ = v___y_1600_;
v___y_1573_ = v___y_1557_;
goto v___jp_1563_;
}
else
{
uint8_t v___x_1619_; 
lean_inc(v_a_1610_);
v___x_1619_ = l_Lean_MessageData_hasTag(v___y_1598_, v_a_1610_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec_ref(v___x_1617_);
lean_dec_ref(v___x_1614_);
lean_dec(v_a_1610_);
v___x_1620_ = lean_box(0);
v_a_1560_ = v___x_1620_;
goto v___jp_1559_;
}
else
{
v___y_1564_ = v_a_1610_;
v___y_1565_ = v___x_1614_;
v___y_1566_ = v___x_1617_;
v___y_1567_ = v___y_1604_;
v___y_1568_ = v___y_1603_;
v___y_1569_ = v___x_1618_;
v___y_1570_ = v___y_1605_;
v_currNamespace_1571_ = v___y_1599_;
v_openDecls_1572_ = v___y_1600_;
v___y_1573_ = v___y_1557_;
goto v___jp_1563_;
}
}
}
}
}
v___jp_1623_:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Syntax_getTailPos_x3f(v___y_1627_, v___y_1630_);
lean_dec(v___y_1627_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_inc(v___y_1633_);
v___y_1598_ = v___y_1624_;
v___y_1599_ = v___y_1625_;
v___y_1600_ = v___y_1626_;
v___y_1601_ = v___y_1628_;
v___y_1602_ = v___y_1633_;
v___y_1603_ = v___y_1630_;
v___y_1604_ = v___y_1629_;
v___y_1605_ = v___y_1631_;
v___y_1606_ = v___y_1632_;
v___y_1607_ = v___y_1633_;
goto v___jp_1597_;
}
else
{
lean_object* v_val_1635_; 
v_val_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_val_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v___y_1598_ = v___y_1624_;
v___y_1599_ = v___y_1625_;
v___y_1600_ = v___y_1626_;
v___y_1601_ = v___y_1628_;
v___y_1602_ = v___y_1633_;
v___y_1603_ = v___y_1630_;
v___y_1604_ = v___y_1629_;
v___y_1605_ = v___y_1631_;
v___y_1606_ = v___y_1632_;
v___y_1607_ = v_val_1635_;
goto v___jp_1597_;
}
}
v___jp_1636_:
{
lean_object* v_ref_1646_; lean_object* v___x_1647_; 
v_ref_1646_ = l_Lean_replaceRef(v_ref_1551_, v___y_1641_);
v___x_1647_ = l_Lean_Syntax_getPos_x3f(v_ref_1646_, v___y_1642_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___y_1624_ = v___y_1637_;
v___y_1625_ = v___y_1638_;
v___y_1626_ = v___y_1639_;
v___y_1627_ = v_ref_1646_;
v___y_1628_ = v___y_1640_;
v___y_1629_ = v___y_1645_;
v___y_1630_ = v___y_1642_;
v___y_1631_ = v___y_1643_;
v___y_1632_ = v___y_1644_;
v___y_1633_ = v___x_1648_;
goto v___jp_1623_;
}
else
{
lean_object* v_val_1649_; 
v_val_1649_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_val_1649_);
lean_dec_ref_known(v___x_1647_, 1);
v___y_1624_ = v___y_1637_;
v___y_1625_ = v___y_1638_;
v___y_1626_ = v___y_1639_;
v___y_1627_ = v_ref_1646_;
v___y_1628_ = v___y_1640_;
v___y_1629_ = v___y_1645_;
v___y_1630_ = v___y_1642_;
v___y_1631_ = v___y_1643_;
v___y_1632_ = v___y_1644_;
v___y_1633_ = v_val_1649_;
goto v___jp_1623_;
}
}
v___jp_1651_:
{
if (v___y_1660_ == 0)
{
v___y_1637_ = v___y_1653_;
v___y_1638_ = v___y_1654_;
v___y_1639_ = v___y_1656_;
v___y_1640_ = v___y_1652_;
v___y_1641_ = v___y_1657_;
v___y_1642_ = v___y_1658_;
v___y_1643_ = v___y_1655_;
v___y_1644_ = v___y_1659_;
v___y_1645_ = v_severity_1553_;
goto v___jp_1636_;
}
else
{
v___y_1637_ = v___y_1653_;
v___y_1638_ = v___y_1654_;
v___y_1639_ = v___y_1656_;
v___y_1640_ = v___y_1652_;
v___y_1641_ = v___y_1657_;
v___y_1642_ = v___y_1658_;
v___y_1643_ = v___y_1655_;
v___y_1644_ = v___y_1659_;
v___y_1645_ = v___x_1650_;
goto v___jp_1636_;
}
}
v___jp_1661_:
{
if (v___y_1662_ == 0)
{
lean_object* v_toCold_1663_; lean_object* v_ref_1664_; uint8_t v_suppressElabErrors_1665_; lean_object* v_fileName_1666_; lean_object* v_fileMap_1667_; lean_object* v_options_1668_; lean_object* v_currNamespace_1669_; lean_object* v_openDecls_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___f_1673_; uint8_t v___x_1674_; uint8_t v___x_1675_; 
v_toCold_1663_ = lean_ctor_get(v___y_1556_, 0);
v_ref_1664_ = lean_ctor_get(v___y_1556_, 2);
v_suppressElabErrors_1665_ = lean_ctor_get_uint8(v___y_1556_, sizeof(void*)*3 + 1);
v_fileName_1666_ = lean_ctor_get(v_toCold_1663_, 0);
v_fileMap_1667_ = lean_ctor_get(v_toCold_1663_, 1);
v_options_1668_ = lean_ctor_get(v_toCold_1663_, 2);
v_currNamespace_1669_ = lean_ctor_get(v_toCold_1663_, 4);
v_openDecls_1670_ = lean_ctor_get(v_toCold_1663_, 5);
v___x_1671_ = lean_box(v_suppressElabErrors_1665_);
v___x_1672_ = lean_box(v___y_1662_);
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1673_, 0, v___x_1671_);
lean_closure_set(v___f_1673_, 1, v___x_1672_);
v___x_1674_ = 1;
v___x_1675_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1553_, v___x_1674_);
if (v___x_1675_ == 0)
{
v___y_1652_ = v_fileMap_1667_;
v___y_1653_ = v___f_1673_;
v___y_1654_ = v_currNamespace_1669_;
v___y_1655_ = v_fileName_1666_;
v___y_1656_ = v_openDecls_1670_;
v___y_1657_ = v_ref_1664_;
v___y_1658_ = v___y_1662_;
v___y_1659_ = v_suppressElabErrors_1665_;
v___y_1660_ = v___x_1675_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = l_Lean_warningAsError;
v___x_1677_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_options_1668_, v___x_1676_);
v___y_1652_ = v_fileMap_1667_;
v___y_1653_ = v___f_1673_;
v___y_1654_ = v_currNamespace_1669_;
v___y_1655_ = v_fileName_1666_;
v___y_1656_ = v_openDecls_1670_;
v___y_1657_ = v_ref_1664_;
v___y_1658_ = v___y_1662_;
v___y_1659_ = v_suppressElabErrors_1665_;
v___y_1660_ = v___x_1677_;
goto v___jp_1651_;
}
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec_ref(v_msgData_1552_);
v___x_1678_ = lean_box(0);
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v___y_1555_);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1683_, lean_object* v_msgData_1684_, lean_object* v_severity_1685_, lean_object* v_isSilent_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v_severity_boxed_1691_; uint8_t v_isSilent_boxed_1692_; lean_object* v_res_1693_; 
v_severity_boxed_1691_ = lean_unbox(v_severity_1685_);
v_isSilent_boxed_1692_ = lean_unbox(v_isSilent_1686_);
v_res_1693_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1683_, v_msgData_1684_, v_severity_boxed_1691_, v_isSilent_boxed_1692_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v_ref_1683_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1694_, lean_object* v_msgData_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
uint8_t v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = 2;
v___x_1701_ = 0;
v___x_1702_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1694_, v_msgData_1695_, v___x_1700_, v___x_1701_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1703_, lean_object* v_msgData_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1703_, v_msgData_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v_ref_1703_);
return v_res_1709_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1713_ = l_Lean_MessageData_ofFormat(v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1714_, lean_object* v_as_1715_, size_t v_sz_1716_, size_t v_i_1717_, uint8_t v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_snd_1724_; lean_object* v_snd_1725_; lean_object* v___y_1731_; uint8_t v___y_1732_; lean_object* v_a_1749_; uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_lt(v_i_1717_, v_sz_1716_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_box(v_b_1718_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v___y_1719_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1757_; uint8_t v_recovering_1758_; 
v_a_1756_ = lean_array_uget_borrowed(v_as_1715_, v_i_1717_);
v___x_1757_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1756_);
v_recovering_1758_ = l_Lean_Syntax_isOfKind(v_a_1756_, v___x_1757_);
if (v_recovering_1758_ == 0)
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_a_1756_);
v___x_1760_ = l_Lean_Syntax_isOfKind(v_a_1756_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1756_);
v___x_1762_ = l_Lean_Syntax_isOfKind(v_a_1756_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1719_);
v___x_1764_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1756_, v___x_1763_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v_snd_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v___y_1719_);
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v_snd_1766_ = lean_ctor_get(v_a_1765_, 1);
lean_inc(v_snd_1766_);
lean_dec(v_a_1765_);
v___x_1767_ = lean_box(v_b_1718_);
v_snd_1724_ = v___x_1767_;
v_snd_1725_ = v_snd_1766_;
goto v___jp_1723_;
}
else
{
lean_object* v_a_1768_; 
v_a_1768_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1764_, 1);
v_a_1749_ = v_a_1768_;
goto v___jp_1748_;
}
}
else
{
lean_object* v___x_1769_; 
lean_inc_ref(v___y_1719_);
lean_inc(v_a_1756_);
v___x_1769_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1756_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v_snd_1771_; lean_object* v___x_1772_; 
lean_dec_ref(v___y_1719_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v_snd_1771_ = lean_ctor_get(v_a_1770_, 1);
lean_inc(v_snd_1771_);
lean_dec(v_a_1770_);
v___x_1772_ = lean_box(v_recovering_1758_);
v_snd_1724_ = v___x_1772_;
v_snd_1725_ = v_snd_1771_;
goto v___jp_1723_;
}
else
{
lean_object* v_a_1773_; 
v_a_1773_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1769_, 1);
v_a_1749_ = v_a_1773_;
goto v___jp_1748_;
}
}
}
else
{
lean_object* v___x_1774_; 
lean_inc_ref(v___y_1719_);
lean_inc(v_a_1756_);
v___x_1774_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1756_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v_snd_1776_; lean_object* v___x_1777_; 
lean_dec_ref(v___y_1719_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v_snd_1776_ = lean_ctor_get(v_a_1775_, 1);
lean_inc(v_snd_1776_);
lean_dec(v_a_1775_);
v___x_1777_ = lean_box(v_recovering_1758_);
v_snd_1724_ = v___x_1777_;
v_snd_1725_ = v_snd_1776_;
goto v___jp_1723_;
}
else
{
lean_object* v_a_1778_; 
v_a_1778_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1774_, 1);
v_a_1749_ = v_a_1778_;
goto v___jp_1748_;
}
}
}
else
{
if (v_b_1718_ == 0)
{
lean_object* v___x_1779_; 
lean_inc_ref(v___y_1719_);
lean_inc(v_a_1756_);
v___x_1779_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1756_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v_snd_1781_; lean_object* v___x_1782_; 
lean_dec_ref(v___y_1719_);
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v_snd_1781_ = lean_ctor_get(v_a_1780_, 1);
lean_inc(v_snd_1781_);
lean_dec(v_a_1780_);
v___x_1782_ = lean_box(v_b_1718_);
v_snd_1724_ = v___x_1782_;
v_snd_1725_ = v_snd_1781_;
goto v___jp_1723_;
}
else
{
lean_object* v_a_1783_; 
v_a_1783_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1779_, 1);
v_a_1749_ = v_a_1783_;
goto v___jp_1748_;
}
}
else
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_box(v_b_1718_);
v_snd_1724_ = v___x_1784_;
v_snd_1725_ = v___y_1719_;
goto v___jp_1723_;
}
}
}
v___jp_1723_:
{
size_t v___x_1726_; size_t v___x_1727_; uint8_t v___x_1728_; 
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_add(v_i_1717_, v___x_1726_);
v___x_1728_ = lean_unbox(v_snd_1724_);
lean_dec(v_snd_1724_);
v_i_1717_ = v___x_1727_;
v_b_1718_ = v___x_1728_;
v___y_1719_ = v_snd_1725_;
goto _start;
}
v___jp_1730_:
{
if (v___y_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = l_Lean_Exception_getRef(v___y_1731_);
v___x_1734_ = l_Lean_Exception_toMessageData(v___y_1731_);
v___x_1735_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1733_, v___x_1734_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___x_1733_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v_snd_1737_; lean_object* v___x_1738_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v_snd_1737_ = lean_ctor_get(v_a_1736_, 1);
lean_inc(v_snd_1737_);
lean_dec(v_a_1736_);
v___x_1738_ = lean_box(v_recovering_1714_);
v_snd_1724_ = v___x_1738_;
v_snd_1725_ = v_snd_1737_;
goto v___jp_1723_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1735_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1735_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v___x_1747_; 
lean_dec_ref(v___y_1719_);
v___x_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___y_1731_);
return v___x_1747_;
}
}
v___jp_1748_:
{
uint8_t v___x_1750_; 
v___x_1750_ = l_Lean_Exception_isInterrupt(v_a_1749_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; 
lean_inc_ref(v_a_1749_);
v___x_1751_ = l_Lean_Exception_isRuntime(v_a_1749_);
v___y_1731_ = v_a_1749_;
v___y_1732_ = v___x_1751_;
goto v___jp_1730_;
}
else
{
v___y_1731_ = v_a_1749_;
v___y_1732_ = v___x_1750_;
goto v___jp_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1785_, lean_object* v_as_1786_, lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
uint8_t v_recovering_boxed_1794_; size_t v_sz_boxed_1795_; size_t v_i_boxed_1796_; uint8_t v_b_boxed_1797_; lean_object* v_res_1798_; 
v_recovering_boxed_1794_ = lean_unbox(v_recovering_1785_);
v_sz_boxed_1795_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1796_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v_b_boxed_1797_ = lean_unbox(v_b_1789_);
v_res_1798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1794_, v_as_1786_, v_sz_boxed_1795_, v_i_boxed_1796_, v_b_boxed_1797_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v_as_1786_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_ref_1803_; lean_object* v___x_1804_; lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1813_; 
v_ref_1803_ = lean_ctor_get(v___y_1800_, 2);
v___x_1804_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1799_, v___y_1800_, v___y_1801_);
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1813_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1813_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
lean_inc(v_ref_1803_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_ref_1803_);
lean_ctor_set(v___x_1809_, 1, v_a_1805_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 1);
lean_ctor_set(v___x_1807_, 0, v___x_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1819_, lean_object* v_msg_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_toCold_1824_; lean_object* v_currRecDepth_1825_; lean_object* v_ref_1826_; uint8_t v_diag_1827_; uint8_t v_suppressElabErrors_1828_; lean_object* v_ref_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_toCold_1824_ = lean_ctor_get(v___y_1821_, 0);
v_currRecDepth_1825_ = lean_ctor_get(v___y_1821_, 1);
v_ref_1826_ = lean_ctor_get(v___y_1821_, 2);
v_diag_1827_ = lean_ctor_get_uint8(v___y_1821_, sizeof(void*)*3);
v_suppressElabErrors_1828_ = lean_ctor_get_uint8(v___y_1821_, sizeof(void*)*3 + 1);
v_ref_1829_ = l_Lean_replaceRef(v_ref_1819_, v_ref_1826_);
lean_inc(v_currRecDepth_1825_);
lean_inc_ref(v_toCold_1824_);
v___x_1830_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1830_, 0, v_toCold_1824_);
lean_ctor_set(v___x_1830_, 1, v_currRecDepth_1825_);
lean_ctor_set(v___x_1830_, 2, v_ref_1829_);
lean_ctor_set_uint8(v___x_1830_, sizeof(void*)*3, v_diag_1827_);
lean_ctor_set_uint8(v___x_1830_, sizeof(void*)*3 + 1, v_suppressElabErrors_1828_);
v___x_1831_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1820_, v___x_1830_, v___y_1822_);
lean_dec_ref_known(v___x_1830_, 3);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1832_, lean_object* v_msg_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1832_, v_msg_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v_ref_1832_);
return v_res_1837_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1850_);
v___x_1855_ = l_Lean_Syntax_isOfKind(v_x_1850_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1857_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1850_, v___x_1856_, v_a_1851_, v_a_1852_);
lean_dec(v_x_1850_);
return v___x_1857_;
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v_recovering_1861_; 
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = l_Lean_Syntax_getArg(v_x_1850_, v___x_1858_);
v___x_1860_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1861_ = l_Lean_Syntax_isOfKind(v___x_1859_, v___x_1860_);
if (v_recovering_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1863_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1850_, v___x_1862_, v_a_1851_, v_a_1852_);
lean_dec(v_x_1850_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v_xs_1866_; uint8_t v_recovering_1867_; lean_object* v___x_1868_; size_t v_sz_1869_; size_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1864_ = lean_unsigned_to_nat(1u);
v___x_1865_ = l_Lean_Syntax_getArg(v_x_1850_, v___x_1864_);
lean_dec(v_x_1850_);
v_xs_1866_ = l_Lean_Syntax_getArgs(v___x_1865_);
lean_dec(v___x_1865_);
v_recovering_1867_ = 0;
v___x_1868_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1866_);
lean_dec_ref(v_xs_1866_);
v_sz_1869_ = lean_array_size(v___x_1868_);
v___x_1870_ = ((size_t)0ULL);
v___x_1871_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1861_, v___x_1868_, v_sz_1869_, v___x_1870_, v_recovering_1867_, v___x_1871_, v_a_1851_, v_a_1852_);
lean_dec_ref(v___x_1868_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1883_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1883_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1883_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_snd_1877_; lean_object* v_items_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v_snd_1877_ = lean_ctor_get(v_a_1873_, 1);
lean_inc(v_snd_1877_);
lean_dec(v_a_1873_);
v_items_1878_ = lean_ctor_get(v_snd_1877_, 5);
lean_inc_ref(v_items_1878_);
lean_dec(v_snd_1877_);
v___x_1879_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1878_);
lean_dec_ref(v_items_1878_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1879_);
v___x_1881_ = v___x_1875_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
v_a_1884_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1872_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1872_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lake_Toml_elabToml(v_x_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1897_, lean_object* v_ref_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1898_, v_msg_1899_, v___y_1900_, v___y_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1904_, lean_object* v_ref_1905_, lean_object* v_msg_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1904_, v_ref_1905_, v_msg_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_ref_1905_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1911_, lean_object* v_msg_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1912_, v___y_1913_, v___y_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1917_, lean_object* v_msg_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1917_, v_msg_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1922_;
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
