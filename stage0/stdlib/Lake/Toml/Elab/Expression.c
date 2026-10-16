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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_126_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
lean_ctor_set(v___x_128_, 2, v___x_127_);
lean_ctor_set(v___x_128_, 3, v___x_127_);
lean_ctor_set(v___x_128_, 4, v___x_126_);
lean_ctor_set(v___x_128_, 5, v___x_126_);
lean_ctor_set(v___x_128_, 6, v___x_126_);
lean_ctor_set(v___x_128_, 7, v___x_126_);
lean_ctor_set(v___x_128_, 8, v___x_126_);
lean_ctor_set(v___x_128_, 9, v___x_126_);
lean_ctor_set(v___x_128_, 10, v___x_126_);
lean_ctor_set(v___x_128_, 11, v___x_125_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_unsigned_to_nat(32u);
v___x_130_ = lean_mk_empty_array_with_capacity(v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_132_ = ((size_t)5ULL);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_unsigned_to_nat(32u);
v___x_135_ = lean_mk_empty_array_with_capacity(v___x_134_);
v___x_136_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3);
v___x_137_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
lean_ctor_set(v___x_137_, 2, v___x_133_);
lean_ctor_set(v___x_137_, 3, v___x_133_);
lean_ctor_set_usize(v___x_137_, 4, v___x_132_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_138_ = lean_box(1);
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4);
v___x_140_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
lean_ctor_set(v___x_141_, 2, v___x_138_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(lean_object* v_msgData_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; lean_object* v_toCold_147_; lean_object* v_env_148_; lean_object* v_options_149_; uint8_t v___x_150_; lean_object* v_env_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_146_ = lean_st_ref_get(v___y_144_);
v_toCold_147_ = lean_ctor_get(v___y_143_, 0);
v_env_148_ = lean_ctor_get(v___x_146_, 0);
lean_inc_ref(v_env_148_);
lean_dec(v___x_146_);
v_options_149_ = lean_ctor_get(v_toCold_147_, 2);
v___x_150_ = 0;
v_env_151_ = l_Lean_Environment_setRecordingDeps(v_env_148_, v___x_150_);
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2);
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_149_);
v___x_154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_154_, 0, v_env_151_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
lean_ctor_set(v___x_154_, 2, v___x_153_);
lean_ctor_set(v___x_154_, 3, v_options_149_);
v___x_155_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_msgData_142_);
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
size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_314_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_307_, v___x_318_, v___x_319_, v_currKey_312_, v_a_308_, v_a_309_, v_a_310_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object* v_ks_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec_ref(v_ks_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_327_, lean_object* v_ref_328_, lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_328_, v_msg_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_335_, lean_object* v_ref_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_335_, v_ref_336_, v_msg_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v_ref_336_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_344_, v___y_346_, v___y_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_350_, lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_350_, v_msg_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_357_, lean_object* v_as_358_, size_t v_i_359_, size_t v_stop_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___y_363_; uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_eq(v_i_359_, v_stop_360_);
if (v___x_367_ == 0)
{
lean_object* v_fst_368_; uint8_t v___x_369_; 
v_fst_368_ = lean_ctor_get(v_b_361_, 0);
v___x_369_ = lean_unbox(v_fst_368_);
if (v___x_369_ == 0)
{
lean_object* v_snd_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v_snd_370_ = lean_ctor_get(v_b_361_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_b_361_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v_b_361_, 0);
lean_dec(v_unused_379_);
v___x_372_ = v_b_361_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_snd_370_);
lean_dec(v_b_361_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_box(v___x_357_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_snd_370_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v___y_363_ = v___x_376_;
goto v___jp_362_;
}
}
}
else
{
lean_object* v_snd_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_390_; 
v_snd_380_ = lean_ctor_get(v_b_361_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_b_361_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v_b_361_, 0);
lean_dec(v_unused_391_);
v___x_382_ = v_b_361_;
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_snd_380_);
lean_dec(v_b_361_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_384_ = lean_array_uget_borrowed(v_as_358_, v_i_359_);
lean_inc(v___x_384_);
v___x_385_ = lean_array_push(v_snd_380_, v___x_384_);
v___x_386_ = lean_box(v___x_367_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v___x_385_);
lean_ctor_set(v___x_382_, 0, v___x_386_);
v___x_388_ = v___x_382_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_385_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v___y_363_ = v___x_388_;
goto v___jp_362_;
}
}
}
}
else
{
return v_b_361_;
}
v___jp_362_:
{
size_t v___x_364_; size_t v___x_365_; 
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_359_, v___x_364_);
v_i_359_ = v___x_365_;
v_b_361_ = v___y_363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_392_, lean_object* v_as_393_, lean_object* v_i_394_, lean_object* v_stop_395_, lean_object* v_b_396_){
_start:
{
uint8_t v___x_2936__boxed_397_; size_t v_i_boxed_398_; size_t v_stop_boxed_399_; lean_object* v_res_400_; 
v___x_2936__boxed_397_ = lean_unbox(v___x_392_);
v_i_boxed_398_ = lean_unbox_usize(v_i_394_);
lean_dec(v_i_394_);
v_stop_boxed_399_ = lean_unbox_usize(v_stop_395_);
lean_dec(v_stop_395_);
v_res_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2936__boxed_397_, v_as_393_, v_i_boxed_398_, v_stop_boxed_399_, v_b_396_);
lean_dec_ref(v_as_393_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_408_, size_t v_i_409_, lean_object* v_bs_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_lt(v_i_409_, v_sz_408_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v_bs_410_);
return v___x_412_;
}
else
{
lean_object* v_v_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_v_413_ = lean_array_uget(v_bs_410_, v_i_409_);
v___x_414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_413_);
v___x_415_ = l_Lean_Syntax_isOfKind(v_v_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
lean_dec(v_v_413_);
lean_dec_ref(v_bs_410_);
v___x_416_ = lean_box(0);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v_bs_x27_418_; size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v_bs_x27_418_ = lean_array_uset(v_bs_410_, v_i_409_, v___x_417_);
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_add(v_i_409_, v___x_419_);
v___x_421_ = lean_array_uset(v_bs_x27_418_, v_i_409_, v_v_413_);
v_i_409_ = v___x_420_;
v_bs_410_ = v___x_421_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_423_, lean_object* v_i_424_, lean_object* v_bs_425_){
_start:
{
size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v_sz_boxed_426_ = lean_unbox_usize(v_sz_423_);
lean_dec(v_sz_423_);
v_i_boxed_427_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_426_, v_i_boxed_427_, v_bs_425_);
return v_res_428_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_447_);
v___x_453_ = l_Lean_Syntax_isOfKind(v_kv_447_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_455_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_447_, v___x_454_, v_a_448_, v_a_449_, v_a_450_);
lean_dec_ref(v_a_448_);
lean_dec(v_kv_447_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = l_Lean_Syntax_getArg(v_kv_447_, v___x_456_);
v___x_458_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_457_);
v___x_459_ = l_Lean_Syntax_isOfKind(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v_kv_447_);
v___x_460_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_461_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_457_, v___x_460_, v_a_448_, v_a_449_, v_a_450_);
lean_dec_ref(v_a_448_);
lean_dec(v___x_457_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v_v_463_; lean_object* v___y_465_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_462_ = lean_unsigned_to_nat(2u);
v_v_463_ = l_Lean_Syntax_getArg(v_kv_447_, v___x_462_);
lean_dec(v_kv_447_);
v___x_571_ = l_Lean_Syntax_getArg(v___x_457_, v___x_456_);
v___x_572_ = l_Lean_Syntax_getArgs(v___x_571_);
lean_dec(v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_574_ = lean_array_get_size(v___x_572_);
v___x_575_ = lean_nat_dec_lt(v___x_456_, v___x_574_);
if (v___x_575_ == 0)
{
lean_dec_ref(v___x_572_);
v___y_465_ = v___x_573_;
goto v___jp_464_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; lean_object* v_snd_581_; 
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_573_);
v___x_578_ = ((size_t)0ULL);
v___x_579_ = lean_usize_of_nat(v___x_574_);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_459_, v___x_572_, v___x_578_, v___x_579_, v___x_577_);
lean_dec_ref(v___x_572_);
v_snd_581_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_snd_581_);
lean_dec_ref(v___x_580_);
v___y_465_ = v_snd_581_;
goto v___jp_464_;
}
v___jp_464_:
{
size_t v_sz_466_; size_t v___x_467_; lean_object* v___x_468_; 
v_sz_466_ = lean_array_size(v___y_465_);
v___x_467_ = ((size_t)0ULL);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_466_, v___x_467_, v___y_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_v_463_);
v___x_469_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_470_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_457_, v___x_469_, v_a_448_, v_a_449_, v_a_450_);
lean_dec_ref(v_a_448_);
lean_dec(v___x_457_);
return v___x_470_;
}
else
{
lean_object* v_val_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_tailKeyStx_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_val_471_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_468_, 1);
v___x_472_ = lean_box(0);
v___x_473_ = lean_array_get_size(v_val_471_);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_sub(v___x_473_, v___x_474_);
v_tailKeyStx_476_ = lean_array_get(v___x_472_, v_val_471_, v___x_475_);
lean_dec(v___x_475_);
v___x_477_ = lean_array_pop(v_val_471_);
v___x_478_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_477_, v_a_448_, v_a_449_, v_a_450_);
lean_dec_ref(v___x_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_562_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v_fst_480_ = lean_ctor_get(v_a_479_, 0);
v_snd_481_ = lean_ctor_get(v_a_479_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_562_ == 0)
{
v___x_483_ = v_a_479_;
v_isShared_484_ = v_isSharedCheck_562_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_snd_481_);
lean_inc(v_fst_480_);
lean_dec(v_a_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_562_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; 
lean_inc(v_tailKeyStx_476_);
v___x_485_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_476_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v_keyTys_487_; lean_object* v_arrKeyTys_488_; lean_object* v_arrParents_489_; lean_object* v_currArrKey_490_; lean_object* v_currKey_491_; lean_object* v_items_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v_keyTys_487_ = lean_ctor_get(v_snd_481_, 0);
v_arrKeyTys_488_ = lean_ctor_get(v_snd_481_, 1);
v_arrParents_489_ = lean_ctor_get(v_snd_481_, 2);
v_currArrKey_490_ = lean_ctor_get(v_snd_481_, 3);
v_currKey_491_ = lean_ctor_get(v_snd_481_, 4);
v_items_492_ = lean_ctor_get(v_snd_481_, 5);
v___x_493_ = l_Lean_Name_str___override(v_fst_480_, v_a_486_);
v___x_494_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_487_, v___x_493_);
if (lean_obj_tag(v___x_494_) == 1)
{
lean_object* v_val_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_514_; 
lean_del_object(v___x_483_);
lean_dec(v_v_463_);
lean_dec(v___x_457_);
v_val_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_514_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_val_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_499_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_500_ = lean_unbox(v_val_495_);
lean_dec(v_val_495_);
v___x_501_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_500_);
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 3);
lean_ctor_set(v___x_497_, 0, v___x_501_);
v___x_503_ = v___x_497_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_513_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_504_ = l_Lean_MessageData_ofFormat(v___x_503_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_499_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = l_Lean_MessageData_ofName(v___x_493_);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_476_, v___x_511_, v_snd_481_, v_a_449_, v_a_450_);
lean_dec(v_snd_481_);
lean_dec(v_tailKeyStx_476_);
return v___x_512_;
}
}
}
else
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_547_; 
lean_inc_ref(v_items_492_);
lean_inc(v_currKey_491_);
lean_inc(v_currArrKey_490_);
lean_inc(v_arrParents_489_);
lean_inc(v_arrKeyTys_488_);
lean_inc(v_keyTys_487_);
lean_dec(v___x_494_);
lean_dec(v_tailKeyStx_476_);
v_isSharedCheck_547_ = !lean_is_exclusive(v_snd_481_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; lean_object* v_unused_552_; lean_object* v_unused_553_; 
v_unused_548_ = lean_ctor_get(v_snd_481_, 5);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_snd_481_, 4);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_snd_481_, 3);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_snd_481_, 2);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_snd_481_, 1);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_snd_481_, 0);
lean_dec(v_unused_553_);
v___x_516_ = v_snd_481_;
v_isShared_517_ = v_isSharedCheck_547_;
goto v_resetjp_515_;
}
else
{
lean_dec(v_snd_481_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_547_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lake_Toml_elabVal(v_v_463_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_538_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_538_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_523_ = lean_box(0);
v___x_524_ = 0;
v___x_525_ = lean_box(v___x_524_);
lean_inc(v___x_493_);
v___x_526_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_493_, v___x_525_, v_keyTys_487_);
v___x_527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_527_, 0, v___x_457_);
lean_ctor_set(v___x_527_, 1, v___x_493_);
lean_ctor_set(v___x_527_, 2, v_a_519_);
v___x_528_ = lean_array_push(v_items_492_, v___x_527_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 5, v___x_528_);
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_530_ = v___x_516_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_arrKeyTys_488_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_arrParents_489_);
lean_ctor_set(v_reuseFailAlloc_537_, 3, v_currArrKey_490_);
lean_ctor_set(v_reuseFailAlloc_537_, 4, v_currKey_491_);
lean_ctor_set(v_reuseFailAlloc_537_, 5, v___x_528_);
v___x_530_ = v_reuseFailAlloc_537_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_530_);
lean_ctor_set(v___x_483_, 0, v___x_523_);
v___x_532_ = v___x_483_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_536_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_532_);
v___x_534_ = v___x_521_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_del_object(v___x_516_);
lean_dec(v___x_493_);
lean_dec_ref(v_items_492_);
lean_dec(v_currKey_491_);
lean_dec(v_currArrKey_490_);
lean_dec(v_arrParents_489_);
lean_dec(v_arrKeyTys_488_);
lean_dec(v_keyTys_487_);
lean_del_object(v___x_483_);
lean_dec(v___x_457_);
v_a_539_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_518_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_518_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_del_object(v___x_483_);
lean_dec(v_snd_481_);
lean_dec(v_fst_480_);
lean_dec(v_tailKeyStx_476_);
lean_dec(v_v_463_);
lean_dec(v___x_457_);
v_a_554_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_485_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_485_);
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
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_tailKeyStx_476_);
lean_dec(v_v_463_);
lean_dec(v___x_457_);
v_a_563_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_478_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_478_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
return v_res_587_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_591_, size_t v_i_592_, size_t v_stop_593_, lean_object* v_b_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_fst_600_; lean_object* v_snd_601_; uint8_t v___x_605_; 
v___x_605_ = lean_usize_dec_eq(v_i_592_, v_stop_593_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_array_uget_borrowed(v_as_591_, v_i_592_);
lean_inc(v___x_606_);
v___x_607_ = l_Lake_Toml_elabSimpleKey(v___x_606_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v_keyTys_609_; lean_object* v_arrKeyTys_610_; lean_object* v_arrParents_611_; lean_object* v_currArrKey_612_; lean_object* v_currKey_613_; lean_object* v_items_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v_keyTys_609_ = lean_ctor_get(v___y_595_, 0);
v_arrKeyTys_610_ = lean_ctor_get(v___y_595_, 1);
v_arrParents_611_ = lean_ctor_get(v___y_595_, 2);
v_currArrKey_612_ = lean_ctor_get(v___y_595_, 3);
v_currKey_613_ = lean_ctor_get(v___y_595_, 4);
v_items_614_ = lean_ctor_get(v___y_595_, 5);
v___x_615_ = l_Lean_Name_str___override(v_b_594_, v_a_608_);
v___x_616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_609_, v___x_615_);
if (lean_obj_tag(v___x_616_) == 1)
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_678_; 
v_val_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_678_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_678_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_678_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint8_t v___x_621_; 
v___x_621_ = lean_unbox(v_val_617_);
switch(v___x_621_)
{
case 2:
{
lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_646_; 
lean_inc_ref(v_items_614_);
lean_inc(v_currKey_613_);
lean_inc(v_arrParents_611_);
lean_inc(v_arrKeyTys_610_);
lean_del_object(v___x_619_);
lean_dec(v_val_617_);
v_isSharedCheck_646_ = !lean_is_exclusive(v___y_595_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; lean_object* v_unused_648_; lean_object* v_unused_649_; lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_647_ = lean_ctor_get(v___y_595_, 5);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v___y_595_, 4);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v___y_595_, 3);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v___y_595_, 2);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v___y_595_, 1);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v___y_595_, 0);
lean_dec(v_unused_652_);
v___x_623_ = v___y_595_;
v_isShared_624_ = v_isSharedCheck_646_;
goto v_resetjp_622_;
}
else
{
lean_dec(v___y_595_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_646_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_610_, v___x_615_);
if (lean_obj_tag(v___x_625_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_628_; 
v_val_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v___x_625_, 1);
lean_inc(v___x_615_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 3, v___x_615_);
lean_ctor_set(v___x_623_, 0, v_val_626_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_val_626_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_arrKeyTys_610_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_arrParents_611_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v_currKey_613_);
lean_ctor_set(v_reuseFailAlloc_629_, 5, v_items_614_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_fst_600_ = v___x_615_;
v_snd_601_ = v___x_628_;
goto v___jp_599_;
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v___x_625_);
lean_del_object(v___x_623_);
lean_dec_ref(v_items_614_);
lean_dec(v_currKey_613_);
lean_dec(v_arrParents_611_);
lean_dec(v_arrKeyTys_610_);
v___x_630_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_615_);
v___x_631_ = l_Lean_MessageData_ofName(v___x_615_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_634_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v_snd_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v_snd_637_ = lean_ctor_get(v_a_636_, 1);
lean_inc(v_snd_637_);
lean_dec(v_a_636_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v_snd_637_;
goto v___jp_599_;
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v___x_615_);
v_a_638_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_635_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_635_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
}
case 1:
{
lean_del_object(v___x_619_);
lean_dec(v_val_617_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v___y_595_;
goto v___jp_599_;
}
case 4:
{
lean_del_object(v___x_619_);
lean_dec(v_val_617_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v___y_595_;
goto v___jp_599_;
}
case 3:
{
lean_del_object(v___x_619_);
lean_dec(v_val_617_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v___y_595_;
goto v___jp_599_;
}
default: 
{
lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_654_ = lean_unbox(v_val_617_);
lean_dec(v_val_617_);
v___x_655_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_654_);
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 3);
lean_ctor_set(v___x_619_, 0, v___x_655_);
v___x_657_ = v___x_619_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_677_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_658_ = l_Lean_MessageData_ofFormat(v___x_657_);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_653_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
lean_inc(v___x_615_);
v___x_662_ = l_Lean_MessageData_ofName(v___x_615_);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_606_, v___x_665_, v___y_595_, v___y_596_, v___y_597_);
lean_dec_ref(v___y_595_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v_snd_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v_snd_668_ = lean_ctor_get(v_a_667_, 1);
lean_inc(v_snd_668_);
lean_dec(v_a_667_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v_snd_668_;
goto v___jp_599_;
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v___x_615_);
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
}
}
else
{
lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_688_; 
lean_inc_ref(v_items_614_);
lean_inc(v_currKey_613_);
lean_inc(v_currArrKey_612_);
lean_inc(v_arrParents_611_);
lean_inc(v_arrKeyTys_610_);
lean_inc(v_keyTys_609_);
lean_dec(v___x_616_);
v_isSharedCheck_688_ = !lean_is_exclusive(v___y_595_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; lean_object* v_unused_692_; lean_object* v_unused_693_; lean_object* v_unused_694_; 
v_unused_689_ = lean_ctor_get(v___y_595_, 5);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v___y_595_, 4);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v___y_595_, 3);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v___y_595_, 2);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v___y_595_, 1);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v___y_595_, 0);
lean_dec(v_unused_694_);
v___x_680_ = v___y_595_;
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
else
{
lean_dec(v___y_595_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_682_ = 4;
v___x_683_ = lean_box(v___x_682_);
lean_inc(v___x_615_);
v___x_684_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_615_, v___x_683_, v_keyTys_609_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_684_);
v___x_686_ = v___x_680_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_arrKeyTys_610_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_arrParents_611_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_currArrKey_612_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_currKey_613_);
lean_ctor_set(v_reuseFailAlloc_687_, 5, v_items_614_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v_fst_600_ = v___x_615_;
v_snd_601_ = v___x_686_;
goto v___jp_599_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v___y_595_);
lean_dec(v_b_594_);
v_a_695_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_607_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_607_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_b_594_);
lean_ctor_set(v___x_703_, 1, v___y_595_);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
v___jp_599_:
{
size_t v___x_602_; size_t v___x_603_; 
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_592_, v___x_602_);
v_i_592_ = v___x_603_;
v_b_594_ = v_fst_600_;
v___y_595_ = v_snd_601_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_705_, lean_object* v_i_706_, lean_object* v_stop_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
size_t v_i_boxed_713_; size_t v_stop_boxed_714_; lean_object* v_res_715_; 
v_i_boxed_713_ = lean_unbox_usize(v_i_706_);
lean_dec(v_i_706_);
v_stop_boxed_714_ = lean_unbox_usize(v_stop_707_);
lean_dec(v_stop_707_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_705_, v_i_boxed_713_, v_stop_boxed_714_, v_b_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_as_705_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_716_, lean_object* v_k_717_){
_start:
{
if (lean_obj_tag(v_t_716_) == 0)
{
lean_object* v_k_718_; lean_object* v_v_719_; lean_object* v_l_720_; lean_object* v_r_721_; uint8_t v___x_722_; 
v_k_718_ = lean_ctor_get(v_t_716_, 1);
v_v_719_ = lean_ctor_get(v_t_716_, 2);
v_l_720_ = lean_ctor_get(v_t_716_, 3);
v_r_721_ = lean_ctor_get(v_t_716_, 4);
v___x_722_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_717_, v_k_718_);
switch(v___x_722_)
{
case 0:
{
v_t_716_ = v_l_720_;
goto _start;
}
case 1:
{
lean_object* v___x_724_; 
lean_inc(v_v_719_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_v_719_);
return v___x_724_;
}
default: 
{
v_t_716_ = v_r_721_;
goto _start;
}
}
}
else
{
lean_object* v___x_726_; 
v___x_726_ = lean_box(0);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_727_, lean_object* v_k_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_727_, v_k_728_);
lean_dec(v_k_728_);
lean_dec(v_t_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_keyTys_735_; lean_object* v_arrKeyTys_736_; lean_object* v_arrParents_737_; lean_object* v_currArrKey_738_; lean_object* v_currKey_739_; lean_object* v_items_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_762_; 
v_keyTys_735_ = lean_ctor_get(v_a_731_, 0);
v_arrKeyTys_736_ = lean_ctor_get(v_a_731_, 1);
v_arrParents_737_ = lean_ctor_get(v_a_731_, 2);
v_currArrKey_738_ = lean_ctor_get(v_a_731_, 3);
v_currKey_739_ = lean_ctor_get(v_a_731_, 4);
v_items_740_ = lean_ctor_get(v_a_731_, 5);
v_isSharedCheck_762_ = !lean_is_exclusive(v_a_731_);
if (v_isSharedCheck_762_ == 0)
{
v___x_742_ = v_a_731_;
v_isShared_743_ = v_isSharedCheck_762_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_items_740_);
lean_inc(v_currKey_739_);
lean_inc(v_currArrKey_738_);
lean_inc(v_arrParents_737_);
lean_inc(v_arrKeyTys_736_);
lean_inc(v_keyTys_735_);
lean_dec(v_a_731_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_762_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_arrKeyTys_744_; lean_object* v___x_745_; lean_object* v___y_747_; lean_object* v___x_759_; 
v_arrKeyTys_744_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_738_, v_keyTys_735_, v_arrKeyTys_736_);
v___x_745_ = lean_box(0);
v___x_759_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_744_, v___x_745_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; 
v___x_760_ = lean_box(1);
v___y_747_ = v___x_760_;
goto v___jp_746_;
}
else
{
lean_object* v_val_761_; 
v_val_761_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v___x_759_, 1);
v___y_747_ = v_val_761_;
goto v___jp_746_;
}
v___jp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 3, v___x_745_);
lean_ctor_set(v___x_742_, 1, v_arrKeyTys_744_);
lean_ctor_set(v___x_742_, 0, v___y_747_);
v___x_749_ = v___x_742_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___y_747_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_arrKeyTys_744_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_arrParents_737_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_currKey_739_);
lean_ctor_set(v_reuseFailAlloc_758_, 5, v_items_740_);
v___x_749_ = v_reuseFailAlloc_758_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_array_get_size(v_ks_730_);
v___x_752_ = lean_nat_dec_lt(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_745_);
lean_ctor_set(v___x_753_, 1, v___x_749_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_751_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_730_, v___x_755_, v___x_756_, v___x_745_, v___x_749_, v_a_732_, v_a_733_);
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec_ref(v_ks_763_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_769_, lean_object* v_t_770_, lean_object* v_k_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_770_, v_k_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_773_, lean_object* v_t_774_, lean_object* v_k_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_773_, v_t_774_, v_k_775_);
lean_dec(v_k_775_);
lean_dec(v_t_774_);
return v_res_776_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0(void){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_777_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___y_792_; lean_object* v_keyTys_793_; lean_object* v_arrKeyTys_794_; lean_object* v_arrParents_795_; lean_object* v_currArrKey_796_; lean_object* v_items_797_; lean_object* v_toCold_809_; lean_object* v_currRecDepth_810_; lean_object* v_ref_811_; uint16_t v_optionFlags_812_; uint8_t v_suppressElabErrors_813_; uint8_t v_isRecordingDeps_814_; lean_object* v___x_815_; uint8_t v___x_816_; lean_object* v_ref_817_; lean_object* v___x_818_; 
v_toCold_809_ = lean_ctor_get(v_a_788_, 0);
v_currRecDepth_810_ = lean_ctor_get(v_a_788_, 1);
v_ref_811_ = lean_ctor_get(v_a_788_, 2);
v_optionFlags_812_ = lean_ctor_get_uint16(v_a_788_, sizeof(void*)*3);
v_suppressElabErrors_813_ = lean_ctor_get_uint8(v_a_788_, sizeof(void*)*3 + 2);
v_isRecordingDeps_814_ = lean_ctor_get_uint8(v_a_788_, sizeof(void*)*3 + 3);
v___x_815_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_786_);
v___x_816_ = l_Lean_Syntax_isOfKind(v_x_786_, v___x_815_);
v_ref_817_ = l_Lean_replaceRef(v_x_786_, v_ref_811_);
lean_inc(v_currRecDepth_810_);
lean_inc_ref(v_toCold_809_);
v___x_818_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_818_, 0, v_toCold_809_);
lean_ctor_set(v___x_818_, 1, v_currRecDepth_810_);
lean_ctor_set(v___x_818_, 2, v_ref_817_);
lean_ctor_set_uint16(v___x_818_, sizeof(void*)*3, v_optionFlags_812_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*3 + 2, v_suppressElabErrors_813_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*3 + 3, v_isRecordingDeps_814_);
if (v___x_816_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4);
v___x_820_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_786_, v___x_819_, v_a_787_, v___x_818_, v_a_789_);
lean_dec_ref_known(v___x_818_, 3);
lean_dec_ref(v_a_787_);
lean_dec(v_x_786_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___y_824_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = l_Lean_Syntax_getArg(v_x_786_, v___x_821_);
v___x_892_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_822_);
v___x_893_ = l_Lean_Syntax_isOfKind(v___x_822_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec(v_x_786_);
v___x_894_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_895_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_822_, v___x_894_, v_a_787_, v___x_818_, v_a_789_);
lean_dec_ref_known(v___x_818_, 3);
lean_dec_ref(v_a_787_);
lean_dec(v___x_822_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = l_Lean_Syntax_getArg(v___x_822_, v___x_896_);
v___x_898_ = l_Lean_Syntax_getArgs(v___x_897_);
lean_dec(v___x_897_);
v___x_899_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_900_ = lean_array_get_size(v___x_898_);
v___x_901_ = lean_nat_dec_lt(v___x_896_, v___x_900_);
if (v___x_901_ == 0)
{
lean_dec_ref(v___x_898_);
v___y_824_ = v___x_899_;
goto v___jp_823_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; lean_object* v_snd_907_; 
v___x_902_ = lean_box(v___x_901_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_899_);
v___x_904_ = ((size_t)0ULL);
v___x_905_ = lean_usize_of_nat(v___x_900_);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_893_, v___x_898_, v___x_904_, v___x_905_, v___x_903_);
lean_dec_ref(v___x_898_);
v_snd_907_ = lean_ctor_get(v___x_906_, 1);
lean_inc(v_snd_907_);
lean_dec_ref(v___x_906_);
v___y_824_ = v_snd_907_;
goto v___jp_823_;
}
}
v___jp_823_:
{
size_t v_sz_825_; size_t v___x_826_; lean_object* v___x_827_; 
v_sz_825_ = lean_array_size(v___y_824_);
v___x_826_ = ((size_t)0ULL);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_825_, v___x_826_, v___y_824_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec(v_x_786_);
v___x_828_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_829_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_822_, v___x_828_, v_a_787_, v___x_818_, v_a_789_);
lean_dec_ref_known(v___x_818_, 3);
lean_dec_ref(v_a_787_);
lean_dec(v___x_822_);
return v___x_829_;
}
else
{
lean_object* v_val_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_tailKey_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v___x_822_);
v_val_830_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v___x_827_, 1);
v___x_831_ = lean_box(0);
v___x_832_ = lean_array_get_size(v_val_830_);
v___x_833_ = lean_nat_sub(v___x_832_, v___x_821_);
v_tailKey_834_ = lean_array_get(v___x_831_, v_val_830_, v___x_833_);
lean_dec(v___x_833_);
v___x_835_ = lean_array_pop(v_val_830_);
v___x_836_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_835_, v_a_787_, v___x_818_, v_a_789_);
lean_dec_ref(v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v_fst_838_; lean_object* v_snd_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_883_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
v_fst_838_ = lean_ctor_get(v_a_837_, 0);
v_snd_839_ = lean_ctor_get(v_a_837_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_a_837_);
if (v_isSharedCheck_883_ == 0)
{
v___x_841_ = v_a_837_;
v_isShared_842_ = v_isSharedCheck_883_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snd_839_);
lean_inc(v_fst_838_);
lean_dec(v_a_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_883_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; 
lean_inc(v_tailKey_834_);
v___x_843_ = l_Lake_Toml_elabSimpleKey(v_tailKey_834_, v___x_818_, v_a_789_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v_keyTys_845_; lean_object* v_arrKeyTys_846_; lean_object* v_arrParents_847_; lean_object* v_currArrKey_848_; lean_object* v_items_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v_keyTys_845_ = lean_ctor_get(v_snd_839_, 0);
v_arrKeyTys_846_ = lean_ctor_get(v_snd_839_, 1);
v_arrParents_847_ = lean_ctor_get(v_snd_839_, 2);
v_currArrKey_848_ = lean_ctor_get(v_snd_839_, 3);
v_items_849_ = lean_ctor_get(v_snd_839_, 5);
v___x_850_ = l_Lean_Name_str___override(v_fst_838_, v_a_844_);
v___x_851_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_845_, v___x_850_);
if (lean_obj_tag(v___x_851_) == 1)
{
lean_object* v_val_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_874_; 
v_val_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_874_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_874_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_val_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_874_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v___x_856_; 
v___x_856_ = lean_unbox(v_val_852_);
if (v___x_856_ == 4)
{
lean_inc_ref(v_items_849_);
lean_inc(v_currArrKey_848_);
lean_inc(v_arrParents_847_);
lean_inc(v_arrKeyTys_846_);
lean_inc(v_keyTys_845_);
lean_del_object(v___x_854_);
lean_dec(v_val_852_);
lean_del_object(v___x_841_);
lean_dec(v_snd_839_);
lean_dec(v_tailKey_834_);
lean_dec_ref_known(v___x_818_, 3);
v___y_792_ = v___x_850_;
v_keyTys_793_ = v_keyTys_845_;
v_arrKeyTys_794_ = v_arrKeyTys_846_;
v_arrParents_795_ = v_arrParents_847_;
v_currArrKey_796_ = v_currArrKey_848_;
v_items_797_ = v_items_849_;
goto v___jp_791_;
}
else
{
lean_object* v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_x_786_);
v___x_857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_858_ = lean_unbox(v_val_852_);
lean_dec(v_val_852_);
v___x_859_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_858_);
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 3);
lean_ctor_set(v___x_854_, 0, v___x_859_);
v___x_861_ = v___x_854_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_873_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = l_Lean_MessageData_ofFormat(v___x_861_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 7);
lean_ctor_set(v___x_841_, 1, v___x_862_);
lean_ctor_set(v___x_841_, 0, v___x_857_);
v___x_864_ = v___x_841_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_862_);
v___x_864_ = v_reuseFailAlloc_872_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_865_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Lean_MessageData_ofName(v___x_850_);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_834_, v___x_870_, v_snd_839_, v___x_818_, v_a_789_);
lean_dec_ref_known(v___x_818_, 3);
lean_dec(v_snd_839_);
lean_dec(v_tailKey_834_);
return v___x_871_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_849_);
lean_inc(v_currArrKey_848_);
lean_inc(v_arrParents_847_);
lean_inc(v_arrKeyTys_846_);
lean_inc(v_keyTys_845_);
lean_dec(v___x_851_);
lean_del_object(v___x_841_);
lean_dec(v_snd_839_);
lean_dec(v_tailKey_834_);
lean_dec_ref_known(v___x_818_, 3);
v___y_792_ = v___x_850_;
v_keyTys_793_ = v_keyTys_845_;
v_arrKeyTys_794_ = v_arrKeyTys_846_;
v_arrParents_795_ = v_arrParents_847_;
v_currArrKey_796_ = v_currArrKey_848_;
v_items_797_ = v_items_849_;
goto v___jp_791_;
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_del_object(v___x_841_);
lean_dec(v_snd_839_);
lean_dec(v_fst_838_);
lean_dec(v_tailKey_834_);
lean_dec_ref_known(v___x_818_, 3);
lean_dec(v_x_786_);
v_a_875_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_843_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_843_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_tailKey_834_);
lean_dec_ref_known(v___x_818_, 3);
lean_dec(v_x_786_);
v_a_884_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_836_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_836_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
v___jp_791_:
{
lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_798_ = lean_box(0);
v___x_799_ = 1;
v___x_800_ = lean_box(v___x_799_);
lean_inc_n(v___y_792_, 2);
v___x_801_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_792_, v___x_800_, v_keyTys_793_);
v___x_802_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_x_786_);
v___x_803_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_803_, 0, v_x_786_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_804_, 0, v_x_786_);
lean_ctor_set(v___x_804_, 1, v___y_792_);
lean_ctor_set(v___x_804_, 2, v___x_803_);
v___x_805_ = lean_array_push(v_items_797_, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_806_, 0, v___x_801_);
lean_ctor_set(v___x_806_, 1, v_arrKeyTys_794_);
lean_ctor_set(v___x_806_, 2, v_arrParents_795_);
lean_ctor_set(v___x_806_, 3, v_currArrKey_796_);
lean_ctor_set(v___x_806_, 4, v___y_792_);
lean_ctor_set(v___x_806_, 5, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_798_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
return v_res_913_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_toCold_927_; lean_object* v_currRecDepth_928_; lean_object* v_ref_929_; uint16_t v_optionFlags_930_; uint8_t v_suppressElabErrors_931_; uint8_t v_isRecordingDeps_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v_ref_935_; lean_object* v___x_936_; lean_object* v___y_938_; 
v_toCold_927_ = lean_ctor_get(v_a_924_, 0);
v_currRecDepth_928_ = lean_ctor_get(v_a_924_, 1);
v_ref_929_ = lean_ctor_get(v_a_924_, 2);
v_optionFlags_930_ = lean_ctor_get_uint16(v_a_924_, sizeof(void*)*3);
v_suppressElabErrors_931_ = lean_ctor_get_uint8(v_a_924_, sizeof(void*)*3 + 2);
v_isRecordingDeps_932_ = lean_ctor_get_uint8(v_a_924_, sizeof(void*)*3 + 3);
v___x_933_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_922_);
v___x_934_ = l_Lean_Syntax_isOfKind(v_x_922_, v___x_933_);
v_ref_935_ = l_Lean_replaceRef(v_x_922_, v_ref_929_);
lean_inc(v_currRecDepth_928_);
lean_inc_ref(v_toCold_927_);
v___x_936_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_936_, 0, v_toCold_927_);
lean_ctor_set(v___x_936_, 1, v_currRecDepth_928_);
lean_ctor_set(v___x_936_, 2, v_ref_935_);
lean_ctor_set_uint16(v___x_936_, sizeof(void*)*3, v_optionFlags_930_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*3 + 2, v_suppressElabErrors_931_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*3 + 3, v_isRecordingDeps_932_);
if (v___x_934_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_946_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_922_, v___x_945_, v_a_923_, v___x_936_, v_a_925_);
lean_dec_ref_known(v___x_936_, 3);
lean_dec_ref(v_a_923_);
lean_dec(v_x_922_);
return v___x_946_;
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; lean_object* v___y_952_; 
v___x_947_ = lean_unsigned_to_nat(2u);
v___x_948_ = l_Lean_Syntax_getArg(v_x_922_, v___x_947_);
v___x_949_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_948_);
v___x_950_ = l_Lean_Syntax_isOfKind(v___x_948_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v___x_948_);
v___x_1086_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1087_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_922_, v___x_1086_, v_a_923_, v___x_936_, v_a_925_);
lean_dec_ref_known(v___x_936_, 3);
lean_dec_ref(v_a_923_);
lean_dec(v_x_922_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = l_Lean_Syntax_getArg(v___x_948_, v___x_1088_);
lean_dec(v___x_948_);
v___x_1090_ = l_Lean_Syntax_getArgs(v___x_1089_);
lean_dec(v___x_1089_);
v___x_1091_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1092_ = lean_array_get_size(v___x_1090_);
v___x_1093_ = lean_nat_dec_lt(v___x_1088_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v___x_1090_);
v___y_952_ = v___x_1091_;
goto v___jp_951_;
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; lean_object* v_snd_1099_; 
v___x_1094_ = lean_box(v___x_1093_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1091_);
v___x_1096_ = ((size_t)0ULL);
v___x_1097_ = lean_usize_of_nat(v___x_1092_);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_950_, v___x_1090_, v___x_1096_, v___x_1097_, v___x_1095_);
lean_dec_ref(v___x_1090_);
v_snd_1099_ = lean_ctor_get(v___x_1098_, 1);
lean_inc(v_snd_1099_);
lean_dec_ref(v___x_1098_);
v___y_952_ = v_snd_1099_;
goto v___jp_951_;
}
}
v___jp_951_:
{
size_t v_sz_953_; size_t v___x_954_; lean_object* v___x_955_; 
v_sz_953_ = lean_array_size(v___y_952_);
v___x_954_ = ((size_t)0ULL);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_953_, v___x_954_, v___y_952_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_957_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_922_, v___x_956_, v_a_923_, v___x_936_, v_a_925_);
lean_dec_ref_known(v___x_936_, 3);
lean_dec_ref(v_a_923_);
lean_dec(v_x_922_);
return v___x_957_;
}
else
{
lean_object* v_val_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_tailKey_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_val_958_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v___x_955_, 1);
v___x_959_ = lean_box(0);
v___x_960_ = lean_array_get_size(v_val_958_);
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_nat_sub(v___x_960_, v___x_961_);
v_tailKey_963_ = lean_array_get(v___x_959_, v_val_958_, v___x_962_);
lean_dec(v___x_962_);
v___x_964_ = lean_array_pop(v_val_958_);
v___x_965_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_964_, v_a_923_, v___x_936_, v_a_925_);
lean_dec_ref(v___x_964_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v_fst_967_; lean_object* v_snd_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1077_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v_fst_967_ = lean_ctor_get(v_a_966_, 0);
v_snd_968_ = lean_ctor_get(v_a_966_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_a_966_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_970_ = v_a_966_;
v_isShared_971_ = v_isSharedCheck_1077_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_snd_968_);
lean_inc(v_fst_967_);
lean_dec(v_a_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1077_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; 
lean_inc(v_tailKey_963_);
v___x_972_ = l_Lake_Toml_elabSimpleKey(v_tailKey_963_, v___x_936_, v_a_925_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1068_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1068_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1068_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_keyTys_977_; lean_object* v_arrKeyTys_978_; lean_object* v_arrParents_979_; lean_object* v_currArrKey_980_; lean_object* v_items_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_keyTys_977_ = lean_ctor_get(v_snd_968_, 0);
v_arrKeyTys_978_ = lean_ctor_get(v_snd_968_, 1);
v_arrParents_979_ = lean_ctor_get(v_snd_968_, 2);
v_currArrKey_980_ = lean_ctor_get(v_snd_968_, 3);
v_items_981_ = lean_ctor_get(v_snd_968_, 5);
v___x_982_ = l_Lean_Name_str___override(v_fst_967_, v_a_973_);
v___x_983_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_977_, v___x_982_);
if (lean_obj_tag(v___x_983_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1035_; 
v_val_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_1035_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_val_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1035_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v___x_988_; 
v___x_988_ = lean_unbox(v_val_984_);
if (v___x_988_ == 2)
{
lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1013_; 
lean_inc_ref(v_items_981_);
lean_inc(v_arrParents_979_);
lean_inc(v_arrKeyTys_978_);
lean_del_object(v___x_986_);
lean_dec(v_val_984_);
lean_dec(v_tailKey_963_);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_snd_968_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; lean_object* v_unused_1015_; lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1014_ = lean_ctor_get(v_snd_968_, 5);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_snd_968_, 4);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_snd_968_, 3);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_snd_968_, 2);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_snd_968_, 1);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_snd_968_, 0);
lean_dec(v_unused_1019_);
v___x_990_ = v_snd_968_;
v_isShared_991_ = v_isSharedCheck_1013_;
goto v_resetjp_989_;
}
else
{
lean_dec(v_snd_968_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1013_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_979_, v___x_982_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_del_object(v___x_990_);
lean_dec_ref(v_items_981_);
lean_dec(v_arrParents_979_);
lean_dec(v_arrKeyTys_978_);
lean_del_object(v___x_975_);
lean_del_object(v___x_970_);
lean_dec(v_x_922_);
v___y_938_ = v___x_982_;
goto v___jp_937_;
}
else
{
lean_object* v_val_993_; lean_object* v___x_994_; 
v_val_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_val_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_978_, v_val_993_);
lean_dec(v_val_993_);
if (lean_obj_tag(v___x_994_) == 1)
{
lean_object* v_val_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec_ref_known(v___x_936_, 3);
v_val_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = lean_box(0);
v___x_997_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_922_, 2);
v___x_998_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_998_, 0, v_x_922_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_mk_empty_array_with_capacity(v___x_961_);
v___x_1000_ = lean_array_push(v___x_999_, v___x_998_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_x_922_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
lean_inc_n(v___x_982_, 2);
v___x_1002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1002_, 0, v_x_922_);
lean_ctor_set(v___x_1002_, 1, v___x_982_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
v___x_1003_ = lean_array_push(v_items_981_, v___x_1002_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 5, v___x_1003_);
lean_ctor_set(v___x_990_, 4, v___x_982_);
lean_ctor_set(v___x_990_, 3, v___x_982_);
lean_ctor_set(v___x_990_, 0, v_val_995_);
v___x_1005_ = v___x_990_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_val_995_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_arrKeyTys_978_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_arrParents_979_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_1012_, 5, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1005_);
lean_ctor_set(v___x_970_, 0, v___x_996_);
v___x_1007_ = v___x_970_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_1007_);
v___x_1009_ = v___x_975_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_dec(v___x_994_);
lean_del_object(v___x_990_);
lean_dec_ref(v_items_981_);
lean_dec(v_arrParents_979_);
lean_dec(v_arrKeyTys_978_);
lean_del_object(v___x_975_);
lean_del_object(v___x_970_);
lean_dec(v_x_922_);
v___y_938_ = v___x_982_;
goto v___jp_937_;
}
}
}
}
else
{
lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_del_object(v___x_975_);
lean_del_object(v___x_970_);
lean_dec(v_x_922_);
v___x_1020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1021_ = lean_unbox(v_val_984_);
lean_dec(v_val_984_);
v___x_1022_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1021_);
v___x_1023_ = lean_string_append(v___x_1020_, v___x_1022_);
lean_dec_ref(v___x_1022_);
v___x_1024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1025_ = lean_string_append(v___x_1023_, v___x_1024_);
v___x_1026_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_982_, v___x_950_);
v___x_1027_ = lean_string_append(v___x_1025_, v___x_1026_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1029_ = lean_string_append(v___x_1027_, v___x_1028_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 3);
lean_ctor_set(v___x_986_, 0, v___x_1029_);
v___x_1031_ = v___x_986_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = l_Lean_MessageData_ofFormat(v___x_1031_);
v___x_1033_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_963_, v___x_1032_, v_snd_968_, v___x_936_, v_a_925_);
lean_dec_ref_known(v___x_936_, 3);
lean_dec(v_snd_968_);
lean_dec(v_tailKey_963_);
return v___x_1033_;
}
}
}
}
else
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1061_; 
lean_inc_ref(v_items_981_);
lean_inc(v_currArrKey_980_);
lean_inc(v_arrParents_979_);
lean_inc(v_arrKeyTys_978_);
lean_inc(v_keyTys_977_);
lean_dec(v___x_983_);
lean_dec(v_tailKey_963_);
lean_dec_ref_known(v___x_936_, 3);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_snd_968_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; lean_object* v_unused_1063_; lean_object* v_unused_1064_; lean_object* v_unused_1065_; lean_object* v_unused_1066_; lean_object* v_unused_1067_; 
v_unused_1062_ = lean_ctor_get(v_snd_968_, 5);
lean_dec(v_unused_1062_);
v_unused_1063_ = lean_ctor_get(v_snd_968_, 4);
lean_dec(v_unused_1063_);
v_unused_1064_ = lean_ctor_get(v_snd_968_, 3);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v_snd_968_, 2);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_snd_968_, 1);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_snd_968_, 0);
lean_dec(v_unused_1067_);
v___x_1037_ = v_snd_968_;
v_isShared_1038_ = v_isSharedCheck_1061_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v_snd_968_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1061_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = 2;
v___x_1041_ = lean_box(v___x_1040_);
lean_inc_n(v___x_982_, 4);
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_982_, v___x_1041_, v_keyTys_977_);
lean_inc(v___x_1042_);
lean_inc(v_currArrKey_980_);
v___x_1043_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_980_, v___x_1042_, v_arrKeyTys_978_);
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_982_, v_currArrKey_980_, v_arrParents_979_);
v___x_1045_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_922_, 2);
v___x_1046_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_x_922_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_mk_empty_array_with_capacity(v___x_961_);
v___x_1048_ = lean_array_push(v___x_1047_, v___x_1046_);
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_x_922_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1050_, 0, v_x_922_);
lean_ctor_set(v___x_1050_, 1, v___x_982_);
lean_ctor_set(v___x_1050_, 2, v___x_1049_);
v___x_1051_ = lean_array_push(v_items_981_, v___x_1050_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 5, v___x_1051_);
lean_ctor_set(v___x_1037_, 4, v___x_982_);
lean_ctor_set(v___x_1037_, 3, v___x_982_);
lean_ctor_set(v___x_1037_, 2, v___x_1044_);
lean_ctor_set(v___x_1037_, 1, v___x_1043_);
lean_ctor_set(v___x_1037_, 0, v___x_1042_);
v___x_1053_ = v___x_1037_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_1060_, 5, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1055_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1053_);
lean_ctor_set(v___x_970_, 0, v___x_1039_);
v___x_1055_ = v___x_970_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_1055_);
v___x_1057_ = v___x_975_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_del_object(v___x_970_);
lean_dec(v_snd_968_);
lean_dec(v_fst_967_);
lean_dec(v_tailKey_963_);
lean_dec_ref_known(v___x_936_, 3);
lean_dec(v_x_922_);
v_a_1069_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_972_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_972_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v_tailKey_963_);
lean_dec_ref_known(v___x_936_, 3);
lean_dec(v_x_922_);
v_a_1078_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_965_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_965_);
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
}
v___jp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_939_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_940_ = l_Lean_MessageData_ofName(v___y_938_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_943_, v___x_936_, v_a_925_);
lean_dec_ref_known(v___x_936_, 3);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
return v_res_1105_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1109_);
v___x_1115_ = l_Lean_Syntax_isOfKind(v_x_1109_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_1109_);
v___x_1117_ = l_Lean_Syntax_isOfKind(v_x_1109_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1109_);
v___x_1119_ = l_Lean_Syntax_isOfKind(v_x_1109_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1121_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1109_, v___x_1120_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec_ref(v_a_1110_);
lean_dec(v_x_1109_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1122_;
}
}
else
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1123_;
}
}
else
{
lean_object* v___x_1124_; 
v___x_1124_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1132_, lean_object* v_as_1133_, size_t v_i_1134_, size_t v_stop_1135_, lean_object* v_b_1136_){
_start:
{
lean_object* v___y_1138_; uint8_t v___x_1142_; 
v___x_1142_ = lean_usize_dec_eq(v_i_1134_, v_stop_1135_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v_fst_1144_; lean_object* v_snd_1145_; lean_object* v___x_1146_; 
v___x_1143_ = lean_array_uget_borrowed(v_as_1133_, v_i_1134_);
v_fst_1144_ = lean_ctor_get(v___x_1143_, 0);
v_snd_1145_ = lean_ctor_get(v___x_1143_, 1);
lean_inc(v_fst_1144_);
v___x_1146_ = l_Lean_Name_components(v_fst_1144_);
if (lean_obj_tag(v___x_1146_) == 0)
{
v___y_1138_ = v_b_1136_;
goto v___jp_1137_;
}
else
{
lean_object* v_head_1147_; lean_object* v_tail_1148_; lean_object* v___x_1149_; 
v_head_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_head_1147_);
v_tail_1148_ = lean_ctor_get(v___x_1146_, 1);
lean_inc(v_tail_1148_);
lean_dec_ref_known(v___x_1146_, 2);
lean_inc(v_snd_1145_);
lean_inc(v_ref_1132_);
v___x_1149_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1136_, v_ref_1132_, v_head_1147_, v_tail_1148_, v_snd_1145_);
v___y_1138_ = v___x_1149_;
goto v___jp_1137_;
}
}
else
{
lean_dec(v_ref_1132_);
return v_b_1136_;
}
v___jp_1137_:
{
size_t v___x_1139_; size_t v___x_1140_; 
v___x_1139_ = ((size_t)1ULL);
v___x_1140_ = lean_usize_add(v_i_1134_, v___x_1139_);
v_i_1134_ = v___x_1140_;
v_b_1136_ = v___y_1138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1150_, size_t v_i_1151_, lean_object* v_bs_1152_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_usize_dec_lt(v_i_1151_, v_sz_1150_);
if (v___x_1153_ == 0)
{
return v_bs_1152_;
}
else
{
lean_object* v_v_1154_; lean_object* v___x_1155_; lean_object* v_bs_x27_1156_; lean_object* v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; lean_object* v___x_1160_; 
v_v_1154_ = lean_array_uget(v_bs_1152_, v_i_1151_);
v___x_1155_ = lean_unsigned_to_nat(0u);
v_bs_x27_1156_ = lean_array_uset(v_bs_1152_, v_i_1151_, v___x_1155_);
v___x_1157_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1154_);
v___x_1158_ = ((size_t)1ULL);
v___x_1159_ = lean_usize_add(v_i_1151_, v___x_1158_);
v___x_1160_ = lean_array_uset(v_bs_x27_1156_, v_i_1151_, v___x_1157_);
v_i_1151_ = v___x_1159_;
v_bs_1152_ = v___x_1160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1162_){
_start:
{
switch(lean_obj_tag(v_a_1162_))
{
case 6:
{
lean_object* v_xs_1163_; lean_object* v_ref_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1182_; 
v_xs_1163_ = lean_ctor_get(v_a_1162_, 1);
v_ref_1164_ = lean_ctor_get(v_a_1162_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_a_1162_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1166_ = v_a_1162_;
v_isShared_1167_ = v_isSharedCheck_1182_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_xs_1163_);
lean_inc(v_ref_1164_);
lean_dec(v_a_1162_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1182_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_items_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_items_1168_ = lean_ctor_get(v_xs_1163_, 0);
lean_inc_ref(v_items_1168_);
lean_dec_ref(v_xs_1163_);
v___x_1169_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_array_get_size(v_items_1168_);
v___x_1172_ = lean_nat_dec_lt(v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1174_; 
lean_dec_ref(v_items_1168_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1169_);
v___x_1174_ = v___x_1166_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_ref_1164_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
else
{
size_t v___x_1176_; size_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1176_ = ((size_t)0ULL);
v___x_1177_ = lean_usize_of_nat(v___x_1171_);
lean_inc(v_ref_1164_);
v___x_1178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1164_, v_items_1168_, v___x_1176_, v___x_1177_, v___x_1169_);
lean_dec_ref(v_items_1168_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1178_);
v___x_1180_ = v___x_1166_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_ref_1164_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
case 5:
{
lean_object* v_ref_1183_; lean_object* v_xs_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1194_; 
v_ref_1183_ = lean_ctor_get(v_a_1162_, 0);
v_xs_1184_ = lean_ctor_get(v_a_1162_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_a_1162_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1186_ = v_a_1162_;
v_isShared_1187_ = v_isSharedCheck_1194_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_xs_1184_);
lean_inc(v_ref_1183_);
lean_dec(v_a_1162_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1194_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
size_t v_sz_1188_; size_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v_sz_1188_ = lean_array_size(v_xs_1184_);
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1188_, v___x_1189_, v_xs_1184_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1190_);
v___x_1192_ = v___x_1186_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_ref_1183_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
default: 
{
return v_a_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1195_, lean_object* v___x_1196_, lean_object* v_v_x3f_1197_){
_start:
{
if (lean_obj_tag(v_v_x3f_1197_) == 1)
{
lean_object* v_val_1198_; 
v_val_1198_ = lean_ctor_get(v_v_x3f_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v_v_x3f_1197_, 1);
switch(lean_obj_tag(v_val_1198_))
{
case 6:
{
lean_object* v_ref_1199_; lean_object* v_xs_1200_; lean_object* v___x_1201_; 
v_ref_1199_ = lean_ctor_get(v_val_1198_, 0);
lean_inc(v_ref_1199_);
v_xs_1200_ = lean_ctor_get(v_val_1198_, 1);
lean_inc_ref(v_xs_1200_);
lean_dec_ref_known(v_val_1198_, 2);
v___x_1201_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1195_);
if (lean_obj_tag(v___x_1201_) == 6)
{
lean_object* v_xs_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1211_; 
v_xs_1202_ = lean_ctor_get(v___x_1201_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v___x_1201_, 0);
lean_dec(v_unused_1212_);
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1211_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_xs_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1211_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_items_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v_items_1206_ = lean_ctor_get(v_xs_1202_, 0);
lean_inc_ref(v_items_1206_);
lean_dec_ref(v_xs_1202_);
v___x_1207_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1196_, v_xs_1200_, v_items_1206_);
lean_dec_ref(v_items_1206_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1207_);
lean_ctor_set(v___x_1204_, 0, v_ref_1199_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_ref_1199_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_dec_ref(v_xs_1200_);
lean_dec(v_ref_1199_);
lean_dec_ref(v___x_1196_);
return v___x_1201_;
}
}
case 5:
{
lean_object* v_ref_1213_; lean_object* v_xs_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v___x_1196_);
v_ref_1213_ = lean_ctor_get(v_val_1198_, 0);
v_xs_1214_ = lean_ctor_get(v_val_1198_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_val_1198_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1216_ = v_val_1198_;
v_isShared_1217_ = v_isSharedCheck_1233_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_xs_1214_);
lean_inc(v_ref_1213_);
lean_dec(v_val_1198_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1233_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; 
v___x_1218_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1195_);
if (lean_obj_tag(v___x_1218_) == 5)
{
lean_object* v_xs_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
lean_del_object(v___x_1216_);
v_xs_1219_ = lean_ctor_get(v___x_1218_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v___x_1218_, 0);
lean_dec(v_unused_1228_);
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_xs_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = l_Array_append___redArg(v_xs_1214_, v_xs_1219_);
lean_dec_ref(v_xs_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___x_1223_);
lean_ctor_set(v___x_1221_, 0, v_ref_1213_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_ref_1213_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_array_push(v_xs_1214_, v___x_1218_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v___x_1229_);
v___x_1231_ = v___x_1216_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_ref_1213_);
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
}
default: 
{
lean_object* v___x_1234_; 
lean_dec(v_val_1198_);
lean_dec_ref(v___x_1196_);
v___x_1234_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1195_);
return v___x_1234_;
}
}
}
else
{
lean_object* v___x_1235_; 
lean_dec(v_v_x3f_1197_);
lean_dec_ref(v___x_1196_);
v___x_1235_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1195_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1236_, lean_object* v_k_1237_, lean_object* v_t_1238_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1238_);
lean_inc(v_k_1237_);
v___x_1240_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1239_, v_k_1237_, v_t_1238_);
if (lean_obj_tag(v___x_1240_) == 1)
{
lean_object* v_val_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_k_1237_);
v_val_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1276_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_val_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1276_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_items_1245_; lean_object* v_indices_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1275_; 
v_items_1245_ = lean_ctor_get(v_t_1238_, 0);
v_indices_1246_ = lean_ctor_get(v_t_1238_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_t_1238_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1248_ = v_t_1238_;
v_isShared_1249_ = v_isSharedCheck_1275_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_indices_1246_);
lean_inc(v_items_1245_);
lean_dec(v_t_1238_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1275_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_array_get_size(v_items_1245_);
v___x_1251_ = lean_nat_dec_lt(v_val_1241_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1253_; 
lean_del_object(v___x_1243_);
lean_dec(v_val_1241_);
lean_dec_ref(v_newV_1236_);
if (v_isShared_1249_ == 0)
{
v___x_1253_ = v___x_1248_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_items_1245_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_indices_1246_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
else
{
lean_object* v_v_1255_; lean_object* v_fst_1256_; lean_object* v_snd_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1274_; 
v_v_1255_ = lean_array_fget(v_items_1245_, v_val_1241_);
v_fst_1256_ = lean_ctor_get(v_v_1255_, 0);
v_snd_1257_ = lean_ctor_get(v_v_1255_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_v_1255_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1259_ = v_v_1255_;
v_isShared_1260_ = v_isSharedCheck_1274_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_snd_1257_);
lean_inc(v_fst_1256_);
lean_dec(v_v_1255_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1274_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v_xs_x27_1262_; lean_object* v___x_1264_; 
v___x_1261_ = lean_box(0);
v_xs_x27_1262_ = lean_array_fset(v_items_1245_, v_val_1241_, v___x_1261_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_snd_1257_);
v___x_1264_ = v___x_1243_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_snd_1257_);
v___x_1264_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1236_, v___x_1239_, v___x_1264_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v___x_1265_);
v___x_1267_ = v___x_1259_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_fst_1256_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = lean_array_fset(v_xs_x27_1262_, v_val_1241_, v___x_1267_);
lean_dec(v_val_1241_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1268_);
v___x_1270_ = v___x_1248_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_indices_1246_);
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
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec(v___x_1240_);
v___x_1277_ = lean_box(0);
v___x_1278_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1236_, v___x_1239_, v___x_1277_);
v___x_1279_ = l_Lake_Toml_RBDict_push___redArg(v___x_1239_, v_k_1237_, v___x_1278_, v_t_1238_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1280_, lean_object* v_head_1281_, lean_object* v_tail_1282_, lean_object* v_newV_1283_, lean_object* v_v_x3f_1284_){
_start:
{
if (lean_obj_tag(v_v_x3f_1284_) == 1)
{
lean_object* v_val_1285_; 
v_val_1285_ = lean_ctor_get(v_v_x3f_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v_v_x3f_1284_, 1);
switch(lean_obj_tag(v_val_1285_))
{
case 5:
{
lean_object* v_ref_1286_; lean_object* v_xs_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_ref_1286_ = lean_ctor_get(v_val_1285_, 0);
v_xs_1287_ = lean_ctor_get(v_val_1285_, 1);
v___x_1288_ = lean_array_get_size(v_xs_1287_);
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_nat_sub(v___x_1288_, v___x_1289_);
v___x_1291_ = lean_nat_dec_lt(v___x_1290_, v___x_1288_);
if (v___x_1291_ == 0)
{
lean_dec(v___x_1290_);
lean_dec_ref(v_newV_1283_);
lean_dec(v_tail_1282_);
lean_dec(v_head_1281_);
lean_dec(v_kRef_1280_);
return v_val_1285_;
}
else
{
lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1316_; 
lean_inc_ref(v_xs_1287_);
lean_inc(v_ref_1286_);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_val_1285_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; lean_object* v_unused_1318_; 
v_unused_1317_ = lean_ctor_get(v_val_1285_, 1);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_val_1285_, 0);
lean_dec(v_unused_1318_);
v___x_1293_ = v_val_1285_;
v_isShared_1294_ = v_isSharedCheck_1316_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v_val_1285_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1316_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_v_1295_; lean_object* v___x_1296_; lean_object* v_xs_x27_1297_; lean_object* v___y_1299_; 
v_v_1295_ = lean_array_fget(v_xs_1287_, v___x_1290_);
v___x_1296_ = lean_box(0);
v_xs_x27_1297_ = lean_array_fset(v_xs_1287_, v___x_1290_, v___x_1296_);
if (lean_obj_tag(v_v_1295_) == 6)
{
lean_object* v_ref_1304_; lean_object* v_xs_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1313_; 
v_ref_1304_ = lean_ctor_get(v_v_1295_, 0);
v_xs_1305_ = lean_ctor_get(v_v_1295_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_v_1295_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1307_ = v_v_1295_;
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_xs_1305_);
lean_inc(v_ref_1304_);
lean_dec(v_v_1295_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1305_, v_kRef_1280_, v_head_1281_, v_tail_1282_, v_newV_1283_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1309_);
v___x_1311_ = v___x_1307_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_ref_1304_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
v___y_1299_ = v___x_1311_;
goto v___jp_1298_;
}
}
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_v_1295_);
lean_dec_ref(v_newV_1283_);
lean_dec(v_tail_1282_);
lean_dec(v_head_1281_);
v___x_1314_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1315_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1315_, 0, v_kRef_1280_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___y_1299_ = v___x_1315_;
goto v___jp_1298_;
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1300_ = lean_array_fset(v_xs_x27_1297_, v___x_1290_, v___y_1299_);
lean_dec(v___x_1290_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v___x_1300_);
v___x_1302_ = v___x_1293_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_ref_1286_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1319_; lean_object* v_xs_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1328_; 
v_ref_1319_ = lean_ctor_get(v_val_1285_, 0);
v_xs_1320_ = lean_ctor_get(v_val_1285_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_val_1285_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1322_ = v_val_1285_;
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_xs_1320_);
lean_inc(v_ref_1319_);
lean_dec(v_val_1285_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1320_, v_kRef_1280_, v_head_1281_, v_tail_1282_, v_newV_1283_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v___x_1324_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_ref_1319_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
default: 
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v_val_1285_);
v___x_1329_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1280_);
v___x_1330_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1329_, v_kRef_1280_, v_head_1281_, v_tail_1282_, v_newV_1283_);
v___x_1331_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_kRef_1280_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
return v___x_1331_;
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec(v_v_x3f_1284_);
v___x_1332_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1280_);
v___x_1333_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1332_, v_kRef_1280_, v_head_1281_, v_tail_1282_, v_newV_1283_);
v___x_1334_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_kRef_1280_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1335_, lean_object* v_head_1336_, lean_object* v_tail_1337_, lean_object* v_newV_1338_, lean_object* v_k_1339_, lean_object* v_t_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1340_);
lean_inc(v_k_1339_);
v___x_1342_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1341_, v_k_1339_, v_t_1340_);
if (lean_obj_tag(v___x_1342_) == 1)
{
lean_object* v_val_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_k_1339_);
v_val_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1378_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_val_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1378_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_items_1347_; lean_object* v_indices_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1377_; 
v_items_1347_ = lean_ctor_get(v_t_1340_, 0);
v_indices_1348_ = lean_ctor_get(v_t_1340_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_t_1340_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1350_ = v_t_1340_;
v_isShared_1351_ = v_isSharedCheck_1377_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_indices_1348_);
lean_inc(v_items_1347_);
lean_dec(v_t_1340_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1377_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1352_ = lean_array_get_size(v_items_1347_);
v___x_1353_ = lean_nat_dec_lt(v_val_1343_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1355_; 
lean_del_object(v___x_1345_);
lean_dec(v_val_1343_);
lean_dec_ref(v_newV_1338_);
lean_dec(v_tail_1337_);
lean_dec(v_head_1336_);
lean_dec(v_kRef_1335_);
if (v_isShared_1351_ == 0)
{
v___x_1355_ = v___x_1350_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_items_1347_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_indices_1348_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
else
{
lean_object* v_v_1357_; lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1376_; 
v_v_1357_ = lean_array_fget(v_items_1347_, v_val_1343_);
v_fst_1358_ = lean_ctor_get(v_v_1357_, 0);
v_snd_1359_ = lean_ctor_get(v_v_1357_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_v_1357_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1361_ = v_v_1357_;
v_isShared_1362_ = v_isSharedCheck_1376_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snd_1359_);
lean_inc(v_fst_1358_);
lean_dec(v_v_1357_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1376_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v_xs_x27_1364_; lean_object* v___x_1366_; 
v___x_1363_ = lean_box(0);
v_xs_x27_1364_ = lean_array_fset(v_items_1347_, v_val_1343_, v___x_1363_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v_snd_1359_);
v___x_1366_ = v___x_1345_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_snd_1359_);
v___x_1366_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1335_, v_head_1336_, v_tail_1337_, v_newV_1338_, v___x_1366_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v___x_1367_);
v___x_1369_ = v___x_1361_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_fst_1358_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_array_fset(v_xs_x27_1364_, v_val_1343_, v___x_1369_);
lean_dec(v_val_1343_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1370_);
v___x_1372_ = v___x_1350_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_indices_1348_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
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
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec(v___x_1342_);
v___x_1379_ = lean_box(0);
v___x_1380_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1335_, v_head_1336_, v_tail_1337_, v_newV_1338_, v___x_1379_);
v___x_1381_ = l_Lake_Toml_RBDict_push___redArg(v___x_1341_, v_k_1339_, v___x_1380_, v_t_1340_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1382_, lean_object* v_kRef_1383_, lean_object* v_k_1384_, lean_object* v_ks_1385_, lean_object* v_newV_1386_){
_start:
{
if (lean_obj_tag(v_ks_1385_) == 0)
{
lean_object* v___x_1387_; 
lean_dec(v_kRef_1383_);
v___x_1387_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1386_, v_k_1384_, v_t_1382_);
return v___x_1387_;
}
else
{
lean_object* v_head_1388_; lean_object* v_tail_1389_; lean_object* v___x_1390_; 
v_head_1388_ = lean_ctor_get(v_ks_1385_, 0);
lean_inc(v_head_1388_);
v_tail_1389_ = lean_ctor_get(v_ks_1385_, 1);
lean_inc(v_tail_1389_);
lean_dec_ref_known(v_ks_1385_, 2);
v___x_1390_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1383_, v_head_1388_, v_tail_1389_, v_newV_1386_, v_k_1384_, v_t_1382_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1391_, lean_object* v_i_1392_, lean_object* v_bs_1393_){
_start:
{
size_t v_sz_boxed_1394_; size_t v_i_boxed_1395_; lean_object* v_res_1396_; 
v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1391_);
lean_dec(v_sz_1391_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1394_, v_i_boxed_1395_, v_bs_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1397_, lean_object* v_as_1398_, lean_object* v_i_1399_, lean_object* v_stop_1400_, lean_object* v_b_1401_){
_start:
{
size_t v_i_boxed_1402_; size_t v_stop_boxed_1403_; lean_object* v_res_1404_; 
v_i_boxed_1402_ = lean_unbox_usize(v_i_1399_);
lean_dec(v_i_1399_);
v_stop_boxed_1403_ = lean_unbox_usize(v_stop_1400_);
lean_dec(v_stop_1400_);
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1397_, v_as_1398_, v_i_boxed_1402_, v_stop_boxed_1403_, v_b_1401_);
lean_dec_ref(v_as_1398_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1405_, size_t v_i_1406_, size_t v_stop_1407_, lean_object* v_b_1408_){
_start:
{
lean_object* v___y_1410_; uint8_t v___x_1414_; 
v___x_1414_ = lean_usize_dec_eq(v_i_1406_, v_stop_1407_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v_ref_1416_; lean_object* v_key_1417_; lean_object* v_val_1418_; lean_object* v___x_1419_; 
v___x_1415_ = lean_array_uget_borrowed(v_as_1405_, v_i_1406_);
v_ref_1416_ = lean_ctor_get(v___x_1415_, 0);
v_key_1417_ = lean_ctor_get(v___x_1415_, 1);
v_val_1418_ = lean_ctor_get(v___x_1415_, 2);
lean_inc(v_key_1417_);
v___x_1419_ = l_Lean_Name_components(v_key_1417_);
if (lean_obj_tag(v___x_1419_) == 0)
{
v___y_1410_ = v_b_1408_;
goto v___jp_1409_;
}
else
{
lean_object* v_head_1420_; lean_object* v_tail_1421_; lean_object* v___x_1422_; 
v_head_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_head_1420_);
v_tail_1421_ = lean_ctor_get(v___x_1419_, 1);
lean_inc(v_tail_1421_);
lean_dec_ref_known(v___x_1419_, 2);
lean_inc_ref(v_val_1418_);
lean_inc(v_ref_1416_);
v___x_1422_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1408_, v_ref_1416_, v_head_1420_, v_tail_1421_, v_val_1418_);
v___y_1410_ = v___x_1422_;
goto v___jp_1409_;
}
}
else
{
return v_b_1408_;
}
v___jp_1409_:
{
size_t v___x_1411_; size_t v___x_1412_; 
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_add(v_i_1406_, v___x_1411_);
v_i_1406_ = v___x_1412_;
v_b_1408_ = v___y_1410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1423_, lean_object* v_i_1424_, lean_object* v_stop_1425_, lean_object* v_b_1426_){
_start:
{
size_t v_i_boxed_1427_; size_t v_stop_boxed_1428_; lean_object* v_res_1429_; 
v_i_boxed_1427_ = lean_unbox_usize(v_i_1424_);
lean_dec(v_i_1424_);
v_stop_boxed_1428_ = lean_unbox_usize(v_stop_1425_);
lean_dec(v_stop_1425_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1423_, v_i_boxed_1427_, v_stop_boxed_1428_, v_b_1426_);
lean_dec_ref(v_as_1423_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1431_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = lean_array_get_size(v_items_1430_);
v___x_1434_ = lean_nat_dec_lt(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
return v___x_1431_;
}
else
{
size_t v___x_1435_; size_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = lean_usize_of_nat(v___x_1433_);
v___x_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1430_, v___x_1435_, v___x_1436_, v___x_1431_);
return v___x_1437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1438_);
lean_dec_ref(v_items_1438_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1442_);
lean_inc_ref(v_a_1441_);
v___x_1445_ = lean_apply_4(v_x_1440_, v___x_1444_, v_a_1441_, v_a_1442_, lean_box(0));
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1456_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1456_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1456_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v_snd_1450_; lean_object* v_items_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
v_snd_1450_ = lean_ctor_get(v_a_1446_, 1);
lean_inc(v_snd_1450_);
lean_dec(v_a_1446_);
v_items_1451_ = lean_ctor_get(v_snd_1450_, 5);
lean_inc_ref(v_items_1451_);
lean_dec(v_snd_1450_);
v___x_1452_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1451_);
lean_dec_ref(v_items_1451_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v___x_1452_);
v___x_1454_ = v___x_1448_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_a_1457_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1445_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1445_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1478_, lean_object* v_x_1479_){
_start:
{
if (lean_obj_tag(v_x_1479_) == 1)
{
lean_object* v_pre_1480_; 
v_pre_1480_ = lean_ctor_get(v_x_1479_, 0);
switch(lean_obj_tag(v_pre_1480_))
{
case 1:
{
lean_object* v_pre_1481_; 
v_pre_1481_ = lean_ctor_get(v_pre_1480_, 0);
switch(lean_obj_tag(v_pre_1481_))
{
case 0:
{
lean_object* v_str_1482_; lean_object* v_str_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v_str_1482_ = lean_ctor_get(v_x_1479_, 1);
v_str_1483_ = lean_ctor_get(v_pre_1480_, 1);
v___x_1484_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1485_ = lean_string_dec_eq(v_str_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1487_ = lean_string_dec_eq(v_str_1483_, v___x_1486_);
if (v___x_1487_ == 0)
{
return v___x_1487_;
}
else
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1489_ = lean_string_dec_eq(v_str_1482_, v___x_1488_);
if (v___x_1489_ == 0)
{
return v___x_1489_;
}
else
{
return v_suppressElabErrors_1478_;
}
}
}
else
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1491_ = lean_string_dec_eq(v_str_1482_, v___x_1490_);
if (v___x_1491_ == 0)
{
return v___x_1491_;
}
else
{
return v_suppressElabErrors_1478_;
}
}
}
case 1:
{
lean_object* v_pre_1492_; 
v_pre_1492_ = lean_ctor_get(v_pre_1481_, 0);
if (lean_obj_tag(v_pre_1492_) == 0)
{
lean_object* v_str_1493_; lean_object* v_str_1494_; lean_object* v_str_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v_str_1493_ = lean_ctor_get(v_x_1479_, 1);
v_str_1494_ = lean_ctor_get(v_pre_1480_, 1);
v_str_1495_ = lean_ctor_get(v_pre_1481_, 1);
v___x_1496_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1497_ = lean_string_dec_eq(v_str_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1499_ = lean_string_dec_eq(v_str_1494_, v___x_1498_);
if (v___x_1499_ == 0)
{
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1501_ = lean_string_dec_eq(v_str_1493_, v___x_1500_);
if (v___x_1501_ == 0)
{
return v___x_1501_;
}
else
{
return v_suppressElabErrors_1478_;
}
}
}
}
else
{
uint8_t v___x_1502_; 
v___x_1502_ = 0;
return v___x_1502_;
}
}
default: 
{
uint8_t v___x_1503_; 
v___x_1503_ = 0;
return v___x_1503_;
}
}
}
case 0:
{
lean_object* v_str_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v_str_1504_ = lean_ctor_get(v_x_1479_, 1);
v___x_1505_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1506_ = lean_string_dec_eq(v_str_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
return v___x_1506_;
}
else
{
return v_suppressElabErrors_1478_;
}
}
default: 
{
uint8_t v___x_1507_; 
v___x_1507_ = 0;
return v___x_1507_;
}
}
}
else
{
uint8_t v___x_1508_; 
v___x_1508_ = 0;
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1509_, lean_object* v_x_1510_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1511_; uint8_t v_res_1512_; lean_object* v_r_1513_; 
v_suppressElabErrors_boxed_1511_ = lean_unbox(v_suppressElabErrors_1509_);
v_res_1512_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1511_, v_x_1510_);
lean_dec(v_x_1510_);
v_r_1513_ = lean_box(v_res_1512_);
return v_r_1513_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1514_, lean_object* v_opt_1515_){
_start:
{
lean_object* v_name_1516_; lean_object* v_defValue_1517_; lean_object* v_map_1518_; lean_object* v___x_1519_; 
v_name_1516_ = lean_ctor_get(v_opt_1515_, 0);
v_defValue_1517_ = lean_ctor_get(v_opt_1515_, 1);
v_map_1518_ = lean_ctor_get(v_opts_1514_, 0);
v___x_1519_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1518_, v_name_1516_);
if (lean_obj_tag(v___x_1519_) == 0)
{
uint8_t v___x_1520_; 
v___x_1520_ = lean_unbox(v_defValue_1517_);
return v___x_1520_;
}
else
{
lean_object* v_val_1521_; 
v_val_1521_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1521_);
lean_dec_ref_known(v___x_1519_, 1);
if (lean_obj_tag(v_val_1521_) == 1)
{
uint8_t v_v_1522_; 
v_v_1522_ = lean_ctor_get_uint8(v_val_1521_, 0);
lean_dec_ref_known(v_val_1521_, 0);
return v_v_1522_;
}
else
{
uint8_t v___x_1523_; 
lean_dec(v_val_1521_);
v___x_1523_ = lean_unbox(v_defValue_1517_);
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1524_, lean_object* v_opt_1525_){
_start:
{
uint8_t v_res_1526_; lean_object* v_r_1527_; 
v_res_1526_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1524_, v_opt_1525_);
lean_dec_ref(v_opt_1525_);
lean_dec_ref(v_opts_1524_);
v_r_1527_ = lean_box(v_res_1526_);
return v_r_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1529_, lean_object* v_msgData_1530_, uint8_t v_severity_1531_, uint8_t v_isSilent_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_a_1538_; uint8_t v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; uint8_t v___y_1547_; lean_object* v___y_1548_; lean_object* v_toCold_1549_; lean_object* v___y_1550_; lean_object* v___y_1578_; lean_object* v___y_1579_; uint8_t v___y_1580_; lean_object* v___y_1581_; uint8_t v___y_1582_; uint8_t v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1604_; uint8_t v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; uint8_t v___y_1609_; lean_object* v___y_1610_; uint8_t v___y_1614_; uint8_t v___y_1615_; uint8_t v___x_1625_; uint8_t v___y_1627_; uint8_t v___x_1633_; 
v___x_1625_ = 2;
v___x_1633_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1531_, v___x_1625_);
if (v___x_1633_ == 0)
{
v___y_1627_ = v___x_1633_;
goto v___jp_1626_;
}
else
{
uint8_t v___x_1634_; 
lean_inc_ref(v_msgData_1530_);
v___x_1634_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1530_);
if (v___x_1634_ == 0)
{
v___y_1627_ = v___x_1634_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref(v_msgData_1530_);
v___x_1635_ = lean_box(0);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___y_1533_);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
return v___x_1637_;
}
}
v___jp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_a_1538_);
lean_ctor_set(v___x_1539_, 1, v___y_1533_);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
v___jp_1541_:
{
lean_object* v_currNamespace_1551_; lean_object* v_openDecls_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_env_1557_; lean_object* v_nextMacroScope_1558_; lean_object* v_ngen_1559_; lean_object* v_auxDeclNGen_1560_; lean_object* v_traceState_1561_; lean_object* v_cache_1562_; lean_object* v_recordedDeps_1563_; lean_object* v_messages_1564_; lean_object* v_infoState_1565_; lean_object* v_snapshotTasks_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1576_; 
v_currNamespace_1551_ = lean_ctor_get(v_toCold_1549_, 4);
v_openDecls_1552_ = lean_ctor_get(v_toCold_1549_, 5);
lean_inc(v_openDecls_1552_);
lean_inc(v_currNamespace_1551_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_currNamespace_1551_);
lean_ctor_set(v___x_1553_, 1, v_openDecls_1552_);
v___x_1554_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___y_1546_);
lean_inc_ref(v___y_1543_);
lean_inc_ref(v___y_1544_);
v___x_1555_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1555_, 0, v___y_1544_);
lean_ctor_set(v___x_1555_, 1, v___y_1545_);
lean_ctor_set(v___x_1555_, 2, v___y_1548_);
lean_ctor_set(v___x_1555_, 3, v___y_1543_);
lean_ctor_set(v___x_1555_, 4, v___x_1554_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*5, v___y_1547_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*5 + 1, v___y_1542_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*5 + 2, v_isSilent_1532_);
v___x_1556_ = lean_st_ref_take(v___y_1550_);
v_env_1557_ = lean_ctor_get(v___x_1556_, 0);
v_nextMacroScope_1558_ = lean_ctor_get(v___x_1556_, 1);
v_ngen_1559_ = lean_ctor_get(v___x_1556_, 2);
v_auxDeclNGen_1560_ = lean_ctor_get(v___x_1556_, 3);
v_traceState_1561_ = lean_ctor_get(v___x_1556_, 4);
v_cache_1562_ = lean_ctor_get(v___x_1556_, 5);
v_recordedDeps_1563_ = lean_ctor_get(v___x_1556_, 6);
v_messages_1564_ = lean_ctor_get(v___x_1556_, 7);
v_infoState_1565_ = lean_ctor_get(v___x_1556_, 8);
v_snapshotTasks_1566_ = lean_ctor_get(v___x_1556_, 9);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1568_ = v___x_1556_;
v_isShared_1569_ = v_isSharedCheck_1576_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_snapshotTasks_1566_);
lean_inc(v_infoState_1565_);
lean_inc(v_messages_1564_);
lean_inc(v_recordedDeps_1563_);
lean_inc(v_cache_1562_);
lean_inc(v_traceState_1561_);
lean_inc(v_auxDeclNGen_1560_);
lean_inc(v_ngen_1559_);
lean_inc(v_nextMacroScope_1558_);
lean_inc(v_env_1557_);
lean_dec(v___x_1556_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1576_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1570_ = lean_box(0);
v___x_1571_ = l_Lean_MessageLog_add(v___x_1555_, v_messages_1564_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 7, v___x_1571_);
v___x_1573_ = v___x_1568_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_env_1557_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_nextMacroScope_1558_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_ngen_1559_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_auxDeclNGen_1560_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_traceState_1561_);
lean_ctor_set(v_reuseFailAlloc_1575_, 5, v_cache_1562_);
lean_ctor_set(v_reuseFailAlloc_1575_, 6, v_recordedDeps_1563_);
lean_ctor_set(v_reuseFailAlloc_1575_, 7, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1575_, 8, v_infoState_1565_);
lean_ctor_set(v_reuseFailAlloc_1575_, 9, v_snapshotTasks_1566_);
v___x_1573_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_st_ref_put(v___y_1550_, v___x_1573_);
v_a_1538_ = v___x_1570_;
goto v___jp_1537_;
}
}
}
v___jp_1577_:
{
lean_object* v_fileName_1586_; lean_object* v_fileMap_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1602_; 
v_fileName_1586_ = lean_ctor_get(v___y_1584_, 0);
v_fileMap_1587_ = lean_ctor_get(v___y_1584_, 1);
v___x_1588_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1530_);
v___x_1589_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1588_, v___y_1534_, v___y_1535_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1602_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1602_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_inc_ref_n(v_fileMap_1587_, 2);
v___x_1594_ = l_Lean_FileMap_toPosition(v_fileMap_1587_, v___y_1581_);
lean_dec(v___y_1581_);
v___x_1595_ = l_Lean_FileMap_toPosition(v_fileMap_1587_, v___y_1585_);
lean_dec(v___y_1585_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 1);
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
v___x_1598_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1582_ == 0)
{
lean_dec_ref(v___y_1578_);
v___y_1542_ = v___y_1580_;
v___y_1543_ = v___x_1598_;
v___y_1544_ = v_fileName_1586_;
v___y_1545_ = v___x_1594_;
v___y_1546_ = v_a_1590_;
v___y_1547_ = v___y_1583_;
v___y_1548_ = v___x_1597_;
v_toCold_1549_ = v___y_1579_;
v___y_1550_ = v___y_1535_;
goto v___jp_1541_;
}
else
{
uint8_t v___x_1599_; 
lean_inc(v_a_1590_);
v___x_1599_ = l_Lean_MessageData_hasTag(v___y_1578_, v_a_1590_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
lean_dec_ref(v___x_1597_);
lean_dec_ref(v___x_1594_);
lean_dec(v_a_1590_);
v___x_1600_ = lean_box(0);
v_a_1538_ = v___x_1600_;
goto v___jp_1537_;
}
else
{
v___y_1542_ = v___y_1580_;
v___y_1543_ = v___x_1598_;
v___y_1544_ = v_fileName_1586_;
v___y_1545_ = v___x_1594_;
v___y_1546_ = v_a_1590_;
v___y_1547_ = v___y_1583_;
v___y_1548_ = v___x_1597_;
v_toCold_1549_ = v___y_1579_;
v___y_1550_ = v___y_1535_;
goto v___jp_1541_;
}
}
}
}
}
v___jp_1603_:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Syntax_getTailPos_x3f(v___y_1607_, v___y_1609_);
lean_dec(v___y_1607_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_inc(v___y_1610_);
v___y_1578_ = v___y_1604_;
v___y_1579_ = v___y_1606_;
v___y_1580_ = v___y_1608_;
v___y_1581_ = v___y_1610_;
v___y_1582_ = v___y_1605_;
v___y_1583_ = v___y_1609_;
v___y_1584_ = v___y_1606_;
v___y_1585_ = v___y_1610_;
goto v___jp_1577_;
}
else
{
lean_object* v_val_1612_; 
v_val_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___y_1578_ = v___y_1604_;
v___y_1579_ = v___y_1606_;
v___y_1580_ = v___y_1608_;
v___y_1581_ = v___y_1610_;
v___y_1582_ = v___y_1605_;
v___y_1583_ = v___y_1609_;
v___y_1584_ = v___y_1606_;
v___y_1585_ = v_val_1612_;
goto v___jp_1577_;
}
}
v___jp_1613_:
{
lean_object* v_toCold_1616_; lean_object* v_ref_1617_; uint8_t v_suppressElabErrors_1618_; lean_object* v___x_1619_; lean_object* v___f_1620_; lean_object* v_ref_1621_; lean_object* v___x_1622_; 
v_toCold_1616_ = lean_ctor_get(v___y_1534_, 0);
v_ref_1617_ = lean_ctor_get(v___y_1534_, 2);
v_suppressElabErrors_1618_ = lean_ctor_get_uint8(v___y_1534_, sizeof(void*)*3 + 2);
v___x_1619_ = lean_box(v_suppressElabErrors_1618_);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1620_, 0, v___x_1619_);
v_ref_1621_ = l_Lean_replaceRef(v_ref_1529_, v_ref_1617_);
v___x_1622_ = l_Lean_Syntax_getPos_x3f(v_ref_1621_, v___y_1614_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_unsigned_to_nat(0u);
v___y_1604_ = v___f_1620_;
v___y_1605_ = v_suppressElabErrors_1618_;
v___y_1606_ = v_toCold_1616_;
v___y_1607_ = v_ref_1621_;
v___y_1608_ = v___y_1615_;
v___y_1609_ = v___y_1614_;
v___y_1610_ = v___x_1623_;
goto v___jp_1603_;
}
else
{
lean_object* v_val_1624_; 
v_val_1624_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v___x_1622_, 1);
v___y_1604_ = v___f_1620_;
v___y_1605_ = v_suppressElabErrors_1618_;
v___y_1606_ = v_toCold_1616_;
v___y_1607_ = v_ref_1621_;
v___y_1608_ = v___y_1615_;
v___y_1609_ = v___y_1614_;
v___y_1610_ = v_val_1624_;
goto v___jp_1603_;
}
}
v___jp_1626_:
{
uint8_t v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = 1;
v___x_1629_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1531_, v___x_1628_);
if (v___x_1629_ == 0)
{
v___y_1614_ = v___y_1627_;
v___y_1615_ = v_severity_1531_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1630_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1534_);
v___x_1631_ = l_Lean_warningAsError;
v___x_1632_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v___x_1630_, v___x_1631_);
lean_dec_ref(v___x_1630_);
if (v___x_1632_ == 0)
{
v___y_1614_ = v___y_1627_;
v___y_1615_ = v_severity_1531_;
goto v___jp_1613_;
}
else
{
v___y_1614_ = v___y_1627_;
v___y_1615_ = v___x_1625_;
goto v___jp_1613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1638_, lean_object* v_msgData_1639_, lean_object* v_severity_1640_, lean_object* v_isSilent_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v_severity_boxed_1646_; uint8_t v_isSilent_boxed_1647_; lean_object* v_res_1648_; 
v_severity_boxed_1646_ = lean_unbox(v_severity_1640_);
v_isSilent_boxed_1647_ = lean_unbox(v_isSilent_1641_);
v_res_1648_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1638_, v_msgData_1639_, v_severity_boxed_1646_, v_isSilent_boxed_1647_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v_ref_1638_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1649_, lean_object* v_msgData_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
uint8_t v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = 2;
v___x_1656_ = 0;
v___x_1657_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1649_, v_msgData_1650_, v___x_1655_, v___x_1656_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1658_, lean_object* v_msgData_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1658_, v_msgData_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v_ref_1658_);
return v_res_1664_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1668_ = l_Lean_MessageData_ofFormat(v___x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1669_, lean_object* v_as_1670_, size_t v_sz_1671_, size_t v_i_1672_, uint8_t v_b_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_snd_1679_; lean_object* v_snd_1680_; lean_object* v_a_1686_; uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_lt(v_i_1672_, v_sz_1671_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_box(v_b_1673_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v___y_1674_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1710_; uint8_t v_recovering_1711_; 
v_a_1709_ = lean_array_uget_borrowed(v_as_1670_, v_i_1672_);
v___x_1710_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1709_);
v_recovering_1711_ = l_Lean_Syntax_isOfKind(v_a_1709_, v___x_1710_);
if (v_recovering_1711_ == 0)
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_a_1709_);
v___x_1713_ = l_Lean_Syntax_isOfKind(v_a_1709_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1709_);
v___x_1715_ = l_Lean_Syntax_isOfKind(v_a_1709_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1674_);
v___x_1717_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1709_, v___x_1716_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v_snd_1719_; lean_object* v___x_1720_; 
lean_dec_ref(v___y_1674_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v_snd_1719_ = lean_ctor_get(v_a_1718_, 1);
lean_inc(v_snd_1719_);
lean_dec(v_a_1718_);
v___x_1720_ = lean_box(v_b_1673_);
v_snd_1679_ = v___x_1720_;
v_snd_1680_ = v_snd_1719_;
goto v___jp_1678_;
}
else
{
lean_object* v_a_1721_; 
v_a_1721_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1717_, 1);
v_a_1686_ = v_a_1721_;
goto v___jp_1685_;
}
}
else
{
lean_object* v___x_1722_; 
lean_inc_ref(v___y_1674_);
lean_inc(v_a_1709_);
v___x_1722_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1709_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v_snd_1724_; lean_object* v___x_1725_; 
lean_dec_ref(v___y_1674_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v_snd_1724_ = lean_ctor_get(v_a_1723_, 1);
lean_inc(v_snd_1724_);
lean_dec(v_a_1723_);
v___x_1725_ = lean_box(v_recovering_1711_);
v_snd_1679_ = v___x_1725_;
v_snd_1680_ = v_snd_1724_;
goto v___jp_1678_;
}
else
{
lean_object* v_a_1726_; 
v_a_1726_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1722_, 1);
v_a_1686_ = v_a_1726_;
goto v___jp_1685_;
}
}
}
else
{
lean_object* v___x_1727_; 
lean_inc_ref(v___y_1674_);
lean_inc(v_a_1709_);
v___x_1727_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1709_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v_snd_1729_; lean_object* v___x_1730_; 
lean_dec_ref(v___y_1674_);
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v_snd_1729_ = lean_ctor_get(v_a_1728_, 1);
lean_inc(v_snd_1729_);
lean_dec(v_a_1728_);
v___x_1730_ = lean_box(v_recovering_1711_);
v_snd_1679_ = v___x_1730_;
v_snd_1680_ = v_snd_1729_;
goto v___jp_1678_;
}
else
{
lean_object* v_a_1731_; 
v_a_1731_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1727_, 1);
v_a_1686_ = v_a_1731_;
goto v___jp_1685_;
}
}
}
else
{
if (v_b_1673_ == 0)
{
lean_object* v___x_1732_; 
lean_inc_ref(v___y_1674_);
lean_inc(v_a_1709_);
v___x_1732_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1709_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v_snd_1734_; lean_object* v___x_1735_; 
lean_dec_ref(v___y_1674_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v_snd_1734_ = lean_ctor_get(v_a_1733_, 1);
lean_inc(v_snd_1734_);
lean_dec(v_a_1733_);
v___x_1735_ = lean_box(v_b_1673_);
v_snd_1679_ = v___x_1735_;
v_snd_1680_ = v_snd_1734_;
goto v___jp_1678_;
}
else
{
lean_object* v_a_1736_; 
v_a_1736_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1732_, 1);
v_a_1686_ = v_a_1736_;
goto v___jp_1685_;
}
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_box(v_b_1673_);
v_snd_1679_ = v___x_1737_;
v_snd_1680_ = v___y_1674_;
goto v___jp_1678_;
}
}
}
v___jp_1678_:
{
size_t v___x_1681_; size_t v___x_1682_; uint8_t v___x_1683_; 
v___x_1681_ = ((size_t)1ULL);
v___x_1682_ = lean_usize_add(v_i_1672_, v___x_1681_);
v___x_1683_ = lean_unbox(v_snd_1679_);
lean_dec(v_snd_1679_);
v_i_1672_ = v___x_1682_;
v_b_1673_ = v___x_1683_;
v___y_1674_ = v_snd_1680_;
goto _start;
}
v___jp_1685_:
{
uint8_t v___x_1687_; 
v___x_1687_ = l_Lean_Exception_isInterrupt(v_a_1686_);
if (v___x_1687_ == 0)
{
uint8_t v___x_1688_; 
lean_inc_ref(v_a_1686_);
v___x_1688_ = l_Lean_Exception_isRuntime(v_a_1686_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = l_Lean_Exception_getRef(v_a_1686_);
v___x_1690_ = l_Lean_Exception_toMessageData(v_a_1686_);
v___x_1691_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1689_, v___x_1690_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___x_1689_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v_snd_1693_; lean_object* v___x_1694_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v_snd_1693_ = lean_ctor_get(v_a_1692_, 1);
lean_inc(v_snd_1693_);
lean_dec(v_a_1692_);
v___x_1694_ = lean_box(v_recovering_1669_);
v_snd_1679_ = v___x_1694_;
v_snd_1680_ = v_snd_1693_;
goto v___jp_1678_;
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1695_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1691_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1691_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v___x_1703_; 
lean_dec_ref(v___y_1674_);
v___x_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_a_1686_);
return v___x_1703_;
}
}
else
{
lean_object* v___x_1704_; 
lean_dec_ref(v___y_1674_);
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_a_1686_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1738_, lean_object* v_as_1739_, lean_object* v_sz_1740_, lean_object* v_i_1741_, lean_object* v_b_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
uint8_t v_recovering_boxed_1747_; size_t v_sz_boxed_1748_; size_t v_i_boxed_1749_; uint8_t v_b_boxed_1750_; lean_object* v_res_1751_; 
v_recovering_boxed_1747_ = lean_unbox(v_recovering_1738_);
v_sz_boxed_1748_ = lean_unbox_usize(v_sz_1740_);
lean_dec(v_sz_1740_);
v_i_boxed_1749_ = lean_unbox_usize(v_i_1741_);
lean_dec(v_i_1741_);
v_b_boxed_1750_ = lean_unbox(v_b_1742_);
v_res_1751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1747_, v_as_1739_, v_sz_boxed_1748_, v_i_boxed_1749_, v_b_boxed_1750_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_as_1739_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_ref_1756_; lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_ref_1756_ = lean_ctor_get(v___y_1753_, 2);
v___x_1757_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1752_, v___y_1753_, v___y_1754_);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_inc(v_ref_1756_);
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v_ref_1756_);
lean_ctor_set(v___x_1762_, 1, v_a_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1772_, lean_object* v_msg_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_toCold_1777_; lean_object* v_currRecDepth_1778_; lean_object* v_ref_1779_; uint16_t v_optionFlags_1780_; uint8_t v_suppressElabErrors_1781_; uint8_t v_isRecordingDeps_1782_; lean_object* v_ref_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_toCold_1777_ = lean_ctor_get(v___y_1774_, 0);
v_currRecDepth_1778_ = lean_ctor_get(v___y_1774_, 1);
v_ref_1779_ = lean_ctor_get(v___y_1774_, 2);
v_optionFlags_1780_ = lean_ctor_get_uint16(v___y_1774_, sizeof(void*)*3);
v_suppressElabErrors_1781_ = lean_ctor_get_uint8(v___y_1774_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1782_ = lean_ctor_get_uint8(v___y_1774_, sizeof(void*)*3 + 3);
v_ref_1783_ = l_Lean_replaceRef(v_ref_1772_, v_ref_1779_);
lean_inc(v_currRecDepth_1778_);
lean_inc_ref(v_toCold_1777_);
v___x_1784_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1784_, 0, v_toCold_1777_);
lean_ctor_set(v___x_1784_, 1, v_currRecDepth_1778_);
lean_ctor_set(v___x_1784_, 2, v_ref_1783_);
lean_ctor_set_uint16(v___x_1784_, sizeof(void*)*3, v_optionFlags_1780_);
lean_ctor_set_uint8(v___x_1784_, sizeof(void*)*3 + 2, v_suppressElabErrors_1781_);
lean_ctor_set_uint8(v___x_1784_, sizeof(void*)*3 + 3, v_isRecordingDeps_1782_);
v___x_1785_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1773_, v___x_1784_, v___y_1775_);
lean_dec_ref_known(v___x_1784_, 3);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1786_, lean_object* v_msg_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1786_, v_msg_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_ref_1786_);
return v_res_1791_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1804_);
v___x_1809_ = l_Lean_Syntax_isOfKind(v_x_1804_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1811_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1804_, v___x_1810_, v_a_1805_, v_a_1806_);
lean_dec(v_x_1804_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v_recovering_1815_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = l_Lean_Syntax_getArg(v_x_1804_, v___x_1812_);
v___x_1814_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1815_ = l_Lean_Syntax_isOfKind(v___x_1813_, v___x_1814_);
if (v_recovering_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1817_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1804_, v___x_1816_, v_a_1805_, v_a_1806_);
lean_dec(v_x_1804_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v_xs_1820_; uint8_t v_recovering_1821_; lean_object* v___x_1822_; size_t v_sz_1823_; size_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1818_ = lean_unsigned_to_nat(1u);
v___x_1819_ = l_Lean_Syntax_getArg(v_x_1804_, v___x_1818_);
lean_dec(v_x_1804_);
v_xs_1820_ = l_Lean_Syntax_getArgs(v___x_1819_);
lean_dec(v___x_1819_);
v_recovering_1821_ = 0;
v___x_1822_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1820_);
lean_dec_ref(v_xs_1820_);
v_sz_1823_ = lean_array_size(v___x_1822_);
v___x_1824_ = ((size_t)0ULL);
v___x_1825_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1815_, v___x_1822_, v_sz_1823_, v___x_1824_, v_recovering_1821_, v___x_1825_, v_a_1805_, v_a_1806_);
lean_dec_ref(v___x_1822_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1837_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_snd_1831_; lean_object* v_items_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v_snd_1831_ = lean_ctor_get(v_a_1827_, 1);
lean_inc(v_snd_1831_);
lean_dec(v_a_1827_);
v_items_1832_ = lean_ctor_get(v_snd_1831_, 5);
lean_inc_ref(v_items_1832_);
lean_dec(v_snd_1831_);
v___x_1833_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1832_);
lean_dec_ref(v_items_1832_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1833_);
v___x_1835_ = v___x_1829_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1826_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1826_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lake_Toml_elabToml(v_x_1846_, v_a_1847_, v_a_1848_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1851_, lean_object* v_ref_1852_, lean_object* v_msg_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1852_, v_msg_1853_, v___y_1854_, v___y_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1858_, lean_object* v_ref_1859_, lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1858_, v_ref_1859_, v_msg_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v_ref_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1865_, lean_object* v_msg_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1866_, v___y_1867_, v___y_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1871_, v_msg_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1876_;
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
