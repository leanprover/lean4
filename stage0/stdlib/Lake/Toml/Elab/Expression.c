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
lean_object* v_toCold_188_; lean_object* v_currRecDepth_189_; lean_object* v_ref_190_; uint16_t v_optionFlags_191_; uint8_t v_suppressElabErrors_192_; uint8_t v_checkDeprecated_193_; uint8_t v_isRecordingDeps_194_; lean_object* v_ref_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_toCold_188_ = lean_ctor_get(v___y_185_, 0);
v_currRecDepth_189_ = lean_ctor_get(v___y_185_, 1);
v_ref_190_ = lean_ctor_get(v___y_185_, 2);
v_optionFlags_191_ = lean_ctor_get_uint16(v___y_185_, sizeof(void*)*3);
v_suppressElabErrors_192_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 2);
v_checkDeprecated_193_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 3);
v_isRecordingDeps_194_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 4);
v_ref_195_ = l_Lean_replaceRef(v_ref_182_, v_ref_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_toCold_188_);
v___x_196_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_196_, 0, v_toCold_188_);
lean_ctor_set(v___x_196_, 1, v_currRecDepth_189_);
lean_ctor_set(v___x_196_, 2, v_ref_195_);
lean_ctor_set_uint16(v___x_196_, sizeof(void*)*3, v_optionFlags_191_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3 + 2, v_suppressElabErrors_192_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3 + 3, v_checkDeprecated_193_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3 + 4, v_isRecordingDeps_194_);
v___x_197_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_183_, v___x_196_, v___y_186_);
lean_dec_ref_known(v___x_196_, 3);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object* v_ref_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_198_, v_msg_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v_ref_198_);
return v_res_204_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object* v_as_214_, size_t v_i_215_, size_t v_stop_216_, lean_object* v_b_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_fst_223_; lean_object* v_snd_224_; uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_eq(v_i_215_, v_stop_216_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_array_uget_borrowed(v_as_214_, v_i_215_);
lean_inc(v___x_229_);
v___x_230_ = l_Lake_Toml_elabSimpleKey(v___x_229_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_keyTys_232_; lean_object* v_arrKeyTys_233_; lean_object* v_arrParents_234_; lean_object* v_currArrKey_235_; lean_object* v_currKey_236_; lean_object* v_items_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v_keyTys_232_ = lean_ctor_get(v___y_218_, 0);
v_arrKeyTys_233_ = lean_ctor_get(v___y_218_, 1);
v_arrParents_234_ = lean_ctor_get(v___y_218_, 2);
v_currArrKey_235_ = lean_ctor_get(v___y_218_, 3);
v_currKey_236_ = lean_ctor_get(v___y_218_, 4);
v_items_237_ = lean_ctor_get(v___y_218_, 5);
v___x_238_ = l_Lean_Name_str___override(v_b_217_, v_a_231_);
v___x_239_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_232_, v___x_238_);
if (lean_obj_tag(v___x_239_) == 1)
{
lean_object* v_val_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_270_; 
v_val_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_270_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_270_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_val_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_270_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
uint8_t v___x_244_; 
v___x_244_ = lean_unbox(v_val_240_);
if (v___x_244_ == 3)
{
lean_del_object(v___x_242_);
lean_dec(v_val_240_);
v_fst_223_ = v___x_238_;
v_snd_224_ = v___y_218_;
goto v___jp_222_;
}
else
{
lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_245_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_246_ = lean_unbox(v_val_240_);
lean_dec(v_val_240_);
v___x_247_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_246_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 3);
lean_ctor_set(v___x_242_, 0, v___x_247_);
v___x_249_ = v___x_242_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_269_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_250_ = l_Lean_MessageData_ofFormat(v___x_249_);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_245_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
lean_inc(v___x_238_);
v___x_254_ = l_Lean_MessageData_ofName(v___x_238_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_229_, v___x_257_, v___y_218_, v___y_219_, v___y_220_);
lean_dec_ref(v___y_218_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v_snd_260_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v___x_258_, 1);
v_snd_260_ = lean_ctor_get(v_a_259_, 1);
lean_inc(v_snd_260_);
lean_dec(v_a_259_);
v_fst_223_ = v___x_238_;
v_snd_224_ = v_snd_260_;
goto v___jp_222_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v___x_238_);
v_a_261_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_258_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_258_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_280_; 
lean_inc_ref(v_items_237_);
lean_inc(v_currKey_236_);
lean_inc(v_currArrKey_235_);
lean_inc(v_arrParents_234_);
lean_inc(v_arrKeyTys_233_);
lean_inc(v_keyTys_232_);
lean_dec(v___x_239_);
v_isSharedCheck_280_ = !lean_is_exclusive(v___y_218_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; 
v_unused_281_ = lean_ctor_get(v___y_218_, 5);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v___y_218_, 4);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v___y_218_, 3);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v___y_218_, 2);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v___y_218_, 1);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v___y_218_, 0);
lean_dec(v_unused_286_);
v___x_272_ = v___y_218_;
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___y_218_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_274_ = 3;
v___x_275_ = lean_box(v___x_274_);
lean_inc(v___x_238_);
v___x_276_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_238_, v___x_275_, v_keyTys_232_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_276_);
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_arrKeyTys_233_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_arrParents_234_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_currArrKey_235_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_currKey_236_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_items_237_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
v_fst_223_ = v___x_238_;
v_snd_224_ = v___x_278_;
goto v___jp_222_;
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v___y_218_);
lean_dec(v_b_217_);
v_a_287_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_230_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_230_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_b_217_);
lean_ctor_set(v___x_295_, 1, v___y_218_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
v___jp_222_:
{
size_t v___x_225_; size_t v___x_226_; 
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_add(v_i_215_, v___x_225_);
v_i_215_ = v___x_226_;
v_b_217_ = v_fst_223_;
v___y_218_ = v_snd_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object* v_as_297_, lean_object* v_i_298_, lean_object* v_stop_299_, lean_object* v_b_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
size_t v_i_boxed_305_; size_t v_stop_boxed_306_; lean_object* v_res_307_; 
v_i_boxed_305_ = lean_unbox_usize(v_i_298_);
lean_dec(v_i_298_);
v_stop_boxed_306_ = lean_unbox_usize(v_stop_299_);
lean_dec(v_stop_299_);
v_res_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_297_, v_i_boxed_305_, v_stop_boxed_306_, v_b_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec_ref(v_as_297_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object* v_ks_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_currKey_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_currKey_313_ = lean_ctor_get(v_a_309_, 4);
lean_inc(v_currKey_313_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_array_get_size(v_ks_308_);
v___x_316_ = lean_nat_dec_lt(v___x_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_currKey_313_);
lean_ctor_set(v___x_317_, 1, v_a_309_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
else
{
size_t v___x_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_of_nat(v___x_315_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_308_, v___x_319_, v___x_320_, v_currKey_313_, v_a_309_, v_a_310_, v_a_311_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object* v_ks_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_322_, v_a_323_, v_a_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec_ref(v_ks_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_328_, lean_object* v_ref_329_, lean_object* v_msg_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_329_, v_msg_330_, v___y_331_, v___y_332_, v___y_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_336_, lean_object* v_ref_337_, lean_object* v_msg_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_336_, v_ref_337_, v_msg_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v_ref_337_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_345_, v___y_347_, v___y_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_351_, lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_351_, v_msg_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_358_, lean_object* v_as_359_, size_t v_i_360_, size_t v_stop_361_, lean_object* v_b_362_){
_start:
{
lean_object* v___y_364_; uint8_t v___x_368_; 
v___x_368_ = lean_usize_dec_eq(v_i_360_, v_stop_361_);
if (v___x_368_ == 0)
{
lean_object* v_fst_369_; uint8_t v___x_370_; 
v_fst_369_ = lean_ctor_get(v_b_362_, 0);
v___x_370_ = lean_unbox(v_fst_369_);
if (v___x_370_ == 0)
{
lean_object* v_snd_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
v_snd_371_ = lean_ctor_get(v_b_362_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_b_362_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v_b_362_, 0);
lean_dec(v_unused_380_);
v___x_373_ = v_b_362_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_snd_371_);
lean_dec(v_b_362_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_box(v___x_358_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_snd_371_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
v___y_364_ = v___x_377_;
goto v___jp_363_;
}
}
}
else
{
lean_object* v_snd_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_391_; 
v_snd_381_ = lean_ctor_get(v_b_362_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_b_362_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_b_362_, 0);
lean_dec(v_unused_392_);
v___x_383_ = v_b_362_;
v_isShared_384_ = v_isSharedCheck_391_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snd_381_);
lean_dec(v_b_362_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_391_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_385_ = lean_array_uget_borrowed(v_as_359_, v_i_360_);
lean_inc(v___x_385_);
v___x_386_ = lean_array_push(v_snd_381_, v___x_385_);
v___x_387_ = lean_box(v___x_368_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v___x_386_);
lean_ctor_set(v___x_383_, 0, v___x_387_);
v___x_389_ = v___x_383_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_386_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
v___y_364_ = v___x_389_;
goto v___jp_363_;
}
}
}
}
else
{
return v_b_362_;
}
v___jp_363_:
{
size_t v___x_365_; size_t v___x_366_; 
v___x_365_ = ((size_t)1ULL);
v___x_366_ = lean_usize_add(v_i_360_, v___x_365_);
v_i_360_ = v___x_366_;
v_b_362_ = v___y_364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_393_, lean_object* v_as_394_, lean_object* v_i_395_, lean_object* v_stop_396_, lean_object* v_b_397_){
_start:
{
uint8_t v___x_2936__boxed_398_; size_t v_i_boxed_399_; size_t v_stop_boxed_400_; lean_object* v_res_401_; 
v___x_2936__boxed_398_ = lean_unbox(v___x_393_);
v_i_boxed_399_ = lean_unbox_usize(v_i_395_);
lean_dec(v_i_395_);
v_stop_boxed_400_ = lean_unbox_usize(v_stop_396_);
lean_dec(v_stop_396_);
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2936__boxed_398_, v_as_394_, v_i_boxed_399_, v_stop_boxed_400_, v_b_397_);
lean_dec_ref(v_as_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_409_, size_t v_i_410_, lean_object* v_bs_411_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = lean_usize_dec_lt(v_i_410_, v_sz_409_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
v___x_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_413_, 0, v_bs_411_);
return v___x_413_;
}
else
{
lean_object* v_v_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_v_414_ = lean_array_uget(v_bs_411_, v_i_410_);
v___x_415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_414_);
v___x_416_ = l_Lean_Syntax_isOfKind(v_v_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_dec(v_v_414_);
lean_dec_ref(v_bs_411_);
v___x_417_ = lean_box(0);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v_bs_x27_419_; size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v_bs_x27_419_ = lean_array_uset(v_bs_411_, v_i_410_, v___x_418_);
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_add(v_i_410_, v___x_420_);
v___x_422_ = lean_array_uset(v_bs_x27_419_, v_i_410_, v_v_414_);
v_i_410_ = v___x_421_;
v_bs_411_ = v___x_422_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_424_, lean_object* v_i_425_, lean_object* v_bs_426_){
_start:
{
size_t v_sz_boxed_427_; size_t v_i_boxed_428_; lean_object* v_res_429_; 
v_sz_boxed_427_ = lean_unbox_usize(v_sz_424_);
lean_dec(v_sz_424_);
v_i_boxed_428_ = lean_unbox_usize(v_i_425_);
lean_dec(v_i_425_);
v_res_429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_427_, v_i_boxed_428_, v_bs_426_);
return v_res_429_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_437_ = l_Lean_stringToMessageData(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_445_ = l_Lean_stringToMessageData(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_448_);
v___x_454_ = l_Lean_Syntax_isOfKind(v_kv_448_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_456_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_448_, v___x_455_, v_a_449_, v_a_450_, v_a_451_);
lean_dec_ref(v_a_449_);
lean_dec(v_kv_448_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = l_Lean_Syntax_getArg(v_kv_448_, v___x_457_);
v___x_459_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_458_);
v___x_460_ = l_Lean_Syntax_isOfKind(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec(v_kv_448_);
v___x_461_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_462_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_458_, v___x_461_, v_a_449_, v_a_450_, v_a_451_);
lean_dec_ref(v_a_449_);
lean_dec(v___x_458_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v_v_464_; lean_object* v___y_466_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_463_ = lean_unsigned_to_nat(2u);
v_v_464_ = l_Lean_Syntax_getArg(v_kv_448_, v___x_463_);
lean_dec(v_kv_448_);
v___x_572_ = l_Lean_Syntax_getArg(v___x_458_, v___x_457_);
v___x_573_ = l_Lean_Syntax_getArgs(v___x_572_);
lean_dec(v___x_572_);
v___x_574_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_575_ = lean_array_get_size(v___x_573_);
v___x_576_ = lean_nat_dec_lt(v___x_457_, v___x_575_);
if (v___x_576_ == 0)
{
lean_dec_ref(v___x_573_);
v___y_466_ = v___x_574_;
goto v___jp_465_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; lean_object* v_snd_582_; 
v___x_577_ = lean_box(v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_574_);
v___x_579_ = ((size_t)0ULL);
v___x_580_ = lean_usize_of_nat(v___x_575_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_460_, v___x_573_, v___x_579_, v___x_580_, v___x_578_);
lean_dec_ref(v___x_573_);
v_snd_582_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_snd_582_);
lean_dec_ref(v___x_581_);
v___y_466_ = v_snd_582_;
goto v___jp_465_;
}
v___jp_465_:
{
size_t v_sz_467_; size_t v___x_468_; lean_object* v___x_469_; 
v_sz_467_ = lean_array_size(v___y_466_);
v___x_468_ = ((size_t)0ULL);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_467_, v___x_468_, v___y_466_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v_v_464_);
v___x_470_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_471_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_458_, v___x_470_, v_a_449_, v_a_450_, v_a_451_);
lean_dec_ref(v_a_449_);
lean_dec(v___x_458_);
return v___x_471_;
}
else
{
lean_object* v_val_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_tailKeyStx_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_val_472_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___x_469_, 1);
v___x_473_ = lean_box(0);
v___x_474_ = lean_array_get_size(v_val_472_);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_sub(v___x_474_, v___x_475_);
v_tailKeyStx_477_ = lean_array_get(v___x_473_, v_val_472_, v___x_476_);
lean_dec(v___x_476_);
v___x_478_ = lean_array_pop(v_val_472_);
v___x_479_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_478_, v_a_449_, v_a_450_, v_a_451_);
lean_dec_ref(v___x_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v_fst_481_; lean_object* v_snd_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_563_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v_fst_481_ = lean_ctor_get(v_a_480_, 0);
v_snd_482_ = lean_ctor_get(v_a_480_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_563_ == 0)
{
v___x_484_ = v_a_480_;
v_isShared_485_ = v_isSharedCheck_563_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snd_482_);
lean_inc(v_fst_481_);
lean_dec(v_a_480_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_563_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; 
lean_inc(v_tailKeyStx_477_);
v___x_486_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_477_, v_a_450_, v_a_451_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v_keyTys_488_; lean_object* v_arrKeyTys_489_; lean_object* v_arrParents_490_; lean_object* v_currArrKey_491_; lean_object* v_currKey_492_; lean_object* v_items_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
v_keyTys_488_ = lean_ctor_get(v_snd_482_, 0);
v_arrKeyTys_489_ = lean_ctor_get(v_snd_482_, 1);
v_arrParents_490_ = lean_ctor_get(v_snd_482_, 2);
v_currArrKey_491_ = lean_ctor_get(v_snd_482_, 3);
v_currKey_492_ = lean_ctor_get(v_snd_482_, 4);
v_items_493_ = lean_ctor_get(v_snd_482_, 5);
v___x_494_ = l_Lean_Name_str___override(v_fst_481_, v_a_487_);
v___x_495_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_488_, v___x_494_);
if (lean_obj_tag(v___x_495_) == 1)
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_515_; 
lean_del_object(v___x_484_);
lean_dec(v_v_464_);
lean_dec(v___x_458_);
v_val_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_515_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_515_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_515_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_500_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_501_ = lean_unbox(v_val_496_);
lean_dec(v_val_496_);
v___x_502_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_501_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 3);
lean_ctor_set(v___x_498_, 0, v___x_502_);
v___x_504_ = v___x_498_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_514_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_505_ = l_Lean_MessageData_ofFormat(v___x_504_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_500_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_MessageData_ofName(v___x_494_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_477_, v___x_512_, v_snd_482_, v_a_450_, v_a_451_);
lean_dec(v_snd_482_);
lean_dec(v_tailKeyStx_477_);
return v___x_513_;
}
}
}
else
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_548_; 
lean_inc_ref(v_items_493_);
lean_inc(v_currKey_492_);
lean_inc(v_currArrKey_491_);
lean_inc(v_arrParents_490_);
lean_inc(v_arrKeyTys_489_);
lean_inc(v_keyTys_488_);
lean_dec(v___x_495_);
lean_dec(v_tailKeyStx_477_);
v_isSharedCheck_548_ = !lean_is_exclusive(v_snd_482_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; lean_object* v_unused_552_; lean_object* v_unused_553_; lean_object* v_unused_554_; 
v_unused_549_ = lean_ctor_get(v_snd_482_, 5);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_snd_482_, 4);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_snd_482_, 3);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_snd_482_, 2);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_snd_482_, 1);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v_snd_482_, 0);
lean_dec(v_unused_554_);
v___x_517_ = v_snd_482_;
v_isShared_518_ = v_isSharedCheck_548_;
goto v_resetjp_516_;
}
else
{
lean_dec(v_snd_482_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_548_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lake_Toml_elabVal(v_v_464_, v_a_450_, v_a_451_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_539_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_539_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_524_ = lean_box(0);
v___x_525_ = 0;
v___x_526_ = lean_box(v___x_525_);
lean_inc(v___x_494_);
v___x_527_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_494_, v___x_526_, v_keyTys_488_);
v___x_528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_528_, 0, v___x_458_);
lean_ctor_set(v___x_528_, 1, v___x_494_);
lean_ctor_set(v___x_528_, 2, v_a_520_);
v___x_529_ = lean_array_push(v_items_493_, v___x_528_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 5, v___x_529_);
lean_ctor_set(v___x_517_, 0, v___x_527_);
v___x_531_ = v___x_517_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_arrKeyTys_489_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_arrParents_490_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_currArrKey_491_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_currKey_492_);
lean_ctor_set(v_reuseFailAlloc_538_, 5, v___x_529_);
v___x_531_ = v_reuseFailAlloc_538_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_531_);
lean_ctor_set(v___x_484_, 0, v___x_524_);
v___x_533_ = v___x_484_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_535_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_533_);
v___x_535_ = v___x_522_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_del_object(v___x_517_);
lean_dec(v___x_494_);
lean_dec_ref(v_items_493_);
lean_dec(v_currKey_492_);
lean_dec(v_currArrKey_491_);
lean_dec(v_arrParents_490_);
lean_dec(v_arrKeyTys_489_);
lean_dec(v_keyTys_488_);
lean_del_object(v___x_484_);
lean_dec(v___x_458_);
v_a_540_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_519_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_519_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
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
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_del_object(v___x_484_);
lean_dec(v_snd_482_);
lean_dec(v_fst_481_);
lean_dec(v_tailKeyStx_477_);
lean_dec(v_v_464_);
lean_dec(v___x_458_);
v_a_555_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_486_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_486_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
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
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_tailKeyStx_477_);
lean_dec(v_v_464_);
lean_dec(v___x_458_);
v_a_564_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_479_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_479_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
return v_res_588_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_591_ = l_Lean_stringToMessageData(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_592_, size_t v_i_593_, size_t v_stop_594_, lean_object* v_b_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_fst_601_; lean_object* v_snd_602_; uint8_t v___x_606_; 
v___x_606_ = lean_usize_dec_eq(v_i_593_, v_stop_594_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_array_uget_borrowed(v_as_592_, v_i_593_);
lean_inc(v___x_607_);
v___x_608_ = l_Lake_Toml_elabSimpleKey(v___x_607_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v_keyTys_610_; lean_object* v_arrKeyTys_611_; lean_object* v_arrParents_612_; lean_object* v_currArrKey_613_; lean_object* v_currKey_614_; lean_object* v_items_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v_keyTys_610_ = lean_ctor_get(v___y_596_, 0);
v_arrKeyTys_611_ = lean_ctor_get(v___y_596_, 1);
v_arrParents_612_ = lean_ctor_get(v___y_596_, 2);
v_currArrKey_613_ = lean_ctor_get(v___y_596_, 3);
v_currKey_614_ = lean_ctor_get(v___y_596_, 4);
v_items_615_ = lean_ctor_get(v___y_596_, 5);
v___x_616_ = l_Lean_Name_str___override(v_b_595_, v_a_609_);
v___x_617_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_610_, v___x_616_);
if (lean_obj_tag(v___x_617_) == 1)
{
lean_object* v_val_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_679_; 
v_val_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_679_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_679_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_val_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_679_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_unbox(v_val_618_);
switch(v___x_622_)
{
case 2:
{
lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_647_; 
lean_inc_ref(v_items_615_);
lean_inc(v_currKey_614_);
lean_inc(v_arrParents_612_);
lean_inc(v_arrKeyTys_611_);
lean_del_object(v___x_620_);
lean_dec(v_val_618_);
v_isSharedCheck_647_ = !lean_is_exclusive(v___y_596_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; lean_object* v_unused_649_; lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; lean_object* v_unused_653_; 
v_unused_648_ = lean_ctor_get(v___y_596_, 5);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v___y_596_, 4);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v___y_596_, 3);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v___y_596_, 2);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v___y_596_, 1);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v___y_596_, 0);
lean_dec(v_unused_653_);
v___x_624_ = v___y_596_;
v_isShared_625_ = v_isSharedCheck_647_;
goto v_resetjp_623_;
}
else
{
lean_dec(v___y_596_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_647_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_611_, v___x_616_);
if (lean_obj_tag(v___x_626_) == 1)
{
lean_object* v_val_627_; lean_object* v___x_629_; 
v_val_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_val_627_);
lean_dec_ref_known(v___x_626_, 1);
lean_inc(v___x_616_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 3, v___x_616_);
lean_ctor_set(v___x_624_, 0, v_val_627_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_val_627_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_arrKeyTys_611_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_arrParents_612_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v_currKey_614_);
lean_ctor_set(v_reuseFailAlloc_630_, 5, v_items_615_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
v_fst_601_ = v___x_616_;
v_snd_602_ = v___x_629_;
goto v___jp_600_;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v___x_626_);
lean_del_object(v___x_624_);
lean_dec_ref(v_items_615_);
lean_dec(v_currKey_614_);
lean_dec(v_arrParents_612_);
lean_dec(v_arrKeyTys_611_);
v___x_631_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_616_);
v___x_632_ = l_Lean_MessageData_ofName(v___x_616_);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_635_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v_snd_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v_snd_638_ = lean_ctor_get(v_a_637_, 1);
lean_inc(v_snd_638_);
lean_dec(v_a_637_);
v_fst_601_ = v___x_616_;
v_snd_602_ = v_snd_638_;
goto v___jp_600_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v___x_616_);
v_a_639_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_636_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_636_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
case 1:
{
lean_del_object(v___x_620_);
lean_dec(v_val_618_);
v_fst_601_ = v___x_616_;
v_snd_602_ = v___y_596_;
goto v___jp_600_;
}
case 4:
{
lean_del_object(v___x_620_);
lean_dec(v_val_618_);
v_fst_601_ = v___x_616_;
v_snd_602_ = v___y_596_;
goto v___jp_600_;
}
case 3:
{
lean_del_object(v___x_620_);
lean_dec(v_val_618_);
v_fst_601_ = v___x_616_;
v_snd_602_ = v___y_596_;
goto v___jp_600_;
}
default: 
{
lean_object* v___x_654_; uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_654_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_655_ = lean_unbox(v_val_618_);
lean_dec(v_val_618_);
v___x_656_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_655_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 3);
lean_ctor_set(v___x_620_, 0, v___x_656_);
v___x_658_ = v___x_620_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_678_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_659_ = l_Lean_MessageData_ofFormat(v___x_658_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_654_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
lean_inc(v___x_616_);
v___x_663_ = l_Lean_MessageData_ofName(v___x_616_);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_607_, v___x_666_, v___y_596_, v___y_597_, v___y_598_);
lean_dec_ref(v___y_596_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v_snd_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v_snd_669_ = lean_ctor_get(v_a_668_, 1);
lean_inc(v_snd_669_);
lean_dec(v_a_668_);
v_fst_601_ = v___x_616_;
v_snd_602_ = v_snd_669_;
goto v___jp_600_;
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v___x_616_);
v_a_670_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_667_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_667_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
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
lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_689_; 
lean_inc_ref(v_items_615_);
lean_inc(v_currKey_614_);
lean_inc(v_currArrKey_613_);
lean_inc(v_arrParents_612_);
lean_inc(v_arrKeyTys_611_);
lean_inc(v_keyTys_610_);
lean_dec(v___x_617_);
v_isSharedCheck_689_ = !lean_is_exclusive(v___y_596_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; lean_object* v_unused_691_; lean_object* v_unused_692_; lean_object* v_unused_693_; lean_object* v_unused_694_; lean_object* v_unused_695_; 
v_unused_690_ = lean_ctor_get(v___y_596_, 5);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v___y_596_, 4);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v___y_596_, 3);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v___y_596_, 2);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v___y_596_, 1);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v___y_596_, 0);
lean_dec(v_unused_695_);
v___x_681_ = v___y_596_;
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
else
{
lean_dec(v___y_596_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_683_ = 4;
v___x_684_ = lean_box(v___x_683_);
lean_inc(v___x_616_);
v___x_685_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_616_, v___x_684_, v_keyTys_610_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_685_);
v___x_687_ = v___x_681_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_arrKeyTys_611_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_arrParents_612_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_currArrKey_613_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_currKey_614_);
lean_ctor_set(v_reuseFailAlloc_688_, 5, v_items_615_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v_fst_601_ = v___x_616_;
v_snd_602_ = v___x_687_;
goto v___jp_600_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___y_596_);
lean_dec(v_b_595_);
v_a_696_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_608_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_608_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_b_595_);
lean_ctor_set(v___x_704_, 1, v___y_596_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
v___jp_600_:
{
size_t v___x_603_; size_t v___x_604_; 
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_add(v_i_593_, v___x_603_);
v_i_593_ = v___x_604_;
v_b_595_ = v_fst_601_;
v___y_596_ = v_snd_602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_706_, lean_object* v_i_707_, lean_object* v_stop_708_, lean_object* v_b_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
size_t v_i_boxed_714_; size_t v_stop_boxed_715_; lean_object* v_res_716_; 
v_i_boxed_714_ = lean_unbox_usize(v_i_707_);
lean_dec(v_i_707_);
v_stop_boxed_715_ = lean_unbox_usize(v_stop_708_);
lean_dec(v_stop_708_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_706_, v_i_boxed_714_, v_stop_boxed_715_, v_b_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v_as_706_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_717_, lean_object* v_k_718_){
_start:
{
if (lean_obj_tag(v_t_717_) == 0)
{
lean_object* v_k_719_; lean_object* v_v_720_; lean_object* v_l_721_; lean_object* v_r_722_; uint8_t v___x_723_; 
v_k_719_ = lean_ctor_get(v_t_717_, 1);
v_v_720_ = lean_ctor_get(v_t_717_, 2);
v_l_721_ = lean_ctor_get(v_t_717_, 3);
v_r_722_ = lean_ctor_get(v_t_717_, 4);
v___x_723_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_718_, v_k_719_);
switch(v___x_723_)
{
case 0:
{
v_t_717_ = v_l_721_;
goto _start;
}
case 1:
{
lean_object* v___x_725_; 
lean_inc(v_v_720_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v_v_720_);
return v___x_725_;
}
default: 
{
v_t_717_ = v_r_722_;
goto _start;
}
}
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_box(0);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_728_, lean_object* v_k_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_728_, v_k_729_);
lean_dec(v_k_729_);
lean_dec(v_t_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_keyTys_736_; lean_object* v_arrKeyTys_737_; lean_object* v_arrParents_738_; lean_object* v_currArrKey_739_; lean_object* v_currKey_740_; lean_object* v_items_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_763_; 
v_keyTys_736_ = lean_ctor_get(v_a_732_, 0);
v_arrKeyTys_737_ = lean_ctor_get(v_a_732_, 1);
v_arrParents_738_ = lean_ctor_get(v_a_732_, 2);
v_currArrKey_739_ = lean_ctor_get(v_a_732_, 3);
v_currKey_740_ = lean_ctor_get(v_a_732_, 4);
v_items_741_ = lean_ctor_get(v_a_732_, 5);
v_isSharedCheck_763_ = !lean_is_exclusive(v_a_732_);
if (v_isSharedCheck_763_ == 0)
{
v___x_743_ = v_a_732_;
v_isShared_744_ = v_isSharedCheck_763_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_items_741_);
lean_inc(v_currKey_740_);
lean_inc(v_currArrKey_739_);
lean_inc(v_arrParents_738_);
lean_inc(v_arrKeyTys_737_);
lean_inc(v_keyTys_736_);
lean_dec(v_a_732_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_763_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_arrKeyTys_745_; lean_object* v___x_746_; lean_object* v___y_748_; lean_object* v___x_760_; 
v_arrKeyTys_745_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_739_, v_keyTys_736_, v_arrKeyTys_737_);
v___x_746_ = lean_box(0);
v___x_760_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_745_, v___x_746_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_761_; 
v___x_761_ = lean_box(1);
v___y_748_ = v___x_761_;
goto v___jp_747_;
}
else
{
lean_object* v_val_762_; 
v_val_762_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v___x_760_, 1);
v___y_748_ = v_val_762_;
goto v___jp_747_;
}
v___jp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 3, v___x_746_);
lean_ctor_set(v___x_743_, 1, v_arrKeyTys_745_);
lean_ctor_set(v___x_743_, 0, v___y_748_);
v___x_750_ = v___x_743_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___y_748_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_arrKeyTys_745_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_arrParents_738_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_currKey_740_);
lean_ctor_set(v_reuseFailAlloc_759_, 5, v_items_741_);
v___x_750_ = v_reuseFailAlloc_759_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_array_get_size(v_ks_731_);
v___x_753_ = lean_nat_dec_lt(v___x_751_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_746_);
lean_ctor_set(v___x_754_, 1, v___x_750_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
else
{
size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
v___x_756_ = ((size_t)0ULL);
v___x_757_ = lean_usize_of_nat(v___x_752_);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_731_, v___x_756_, v___x_757_, v___x_746_, v___x_750_, v_a_733_, v_a_734_);
return v___x_758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec_ref(v_ks_764_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_770_, lean_object* v_t_771_, lean_object* v_k_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_771_, v_k_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_774_, lean_object* v_t_775_, lean_object* v_k_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_774_, v_t_775_, v_k_776_);
lean_dec(v_k_776_);
lean_dec(v_t_775_);
return v_res_777_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0(void){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_778_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
v___x_786_ = l_Lean_stringToMessageData(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___y_793_; lean_object* v_keyTys_794_; lean_object* v_arrKeyTys_795_; lean_object* v_arrParents_796_; lean_object* v_currArrKey_797_; lean_object* v_items_798_; lean_object* v_toCold_810_; lean_object* v_currRecDepth_811_; lean_object* v_ref_812_; uint16_t v_optionFlags_813_; uint8_t v_suppressElabErrors_814_; uint8_t v_checkDeprecated_815_; uint8_t v_isRecordingDeps_816_; lean_object* v___x_817_; uint8_t v___x_818_; lean_object* v_ref_819_; lean_object* v___x_820_; 
v_toCold_810_ = lean_ctor_get(v_a_789_, 0);
v_currRecDepth_811_ = lean_ctor_get(v_a_789_, 1);
v_ref_812_ = lean_ctor_get(v_a_789_, 2);
v_optionFlags_813_ = lean_ctor_get_uint16(v_a_789_, sizeof(void*)*3);
v_suppressElabErrors_814_ = lean_ctor_get_uint8(v_a_789_, sizeof(void*)*3 + 2);
v_checkDeprecated_815_ = lean_ctor_get_uint8(v_a_789_, sizeof(void*)*3 + 3);
v_isRecordingDeps_816_ = lean_ctor_get_uint8(v_a_789_, sizeof(void*)*3 + 4);
v___x_817_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_787_);
v___x_818_ = l_Lean_Syntax_isOfKind(v_x_787_, v___x_817_);
v_ref_819_ = l_Lean_replaceRef(v_x_787_, v_ref_812_);
lean_inc(v_currRecDepth_811_);
lean_inc_ref(v_toCold_810_);
v___x_820_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_820_, 0, v_toCold_810_);
lean_ctor_set(v___x_820_, 1, v_currRecDepth_811_);
lean_ctor_set(v___x_820_, 2, v_ref_819_);
lean_ctor_set_uint16(v___x_820_, sizeof(void*)*3, v_optionFlags_813_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*3 + 2, v_suppressElabErrors_814_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*3 + 3, v_checkDeprecated_815_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*3 + 4, v_isRecordingDeps_816_);
if (v___x_818_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4);
v___x_822_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_787_, v___x_821_, v_a_788_, v___x_820_, v_a_790_);
lean_dec_ref_known(v___x_820_, 3);
lean_dec_ref(v_a_788_);
lean_dec(v_x_787_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___y_826_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = l_Lean_Syntax_getArg(v_x_787_, v___x_823_);
v___x_894_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_824_);
v___x_895_ = l_Lean_Syntax_isOfKind(v___x_824_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec(v_x_787_);
v___x_896_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_897_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_824_, v___x_896_, v_a_788_, v___x_820_, v_a_790_);
lean_dec_ref_known(v___x_820_, 3);
lean_dec_ref(v_a_788_);
lean_dec(v___x_824_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = l_Lean_Syntax_getArg(v___x_824_, v___x_898_);
v___x_900_ = l_Lean_Syntax_getArgs(v___x_899_);
lean_dec(v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_902_ = lean_array_get_size(v___x_900_);
v___x_903_ = lean_nat_dec_lt(v___x_898_, v___x_902_);
if (v___x_903_ == 0)
{
lean_dec_ref(v___x_900_);
v___y_826_ = v___x_901_;
goto v___jp_825_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; lean_object* v_snd_909_; 
v___x_904_ = lean_box(v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_901_);
v___x_906_ = ((size_t)0ULL);
v___x_907_ = lean_usize_of_nat(v___x_902_);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_895_, v___x_900_, v___x_906_, v___x_907_, v___x_905_);
lean_dec_ref(v___x_900_);
v_snd_909_ = lean_ctor_get(v___x_908_, 1);
lean_inc(v_snd_909_);
lean_dec_ref(v___x_908_);
v___y_826_ = v_snd_909_;
goto v___jp_825_;
}
}
v___jp_825_:
{
size_t v_sz_827_; size_t v___x_828_; lean_object* v___x_829_; 
v_sz_827_ = lean_array_size(v___y_826_);
v___x_828_ = ((size_t)0ULL);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_827_, v___x_828_, v___y_826_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v_x_787_);
v___x_830_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_831_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_824_, v___x_830_, v_a_788_, v___x_820_, v_a_790_);
lean_dec_ref_known(v___x_820_, 3);
lean_dec_ref(v_a_788_);
lean_dec(v___x_824_);
return v___x_831_;
}
else
{
lean_object* v_val_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v_tailKey_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v___x_824_);
v_val_832_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v___x_829_, 1);
v___x_833_ = lean_box(0);
v___x_834_ = lean_array_get_size(v_val_832_);
v___x_835_ = lean_nat_sub(v___x_834_, v___x_823_);
v_tailKey_836_ = lean_array_get(v___x_833_, v_val_832_, v___x_835_);
lean_dec(v___x_835_);
v___x_837_ = lean_array_pop(v_val_832_);
v___x_838_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_837_, v_a_788_, v___x_820_, v_a_790_);
lean_dec_ref(v___x_837_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v_fst_840_; lean_object* v_snd_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_885_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
v_fst_840_ = lean_ctor_get(v_a_839_, 0);
v_snd_841_ = lean_ctor_get(v_a_839_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_a_839_);
if (v_isSharedCheck_885_ == 0)
{
v___x_843_ = v_a_839_;
v_isShared_844_ = v_isSharedCheck_885_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_snd_841_);
lean_inc(v_fst_840_);
lean_dec(v_a_839_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_885_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; 
lean_inc(v_tailKey_836_);
v___x_845_ = l_Lake_Toml_elabSimpleKey(v_tailKey_836_, v___x_820_, v_a_790_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v_keyTys_847_; lean_object* v_arrKeyTys_848_; lean_object* v_arrParents_849_; lean_object* v_currArrKey_850_; lean_object* v_items_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v_keyTys_847_ = lean_ctor_get(v_snd_841_, 0);
v_arrKeyTys_848_ = lean_ctor_get(v_snd_841_, 1);
v_arrParents_849_ = lean_ctor_get(v_snd_841_, 2);
v_currArrKey_850_ = lean_ctor_get(v_snd_841_, 3);
v_items_851_ = lean_ctor_get(v_snd_841_, 5);
v___x_852_ = l_Lean_Name_str___override(v_fst_840_, v_a_846_);
v___x_853_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_847_, v___x_852_);
if (lean_obj_tag(v___x_853_) == 1)
{
lean_object* v_val_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_876_; 
v_val_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_876_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_876_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_val_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_876_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
uint8_t v___x_858_; 
v___x_858_ = lean_unbox(v_val_854_);
if (v___x_858_ == 4)
{
lean_inc_ref(v_items_851_);
lean_inc(v_currArrKey_850_);
lean_inc(v_arrParents_849_);
lean_inc(v_arrKeyTys_848_);
lean_inc(v_keyTys_847_);
lean_del_object(v___x_856_);
lean_dec(v_val_854_);
lean_del_object(v___x_843_);
lean_dec(v_snd_841_);
lean_dec(v_tailKey_836_);
lean_dec_ref_known(v___x_820_, 3);
v___y_793_ = v___x_852_;
v_keyTys_794_ = v_keyTys_847_;
v_arrKeyTys_795_ = v_arrKeyTys_848_;
v_arrParents_796_ = v_arrParents_849_;
v_currArrKey_797_ = v_currArrKey_850_;
v_items_798_ = v_items_851_;
goto v___jp_792_;
}
else
{
lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
lean_dec(v_x_787_);
v___x_859_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_860_ = lean_unbox(v_val_854_);
lean_dec(v_val_854_);
v___x_861_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_860_);
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 3);
lean_ctor_set(v___x_856_, 0, v___x_861_);
v___x_863_ = v___x_856_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_875_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = l_Lean_MessageData_ofFormat(v___x_863_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 7);
lean_ctor_set(v___x_843_, 1, v___x_864_);
lean_ctor_set(v___x_843_, 0, v___x_859_);
v___x_866_ = v___x_843_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_864_);
v___x_866_ = v_reuseFailAlloc_874_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_MessageData_ofName(v___x_852_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_836_, v___x_872_, v_snd_841_, v___x_820_, v_a_790_);
lean_dec_ref_known(v___x_820_, 3);
lean_dec(v_snd_841_);
lean_dec(v_tailKey_836_);
return v___x_873_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_851_);
lean_inc(v_currArrKey_850_);
lean_inc(v_arrParents_849_);
lean_inc(v_arrKeyTys_848_);
lean_inc(v_keyTys_847_);
lean_dec(v___x_853_);
lean_del_object(v___x_843_);
lean_dec(v_snd_841_);
lean_dec(v_tailKey_836_);
lean_dec_ref_known(v___x_820_, 3);
v___y_793_ = v___x_852_;
v_keyTys_794_ = v_keyTys_847_;
v_arrKeyTys_795_ = v_arrKeyTys_848_;
v_arrParents_796_ = v_arrParents_849_;
v_currArrKey_797_ = v_currArrKey_850_;
v_items_798_ = v_items_851_;
goto v___jp_792_;
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_del_object(v___x_843_);
lean_dec(v_snd_841_);
lean_dec(v_fst_840_);
lean_dec(v_tailKey_836_);
lean_dec_ref_known(v___x_820_, 3);
lean_dec(v_x_787_);
v_a_877_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_845_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_845_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_tailKey_836_);
lean_dec_ref_known(v___x_820_, 3);
lean_dec(v_x_787_);
v_a_886_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_838_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_838_);
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
}
v___jp_792_:
{
lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_799_ = lean_box(0);
v___x_800_ = 1;
v___x_801_ = lean_box(v___x_800_);
lean_inc_n(v___y_793_, 2);
v___x_802_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_793_, v___x_801_, v_keyTys_794_);
v___x_803_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_x_787_);
v___x_804_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_804_, 0, v_x_787_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_805_, 0, v_x_787_);
lean_ctor_set(v___x_805_, 1, v___y_793_);
lean_ctor_set(v___x_805_, 2, v___x_804_);
v___x_806_ = lean_array_push(v_items_798_, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_807_, 0, v___x_802_);
lean_ctor_set(v___x_807_, 1, v_arrKeyTys_795_);
lean_ctor_set(v___x_807_, 2, v_arrParents_796_);
lean_ctor_set(v___x_807_, 3, v_currArrKey_797_);
lean_ctor_set(v___x_807_, 4, v___y_793_);
lean_ctor_set(v___x_807_, 5, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_799_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_915_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_toCold_929_; lean_object* v_currRecDepth_930_; lean_object* v_ref_931_; uint16_t v_optionFlags_932_; uint8_t v_suppressElabErrors_933_; uint8_t v_checkDeprecated_934_; uint8_t v_isRecordingDeps_935_; lean_object* v___x_936_; uint8_t v___x_937_; lean_object* v_ref_938_; lean_object* v___x_939_; lean_object* v___y_941_; 
v_toCold_929_ = lean_ctor_get(v_a_926_, 0);
v_currRecDepth_930_ = lean_ctor_get(v_a_926_, 1);
v_ref_931_ = lean_ctor_get(v_a_926_, 2);
v_optionFlags_932_ = lean_ctor_get_uint16(v_a_926_, sizeof(void*)*3);
v_suppressElabErrors_933_ = lean_ctor_get_uint8(v_a_926_, sizeof(void*)*3 + 2);
v_checkDeprecated_934_ = lean_ctor_get_uint8(v_a_926_, sizeof(void*)*3 + 3);
v_isRecordingDeps_935_ = lean_ctor_get_uint8(v_a_926_, sizeof(void*)*3 + 4);
v___x_936_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_924_);
v___x_937_ = l_Lean_Syntax_isOfKind(v_x_924_, v___x_936_);
v_ref_938_ = l_Lean_replaceRef(v_x_924_, v_ref_931_);
lean_inc(v_currRecDepth_930_);
lean_inc_ref(v_toCold_929_);
v___x_939_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_939_, 0, v_toCold_929_);
lean_ctor_set(v___x_939_, 1, v_currRecDepth_930_);
lean_ctor_set(v___x_939_, 2, v_ref_938_);
lean_ctor_set_uint16(v___x_939_, sizeof(void*)*3, v_optionFlags_932_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3 + 2, v_suppressElabErrors_933_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3 + 3, v_checkDeprecated_934_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3 + 4, v_isRecordingDeps_935_);
if (v___x_937_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_949_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_924_, v___x_948_, v_a_925_, v___x_939_, v_a_927_);
lean_dec_ref_known(v___x_939_, 3);
lean_dec_ref(v_a_925_);
lean_dec(v_x_924_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___y_955_; 
v___x_950_ = lean_unsigned_to_nat(2u);
v___x_951_ = l_Lean_Syntax_getArg(v_x_924_, v___x_950_);
v___x_952_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_951_);
v___x_953_ = l_Lean_Syntax_isOfKind(v___x_951_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec(v___x_951_);
v___x_1089_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1090_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_924_, v___x_1089_, v_a_925_, v___x_939_, v_a_927_);
lean_dec_ref_known(v___x_939_, 3);
lean_dec_ref(v_a_925_);
lean_dec(v_x_924_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = l_Lean_Syntax_getArg(v___x_951_, v___x_1091_);
lean_dec(v___x_951_);
v___x_1093_ = l_Lean_Syntax_getArgs(v___x_1092_);
lean_dec(v___x_1092_);
v___x_1094_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1095_ = lean_array_get_size(v___x_1093_);
v___x_1096_ = lean_nat_dec_lt(v___x_1091_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_dec_ref(v___x_1093_);
v___y_955_ = v___x_1094_;
goto v___jp_954_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; lean_object* v___x_1101_; lean_object* v_snd_1102_; 
v___x_1097_ = lean_box(v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v___x_1094_);
v___x_1099_ = ((size_t)0ULL);
v___x_1100_ = lean_usize_of_nat(v___x_1095_);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_953_, v___x_1093_, v___x_1099_, v___x_1100_, v___x_1098_);
lean_dec_ref(v___x_1093_);
v_snd_1102_ = lean_ctor_get(v___x_1101_, 1);
lean_inc(v_snd_1102_);
lean_dec_ref(v___x_1101_);
v___y_955_ = v_snd_1102_;
goto v___jp_954_;
}
}
v___jp_954_:
{
size_t v_sz_956_; size_t v___x_957_; lean_object* v___x_958_; 
v_sz_956_ = lean_array_size(v___y_955_);
v___x_957_ = ((size_t)0ULL);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_956_, v___x_957_, v___y_955_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_960_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_924_, v___x_959_, v_a_925_, v___x_939_, v_a_927_);
lean_dec_ref_known(v___x_939_, 3);
lean_dec_ref(v_a_925_);
lean_dec(v_x_924_);
return v___x_960_;
}
else
{
lean_object* v_val_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_tailKey_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_val_961_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_val_961_);
lean_dec_ref_known(v___x_958_, 1);
v___x_962_ = lean_box(0);
v___x_963_ = lean_array_get_size(v_val_961_);
v___x_964_ = lean_unsigned_to_nat(1u);
v___x_965_ = lean_nat_sub(v___x_963_, v___x_964_);
v_tailKey_966_ = lean_array_get(v___x_962_, v_val_961_, v___x_965_);
lean_dec(v___x_965_);
v___x_967_ = lean_array_pop(v_val_961_);
v___x_968_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_967_, v_a_925_, v___x_939_, v_a_927_);
lean_dec_ref(v___x_967_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v_fst_970_; lean_object* v_snd_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1080_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v_fst_970_ = lean_ctor_get(v_a_969_, 0);
v_snd_971_ = lean_ctor_get(v_a_969_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_a_969_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_973_ = v_a_969_;
v_isShared_974_ = v_isSharedCheck_1080_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_snd_971_);
lean_inc(v_fst_970_);
lean_dec(v_a_969_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1080_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; 
lean_inc(v_tailKey_966_);
v___x_975_ = l_Lake_Toml_elabSimpleKey(v_tailKey_966_, v___x_939_, v_a_927_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1071_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1071_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1071_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_keyTys_980_; lean_object* v_arrKeyTys_981_; lean_object* v_arrParents_982_; lean_object* v_currArrKey_983_; lean_object* v_items_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_keyTys_980_ = lean_ctor_get(v_snd_971_, 0);
v_arrKeyTys_981_ = lean_ctor_get(v_snd_971_, 1);
v_arrParents_982_ = lean_ctor_get(v_snd_971_, 2);
v_currArrKey_983_ = lean_ctor_get(v_snd_971_, 3);
v_items_984_ = lean_ctor_get(v_snd_971_, 5);
v___x_985_ = l_Lean_Name_str___override(v_fst_970_, v_a_976_);
v___x_986_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_980_, v___x_985_);
if (lean_obj_tag(v___x_986_) == 1)
{
lean_object* v_val_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1038_; 
v_val_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1038_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_val_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1038_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
uint8_t v___x_991_; 
v___x_991_ = lean_unbox(v_val_987_);
if (v___x_991_ == 2)
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1016_; 
lean_inc_ref(v_items_984_);
lean_inc(v_arrParents_982_);
lean_inc(v_arrKeyTys_981_);
lean_del_object(v___x_989_);
lean_dec(v_val_987_);
lean_dec(v_tailKey_966_);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_snd_971_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; lean_object* v_unused_1018_; lean_object* v_unused_1019_; lean_object* v_unused_1020_; lean_object* v_unused_1021_; lean_object* v_unused_1022_; 
v_unused_1017_ = lean_ctor_get(v_snd_971_, 5);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_snd_971_, 4);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_snd_971_, 3);
lean_dec(v_unused_1019_);
v_unused_1020_ = lean_ctor_get(v_snd_971_, 2);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_snd_971_, 1);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_snd_971_, 0);
lean_dec(v_unused_1022_);
v___x_993_ = v_snd_971_;
v_isShared_994_ = v_isSharedCheck_1016_;
goto v_resetjp_992_;
}
else
{
lean_dec(v_snd_971_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1016_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; 
v___x_995_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_982_, v___x_985_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_del_object(v___x_993_);
lean_dec_ref(v_items_984_);
lean_dec(v_arrParents_982_);
lean_dec(v_arrKeyTys_981_);
lean_del_object(v___x_978_);
lean_del_object(v___x_973_);
lean_dec(v_x_924_);
v___y_941_ = v___x_985_;
goto v___jp_940_;
}
else
{
lean_object* v_val_996_; lean_object* v___x_997_; 
v_val_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_981_, v_val_996_);
lean_dec(v_val_996_);
if (lean_obj_tag(v___x_997_) == 1)
{
lean_object* v_val_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
lean_dec_ref_known(v___x_939_, 3);
v_val_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_924_, 2);
v___x_1001_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_x_924_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_mk_empty_array_with_capacity(v___x_964_);
v___x_1003_ = lean_array_push(v___x_1002_, v___x_1001_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_x_924_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
lean_inc_n(v___x_985_, 2);
v___x_1005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1005_, 0, v_x_924_);
lean_ctor_set(v___x_1005_, 1, v___x_985_);
lean_ctor_set(v___x_1005_, 2, v___x_1004_);
v___x_1006_ = lean_array_push(v_items_984_, v___x_1005_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 5, v___x_1006_);
lean_ctor_set(v___x_993_, 4, v___x_985_);
lean_ctor_set(v___x_993_, 3, v___x_985_);
lean_ctor_set(v___x_993_, 0, v_val_998_);
v___x_1008_ = v___x_993_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_val_998_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_arrKeyTys_981_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_arrParents_982_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1015_, 5, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 1, v___x_1008_);
lean_ctor_set(v___x_973_, 0, v___x_999_);
v___x_1010_ = v___x_973_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_1010_);
v___x_1012_ = v___x_978_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_dec(v___x_997_);
lean_del_object(v___x_993_);
lean_dec_ref(v_items_984_);
lean_dec(v_arrParents_982_);
lean_dec(v_arrKeyTys_981_);
lean_del_object(v___x_978_);
lean_del_object(v___x_973_);
lean_dec(v_x_924_);
v___y_941_ = v___x_985_;
goto v___jp_940_;
}
}
}
}
else
{
lean_object* v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
lean_del_object(v___x_978_);
lean_del_object(v___x_973_);
lean_dec(v_x_924_);
v___x_1023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1024_ = lean_unbox(v_val_987_);
lean_dec(v_val_987_);
v___x_1025_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1024_);
v___x_1026_ = lean_string_append(v___x_1023_, v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1028_ = lean_string_append(v___x_1026_, v___x_1027_);
v___x_1029_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_985_, v___x_953_);
v___x_1030_ = lean_string_append(v___x_1028_, v___x_1029_);
lean_dec_ref(v___x_1029_);
v___x_1031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1032_ = lean_string_append(v___x_1030_, v___x_1031_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 3);
lean_ctor_set(v___x_989_, 0, v___x_1032_);
v___x_1034_ = v___x_989_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = l_Lean_MessageData_ofFormat(v___x_1034_);
v___x_1036_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_966_, v___x_1035_, v_snd_971_, v___x_939_, v_a_927_);
lean_dec_ref_known(v___x_939_, 3);
lean_dec(v_snd_971_);
lean_dec(v_tailKey_966_);
return v___x_1036_;
}
}
}
}
else
{
lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1064_; 
lean_inc_ref(v_items_984_);
lean_inc(v_currArrKey_983_);
lean_inc(v_arrParents_982_);
lean_inc(v_arrKeyTys_981_);
lean_inc(v_keyTys_980_);
lean_dec(v___x_986_);
lean_dec(v_tailKey_966_);
lean_dec_ref_known(v___x_939_, 3);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_snd_971_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; lean_object* v_unused_1066_; lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; lean_object* v_unused_1070_; 
v_unused_1065_ = lean_ctor_get(v_snd_971_, 5);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_snd_971_, 4);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_snd_971_, 3);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_snd_971_, 2);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_snd_971_, 1);
lean_dec(v_unused_1069_);
v_unused_1070_ = lean_ctor_get(v_snd_971_, 0);
lean_dec(v_unused_1070_);
v___x_1040_ = v_snd_971_;
v_isShared_1041_ = v_isSharedCheck_1064_;
goto v_resetjp_1039_;
}
else
{
lean_dec(v_snd_971_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1064_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = 2;
v___x_1044_ = lean_box(v___x_1043_);
lean_inc_n(v___x_985_, 4);
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_985_, v___x_1044_, v_keyTys_980_);
lean_inc(v___x_1045_);
lean_inc(v_currArrKey_983_);
v___x_1046_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_983_, v___x_1045_, v_arrKeyTys_981_);
v___x_1047_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_985_, v_currArrKey_983_, v_arrParents_982_);
v___x_1048_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_924_, 2);
v___x_1049_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_x_924_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_964_);
v___x_1051_ = lean_array_push(v___x_1050_, v___x_1049_);
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_x_924_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1053_, 0, v_x_924_);
lean_ctor_set(v___x_1053_, 1, v___x_985_);
lean_ctor_set(v___x_1053_, 2, v___x_1052_);
v___x_1054_ = lean_array_push(v_items_984_, v___x_1053_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 5, v___x_1054_);
lean_ctor_set(v___x_1040_, 4, v___x_985_);
lean_ctor_set(v___x_1040_, 3, v___x_985_);
lean_ctor_set(v___x_1040_, 2, v___x_1047_);
lean_ctor_set(v___x_1040_, 1, v___x_1046_);
lean_ctor_set(v___x_1040_, 0, v___x_1045_);
v___x_1056_ = v___x_1040_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1063_, 5, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 1, v___x_1056_);
lean_ctor_set(v___x_973_, 0, v___x_1042_);
v___x_1058_ = v___x_973_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_1058_);
v___x_1060_ = v___x_978_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_del_object(v___x_973_);
lean_dec(v_snd_971_);
lean_dec(v_fst_970_);
lean_dec(v_tailKey_966_);
lean_dec_ref_known(v___x_939_, 3);
lean_dec(v_x_924_);
v_a_1072_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_975_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_975_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_tailKey_966_);
lean_dec_ref_known(v___x_939_, 3);
lean_dec(v_x_924_);
v_a_1081_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_968_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_968_);
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
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_942_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_943_ = l_Lean_MessageData_ofName(v___y_941_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_946_, v___x_939_, v_a_927_);
lean_dec_ref_known(v___x_939_, 3);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1108_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1112_);
v___x_1118_ = l_Lean_Syntax_isOfKind(v_x_1112_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_1112_);
v___x_1120_ = l_Lean_Syntax_isOfKind(v_x_1112_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1112_);
v___x_1122_ = l_Lean_Syntax_isOfKind(v_x_1112_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1124_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1112_, v___x_1123_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec_ref(v_a_1113_);
lean_dec(v_x_1112_);
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1125_;
}
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1126_;
}
}
else
{
lean_object* v___x_1127_; 
v___x_1127_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1135_, lean_object* v_as_1136_, size_t v_i_1137_, size_t v_stop_1138_, lean_object* v_b_1139_){
_start:
{
lean_object* v___y_1141_; uint8_t v___x_1145_; 
v___x_1145_ = lean_usize_dec_eq(v_i_1137_, v_stop_1138_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v_fst_1147_; lean_object* v_snd_1148_; lean_object* v___x_1149_; 
v___x_1146_ = lean_array_uget_borrowed(v_as_1136_, v_i_1137_);
v_fst_1147_ = lean_ctor_get(v___x_1146_, 0);
v_snd_1148_ = lean_ctor_get(v___x_1146_, 1);
lean_inc(v_fst_1147_);
v___x_1149_ = l_Lean_Name_components(v_fst_1147_);
if (lean_obj_tag(v___x_1149_) == 0)
{
v___y_1141_ = v_b_1139_;
goto v___jp_1140_;
}
else
{
lean_object* v_head_1150_; lean_object* v_tail_1151_; lean_object* v___x_1152_; 
v_head_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_head_1150_);
v_tail_1151_ = lean_ctor_get(v___x_1149_, 1);
lean_inc(v_tail_1151_);
lean_dec_ref_known(v___x_1149_, 2);
lean_inc(v_snd_1148_);
lean_inc(v_ref_1135_);
v___x_1152_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1139_, v_ref_1135_, v_head_1150_, v_tail_1151_, v_snd_1148_);
v___y_1141_ = v___x_1152_;
goto v___jp_1140_;
}
}
else
{
lean_dec(v_ref_1135_);
return v_b_1139_;
}
v___jp_1140_:
{
size_t v___x_1142_; size_t v___x_1143_; 
v___x_1142_ = ((size_t)1ULL);
v___x_1143_ = lean_usize_add(v_i_1137_, v___x_1142_);
v_i_1137_ = v___x_1143_;
v_b_1139_ = v___y_1141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1153_, size_t v_i_1154_, lean_object* v_bs_1155_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_lt(v_i_1154_, v_sz_1153_);
if (v___x_1156_ == 0)
{
return v_bs_1155_;
}
else
{
lean_object* v_v_1157_; lean_object* v___x_1158_; lean_object* v_bs_x27_1159_; lean_object* v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; lean_object* v___x_1163_; 
v_v_1157_ = lean_array_uget(v_bs_1155_, v_i_1154_);
v___x_1158_ = lean_unsigned_to_nat(0u);
v_bs_x27_1159_ = lean_array_uset(v_bs_1155_, v_i_1154_, v___x_1158_);
v___x_1160_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1157_);
v___x_1161_ = ((size_t)1ULL);
v___x_1162_ = lean_usize_add(v_i_1154_, v___x_1161_);
v___x_1163_ = lean_array_uset(v_bs_x27_1159_, v_i_1154_, v___x_1160_);
v_i_1154_ = v___x_1162_;
v_bs_1155_ = v___x_1163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1165_){
_start:
{
switch(lean_obj_tag(v_a_1165_))
{
case 6:
{
lean_object* v_xs_1166_; lean_object* v_ref_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1185_; 
v_xs_1166_ = lean_ctor_get(v_a_1165_, 1);
v_ref_1167_ = lean_ctor_get(v_a_1165_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_a_1165_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1169_ = v_a_1165_;
v_isShared_1170_ = v_isSharedCheck_1185_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_xs_1166_);
lean_inc(v_ref_1167_);
lean_dec(v_a_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1185_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_items_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_items_1171_ = lean_ctor_get(v_xs_1166_, 0);
lean_inc_ref(v_items_1171_);
lean_dec_ref(v_xs_1166_);
v___x_1172_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_array_get_size(v_items_1171_);
v___x_1175_ = lean_nat_dec_lt(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1177_; 
lean_dec_ref(v_items_1171_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1172_);
v___x_1177_ = v___x_1169_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_ref_1167_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
else
{
size_t v___x_1179_; size_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1179_ = ((size_t)0ULL);
v___x_1180_ = lean_usize_of_nat(v___x_1174_);
lean_inc(v_ref_1167_);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1167_, v_items_1171_, v___x_1179_, v___x_1180_, v___x_1172_);
lean_dec_ref(v_items_1171_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1181_);
v___x_1183_ = v___x_1169_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_ref_1167_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
case 5:
{
lean_object* v_ref_1186_; lean_object* v_xs_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1197_; 
v_ref_1186_ = lean_ctor_get(v_a_1165_, 0);
v_xs_1187_ = lean_ctor_get(v_a_1165_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_a_1165_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1189_ = v_a_1165_;
v_isShared_1190_ = v_isSharedCheck_1197_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_xs_1187_);
lean_inc(v_ref_1186_);
lean_dec(v_a_1165_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1197_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
size_t v_sz_1191_; size_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v_sz_1191_ = lean_array_size(v_xs_1187_);
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1191_, v___x_1192_, v_xs_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1193_);
v___x_1195_ = v___x_1189_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_ref_1186_);
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
default: 
{
return v_a_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1198_, lean_object* v___x_1199_, lean_object* v_v_x3f_1200_){
_start:
{
if (lean_obj_tag(v_v_x3f_1200_) == 1)
{
lean_object* v_val_1201_; 
v_val_1201_ = lean_ctor_get(v_v_x3f_1200_, 0);
lean_inc(v_val_1201_);
lean_dec_ref_known(v_v_x3f_1200_, 1);
switch(lean_obj_tag(v_val_1201_))
{
case 6:
{
lean_object* v_ref_1202_; lean_object* v_xs_1203_; lean_object* v___x_1204_; 
v_ref_1202_ = lean_ctor_get(v_val_1201_, 0);
lean_inc(v_ref_1202_);
v_xs_1203_ = lean_ctor_get(v_val_1201_, 1);
lean_inc_ref(v_xs_1203_);
lean_dec_ref_known(v_val_1201_, 2);
v___x_1204_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1198_);
if (lean_obj_tag(v___x_1204_) == 6)
{
lean_object* v_xs_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1214_; 
v_xs_1205_ = lean_ctor_get(v___x_1204_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v___x_1204_, 0);
lean_dec(v_unused_1215_);
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1214_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_xs_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1214_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_items_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v_items_1209_ = lean_ctor_get(v_xs_1205_, 0);
lean_inc_ref(v_items_1209_);
lean_dec_ref(v_xs_1205_);
v___x_1210_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1199_, v_xs_1203_, v_items_1209_);
lean_dec_ref(v_items_1209_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1210_);
lean_ctor_set(v___x_1207_, 0, v_ref_1202_);
v___x_1212_ = v___x_1207_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_ref_1202_);
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
else
{
lean_dec_ref(v_xs_1203_);
lean_dec(v_ref_1202_);
lean_dec_ref(v___x_1199_);
return v___x_1204_;
}
}
case 5:
{
lean_object* v_ref_1216_; lean_object* v_xs_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v___x_1199_);
v_ref_1216_ = lean_ctor_get(v_val_1201_, 0);
v_xs_1217_ = lean_ctor_get(v_val_1201_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_val_1201_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1219_ = v_val_1201_;
v_isShared_1220_ = v_isSharedCheck_1236_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_xs_1217_);
lean_inc(v_ref_1216_);
lean_dec(v_val_1201_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1236_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; 
v___x_1221_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1198_);
if (lean_obj_tag(v___x_1221_) == 5)
{
lean_object* v_xs_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
lean_del_object(v___x_1219_);
v_xs_1222_ = lean_ctor_get(v___x_1221_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1221_, 0);
lean_dec(v_unused_1231_);
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_xs_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = l_Array_append___redArg(v_xs_1217_, v_xs_1222_);
lean_dec_ref(v_xs_1222_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___x_1226_);
lean_ctor_set(v___x_1224_, 0, v_ref_1216_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_ref_1216_);
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
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_array_push(v_xs_1217_, v___x_1221_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___x_1232_);
v___x_1234_ = v___x_1219_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_ref_1216_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
default: 
{
lean_object* v___x_1237_; 
lean_dec(v_val_1201_);
lean_dec_ref(v___x_1199_);
v___x_1237_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1198_);
return v___x_1237_;
}
}
}
else
{
lean_object* v___x_1238_; 
lean_dec(v_v_x3f_1200_);
lean_dec_ref(v___x_1199_);
v___x_1238_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1198_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1239_, lean_object* v_k_1240_, lean_object* v_t_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1241_);
lean_inc(v_k_1240_);
v___x_1243_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1242_, v_k_1240_, v_t_1241_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_val_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_k_1240_);
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1279_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_val_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1279_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_items_1248_; lean_object* v_indices_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1278_; 
v_items_1248_ = lean_ctor_get(v_t_1241_, 0);
v_indices_1249_ = lean_ctor_get(v_t_1241_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_t_1241_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1251_ = v_t_1241_;
v_isShared_1252_ = v_isSharedCheck_1278_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_indices_1249_);
lean_inc(v_items_1248_);
lean_dec(v_t_1241_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1278_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_array_get_size(v_items_1248_);
v___x_1254_ = lean_nat_dec_lt(v_val_1244_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1256_; 
lean_del_object(v___x_1246_);
lean_dec(v_val_1244_);
lean_dec_ref(v_newV_1239_);
if (v_isShared_1252_ == 0)
{
v___x_1256_ = v___x_1251_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_items_1248_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_indices_1249_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
lean_object* v_v_1258_; lean_object* v_fst_1259_; lean_object* v_snd_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1277_; 
v_v_1258_ = lean_array_fget(v_items_1248_, v_val_1244_);
v_fst_1259_ = lean_ctor_get(v_v_1258_, 0);
v_snd_1260_ = lean_ctor_get(v_v_1258_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_v_1258_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1262_ = v_v_1258_;
v_isShared_1263_ = v_isSharedCheck_1277_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_snd_1260_);
lean_inc(v_fst_1259_);
lean_dec(v_v_1258_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1277_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v_xs_x27_1265_; lean_object* v___x_1267_; 
v___x_1264_ = lean_box(0);
v_xs_x27_1265_ = lean_array_fset(v_items_1248_, v_val_1244_, v___x_1264_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v_snd_1260_);
v___x_1267_ = v___x_1246_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_snd_1260_);
v___x_1267_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1239_, v___x_1242_, v___x_1267_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1268_);
v___x_1270_ = v___x_1262_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_fst_1259_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_array_fset(v_xs_x27_1265_, v_val_1244_, v___x_1270_);
lean_dec(v_val_1244_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1271_);
v___x_1273_ = v___x_1251_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_indices_1249_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
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
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v___x_1243_);
v___x_1280_ = lean_box(0);
v___x_1281_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1239_, v___x_1242_, v___x_1280_);
v___x_1282_ = l_Lake_Toml_RBDict_push___redArg(v___x_1242_, v_k_1240_, v___x_1281_, v_t_1241_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1283_, lean_object* v_head_1284_, lean_object* v_tail_1285_, lean_object* v_newV_1286_, lean_object* v_v_x3f_1287_){
_start:
{
if (lean_obj_tag(v_v_x3f_1287_) == 1)
{
lean_object* v_val_1288_; 
v_val_1288_ = lean_ctor_get(v_v_x3f_1287_, 0);
lean_inc(v_val_1288_);
lean_dec_ref_known(v_v_x3f_1287_, 1);
switch(lean_obj_tag(v_val_1288_))
{
case 5:
{
lean_object* v_ref_1289_; lean_object* v_xs_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_ref_1289_ = lean_ctor_get(v_val_1288_, 0);
v_xs_1290_ = lean_ctor_get(v_val_1288_, 1);
v___x_1291_ = lean_array_get_size(v_xs_1290_);
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = lean_nat_sub(v___x_1291_, v___x_1292_);
v___x_1294_ = lean_nat_dec_lt(v___x_1293_, v___x_1291_);
if (v___x_1294_ == 0)
{
lean_dec(v___x_1293_);
lean_dec_ref(v_newV_1286_);
lean_dec(v_tail_1285_);
lean_dec(v_head_1284_);
lean_dec(v_kRef_1283_);
return v_val_1288_;
}
else
{
lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1319_; 
lean_inc_ref(v_xs_1290_);
lean_inc(v_ref_1289_);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_val_1288_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; lean_object* v_unused_1321_; 
v_unused_1320_ = lean_ctor_get(v_val_1288_, 1);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_val_1288_, 0);
lean_dec(v_unused_1321_);
v___x_1296_ = v_val_1288_;
v_isShared_1297_ = v_isSharedCheck_1319_;
goto v_resetjp_1295_;
}
else
{
lean_dec(v_val_1288_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1319_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_v_1298_; lean_object* v___x_1299_; lean_object* v_xs_x27_1300_; lean_object* v___y_1302_; 
v_v_1298_ = lean_array_fget(v_xs_1290_, v___x_1293_);
v___x_1299_ = lean_box(0);
v_xs_x27_1300_ = lean_array_fset(v_xs_1290_, v___x_1293_, v___x_1299_);
if (lean_obj_tag(v_v_1298_) == 6)
{
lean_object* v_ref_1307_; lean_object* v_xs_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_ref_1307_ = lean_ctor_get(v_v_1298_, 0);
v_xs_1308_ = lean_ctor_get(v_v_1298_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_v_1298_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1310_ = v_v_1298_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_xs_1308_);
lean_inc(v_ref_1307_);
lean_dec(v_v_1298_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1308_, v_kRef_1283_, v_head_1284_, v_tail_1285_, v_newV_1286_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 1, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_ref_1307_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
v___y_1302_ = v___x_1314_;
goto v___jp_1301_;
}
}
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec(v_v_1298_);
lean_dec_ref(v_newV_1286_);
lean_dec(v_tail_1285_);
lean_dec(v_head_1284_);
v___x_1317_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1318_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_kRef_1283_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___y_1302_ = v___x_1318_;
goto v___jp_1301_;
}
v___jp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = lean_array_fset(v_xs_x27_1300_, v___x_1293_, v___y_1302_);
lean_dec(v___x_1293_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v___x_1303_);
v___x_1305_ = v___x_1296_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_ref_1289_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1322_; lean_object* v_xs_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1331_; 
v_ref_1322_ = lean_ctor_get(v_val_1288_, 0);
v_xs_1323_ = lean_ctor_get(v_val_1288_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_val_1288_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1325_ = v_val_1288_;
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_xs_1323_);
lean_inc(v_ref_1322_);
lean_dec(v_val_1288_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1327_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1323_, v_kRef_1283_, v_head_1284_, v_tail_1285_, v_newV_1286_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v___x_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_ref_1322_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
default: 
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec(v_val_1288_);
v___x_1332_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1283_);
v___x_1333_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1332_, v_kRef_1283_, v_head_1284_, v_tail_1285_, v_newV_1286_);
v___x_1334_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_kRef_1283_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
return v___x_1334_;
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec(v_v_x3f_1287_);
v___x_1335_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1283_);
v___x_1336_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1335_, v_kRef_1283_, v_head_1284_, v_tail_1285_, v_newV_1286_);
v___x_1337_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_kRef_1283_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1338_, lean_object* v_head_1339_, lean_object* v_tail_1340_, lean_object* v_newV_1341_, lean_object* v_k_1342_, lean_object* v_t_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1343_);
lean_inc(v_k_1342_);
v___x_1345_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1344_, v_k_1342_, v_t_1343_);
if (lean_obj_tag(v___x_1345_) == 1)
{
lean_object* v_val_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_k_1342_);
v_val_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1381_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_val_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1381_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_items_1350_; lean_object* v_indices_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1380_; 
v_items_1350_ = lean_ctor_get(v_t_1343_, 0);
v_indices_1351_ = lean_ctor_get(v_t_1343_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_t_1343_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1353_ = v_t_1343_;
v_isShared_1354_ = v_isSharedCheck_1380_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_indices_1351_);
lean_inc(v_items_1350_);
lean_dec(v_t_1343_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1380_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = lean_array_get_size(v_items_1350_);
v___x_1356_ = lean_nat_dec_lt(v_val_1346_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1358_; 
lean_del_object(v___x_1348_);
lean_dec(v_val_1346_);
lean_dec_ref(v_newV_1341_);
lean_dec(v_tail_1340_);
lean_dec(v_head_1339_);
lean_dec(v_kRef_1338_);
if (v_isShared_1354_ == 0)
{
v___x_1358_ = v___x_1353_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_items_1350_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_indices_1351_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
else
{
lean_object* v_v_1360_; lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1379_; 
v_v_1360_ = lean_array_fget(v_items_1350_, v_val_1346_);
v_fst_1361_ = lean_ctor_get(v_v_1360_, 0);
v_snd_1362_ = lean_ctor_get(v_v_1360_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_v_1360_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1364_ = v_v_1360_;
v_isShared_1365_ = v_isSharedCheck_1379_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_snd_1362_);
lean_inc(v_fst_1361_);
lean_dec(v_v_1360_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1379_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v_xs_x27_1367_; lean_object* v___x_1369_; 
v___x_1366_ = lean_box(0);
v_xs_x27_1367_ = lean_array_fset(v_items_1350_, v_val_1346_, v___x_1366_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v_snd_1362_);
v___x_1369_ = v___x_1348_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_snd_1362_);
v___x_1369_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1338_, v_head_1339_, v_tail_1340_, v_newV_1341_, v___x_1369_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1370_);
v___x_1372_ = v___x_1364_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_fst_1361_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_array_fset(v_xs_x27_1367_, v_val_1346_, v___x_1372_);
lean_dec(v_val_1346_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1373_);
v___x_1375_ = v___x_1353_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_indices_1351_);
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
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v___x_1345_);
v___x_1382_ = lean_box(0);
v___x_1383_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1338_, v_head_1339_, v_tail_1340_, v_newV_1341_, v___x_1382_);
v___x_1384_ = l_Lake_Toml_RBDict_push___redArg(v___x_1344_, v_k_1342_, v___x_1383_, v_t_1343_);
return v___x_1384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1385_, lean_object* v_kRef_1386_, lean_object* v_k_1387_, lean_object* v_ks_1388_, lean_object* v_newV_1389_){
_start:
{
if (lean_obj_tag(v_ks_1388_) == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_kRef_1386_);
v___x_1390_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1389_, v_k_1387_, v_t_1385_);
return v___x_1390_;
}
else
{
lean_object* v_head_1391_; lean_object* v_tail_1392_; lean_object* v___x_1393_; 
v_head_1391_ = lean_ctor_get(v_ks_1388_, 0);
lean_inc(v_head_1391_);
v_tail_1392_ = lean_ctor_get(v_ks_1388_, 1);
lean_inc(v_tail_1392_);
lean_dec_ref_known(v_ks_1388_, 2);
v___x_1393_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1386_, v_head_1391_, v_tail_1392_, v_newV_1389_, v_k_1387_, v_t_1385_);
return v___x_1393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1394_, lean_object* v_i_1395_, lean_object* v_bs_1396_){
_start:
{
size_t v_sz_boxed_1397_; size_t v_i_boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1394_);
lean_dec(v_sz_1394_);
v_i_boxed_1398_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1397_, v_i_boxed_1398_, v_bs_1396_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1400_, lean_object* v_as_1401_, lean_object* v_i_1402_, lean_object* v_stop_1403_, lean_object* v_b_1404_){
_start:
{
size_t v_i_boxed_1405_; size_t v_stop_boxed_1406_; lean_object* v_res_1407_; 
v_i_boxed_1405_ = lean_unbox_usize(v_i_1402_);
lean_dec(v_i_1402_);
v_stop_boxed_1406_ = lean_unbox_usize(v_stop_1403_);
lean_dec(v_stop_1403_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1400_, v_as_1401_, v_i_boxed_1405_, v_stop_boxed_1406_, v_b_1404_);
lean_dec_ref(v_as_1401_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1408_, size_t v_i_1409_, size_t v_stop_1410_, lean_object* v_b_1411_){
_start:
{
lean_object* v___y_1413_; uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_eq(v_i_1409_, v_stop_1410_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v_ref_1419_; lean_object* v_key_1420_; lean_object* v_val_1421_; lean_object* v___x_1422_; 
v___x_1418_ = lean_array_uget_borrowed(v_as_1408_, v_i_1409_);
v_ref_1419_ = lean_ctor_get(v___x_1418_, 0);
v_key_1420_ = lean_ctor_get(v___x_1418_, 1);
v_val_1421_ = lean_ctor_get(v___x_1418_, 2);
lean_inc(v_key_1420_);
v___x_1422_ = l_Lean_Name_components(v_key_1420_);
if (lean_obj_tag(v___x_1422_) == 0)
{
v___y_1413_ = v_b_1411_;
goto v___jp_1412_;
}
else
{
lean_object* v_head_1423_; lean_object* v_tail_1424_; lean_object* v___x_1425_; 
v_head_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_head_1423_);
v_tail_1424_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_tail_1424_);
lean_dec_ref_known(v___x_1422_, 2);
lean_inc_ref(v_val_1421_);
lean_inc(v_ref_1419_);
v___x_1425_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1411_, v_ref_1419_, v_head_1423_, v_tail_1424_, v_val_1421_);
v___y_1413_ = v___x_1425_;
goto v___jp_1412_;
}
}
else
{
return v_b_1411_;
}
v___jp_1412_:
{
size_t v___x_1414_; size_t v___x_1415_; 
v___x_1414_ = ((size_t)1ULL);
v___x_1415_ = lean_usize_add(v_i_1409_, v___x_1414_);
v_i_1409_ = v___x_1415_;
v_b_1411_ = v___y_1413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1426_, lean_object* v_i_1427_, lean_object* v_stop_1428_, lean_object* v_b_1429_){
_start:
{
size_t v_i_boxed_1430_; size_t v_stop_boxed_1431_; lean_object* v_res_1432_; 
v_i_boxed_1430_ = lean_unbox_usize(v_i_1427_);
lean_dec(v_i_1427_);
v_stop_boxed_1431_ = lean_unbox_usize(v_stop_1428_);
lean_dec(v_stop_1428_);
v_res_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1426_, v_i_boxed_1430_, v_stop_boxed_1431_, v_b_1429_);
lean_dec_ref(v_as_1426_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1434_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_array_get_size(v_items_1433_);
v___x_1437_ = lean_nat_dec_lt(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
return v___x_1434_;
}
else
{
size_t v___x_1438_; size_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = ((size_t)0ULL);
v___x_1439_ = lean_usize_of_nat(v___x_1436_);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1433_, v___x_1438_, v___x_1439_, v___x_1434_);
return v___x_1440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1441_);
lean_dec_ref(v_items_1441_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1445_);
lean_inc_ref(v_a_1444_);
v___x_1448_ = lean_apply_4(v_x_1443_, v___x_1447_, v_a_1444_, v_a_1445_, lean_box(0));
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1459_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_snd_1453_; lean_object* v_items_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v_snd_1453_ = lean_ctor_get(v_a_1449_, 1);
lean_inc(v_snd_1453_);
lean_dec(v_a_1449_);
v_items_1454_ = lean_ctor_get(v_snd_1453_, 5);
lean_inc_ref(v_items_1454_);
lean_dec(v_snd_1453_);
v___x_1455_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1454_);
lean_dec_ref(v_items_1454_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1455_);
v___x_1457_ = v___x_1451_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
v_a_1460_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1448_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1448_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
return v_res_1472_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1481_, lean_object* v_x_1482_){
_start:
{
if (lean_obj_tag(v_x_1482_) == 1)
{
lean_object* v_pre_1483_; 
v_pre_1483_ = lean_ctor_get(v_x_1482_, 0);
switch(lean_obj_tag(v_pre_1483_))
{
case 1:
{
lean_object* v_pre_1484_; 
v_pre_1484_ = lean_ctor_get(v_pre_1483_, 0);
switch(lean_obj_tag(v_pre_1484_))
{
case 0:
{
lean_object* v_str_1485_; lean_object* v_str_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v_str_1485_ = lean_ctor_get(v_x_1482_, 1);
v_str_1486_ = lean_ctor_get(v_pre_1483_, 1);
v___x_1487_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1488_ = lean_string_dec_eq(v_str_1486_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1490_ = lean_string_dec_eq(v_str_1486_, v___x_1489_);
if (v___x_1490_ == 0)
{
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1492_ = lean_string_dec_eq(v_str_1485_, v___x_1491_);
if (v___x_1492_ == 0)
{
return v___x_1492_;
}
else
{
return v_suppressElabErrors_1481_;
}
}
}
else
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1494_ = lean_string_dec_eq(v_str_1485_, v___x_1493_);
if (v___x_1494_ == 0)
{
return v___x_1494_;
}
else
{
return v_suppressElabErrors_1481_;
}
}
}
case 1:
{
lean_object* v_pre_1495_; 
v_pre_1495_ = lean_ctor_get(v_pre_1484_, 0);
if (lean_obj_tag(v_pre_1495_) == 0)
{
lean_object* v_str_1496_; lean_object* v_str_1497_; lean_object* v_str_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v_str_1496_ = lean_ctor_get(v_x_1482_, 1);
v_str_1497_ = lean_ctor_get(v_pre_1483_, 1);
v_str_1498_ = lean_ctor_get(v_pre_1484_, 1);
v___x_1499_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1500_ = lean_string_dec_eq(v_str_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1502_ = lean_string_dec_eq(v_str_1497_, v___x_1501_);
if (v___x_1502_ == 0)
{
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1504_ = lean_string_dec_eq(v_str_1496_, v___x_1503_);
if (v___x_1504_ == 0)
{
return v___x_1504_;
}
else
{
return v_suppressElabErrors_1481_;
}
}
}
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = 0;
return v___x_1505_;
}
}
default: 
{
uint8_t v___x_1506_; 
v___x_1506_ = 0;
return v___x_1506_;
}
}
}
case 0:
{
lean_object* v_str_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_str_1507_ = lean_ctor_get(v_x_1482_, 1);
v___x_1508_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1509_ = lean_string_dec_eq(v_str_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
return v___x_1509_;
}
else
{
return v_suppressElabErrors_1481_;
}
}
default: 
{
uint8_t v___x_1510_; 
v___x_1510_ = 0;
return v___x_1510_;
}
}
}
else
{
uint8_t v___x_1511_; 
v___x_1511_ = 0;
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1512_, lean_object* v_x_1513_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1514_; uint8_t v_res_1515_; lean_object* v_r_1516_; 
v_suppressElabErrors_boxed_1514_ = lean_unbox(v_suppressElabErrors_1512_);
v_res_1515_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1514_, v_x_1513_);
lean_dec(v_x_1513_);
v_r_1516_ = lean_box(v_res_1515_);
return v_r_1516_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1517_, lean_object* v_opt_1518_){
_start:
{
lean_object* v_name_1519_; lean_object* v_defValue_1520_; lean_object* v_map_1521_; lean_object* v___x_1522_; 
v_name_1519_ = lean_ctor_get(v_opt_1518_, 0);
v_defValue_1520_ = lean_ctor_get(v_opt_1518_, 1);
v_map_1521_ = lean_ctor_get(v_opts_1517_, 0);
v___x_1522_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1521_, v_name_1519_);
if (lean_obj_tag(v___x_1522_) == 0)
{
uint8_t v___x_1523_; 
v___x_1523_ = lean_unbox(v_defValue_1520_);
return v___x_1523_;
}
else
{
lean_object* v_val_1524_; 
v_val_1524_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_val_1524_);
lean_dec_ref_known(v___x_1522_, 1);
if (lean_obj_tag(v_val_1524_) == 1)
{
uint8_t v_v_1525_; 
v_v_1525_ = lean_ctor_get_uint8(v_val_1524_, 0);
lean_dec_ref_known(v_val_1524_, 0);
return v_v_1525_;
}
else
{
uint8_t v___x_1526_; 
lean_dec(v_val_1524_);
v___x_1526_ = lean_unbox(v_defValue_1520_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1527_, lean_object* v_opt_1528_){
_start:
{
uint8_t v_res_1529_; lean_object* v_r_1530_; 
v_res_1529_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1527_, v_opt_1528_);
lean_dec_ref(v_opt_1528_);
lean_dec_ref(v_opts_1527_);
v_r_1530_ = lean_box(v_res_1529_);
return v_r_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1532_, lean_object* v_msgData_1533_, uint8_t v_severity_1534_, uint8_t v_isSilent_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_a_1541_; uint8_t v___y_1545_; lean_object* v___y_1546_; uint8_t v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_toCold_1552_; lean_object* v___y_1553_; lean_object* v___y_1581_; lean_object* v___y_1582_; uint8_t v___y_1583_; uint8_t v___y_1584_; lean_object* v___y_1585_; uint8_t v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; uint8_t v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; uint8_t v___y_1610_; uint8_t v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; uint8_t v___y_1617_; uint8_t v___y_1618_; uint8_t v___x_1628_; uint8_t v___y_1630_; uint8_t v___x_1636_; 
v___x_1628_ = 2;
v___x_1636_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1534_, v___x_1628_);
if (v___x_1636_ == 0)
{
v___y_1630_ = v___x_1636_;
goto v___jp_1629_;
}
else
{
uint8_t v___x_1637_; 
lean_inc_ref(v_msgData_1533_);
v___x_1637_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1533_);
if (v___x_1637_ == 0)
{
v___y_1630_ = v___x_1637_;
goto v___jp_1629_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_msgData_1533_);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v___y_1536_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
v___jp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_a_1541_);
lean_ctor_set(v___x_1542_, 1, v___y_1536_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
v___jp_1544_:
{
lean_object* v_currNamespace_1554_; lean_object* v_openDecls_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_env_1560_; lean_object* v_nextMacroScope_1561_; lean_object* v_ngen_1562_; lean_object* v_auxDeclNGen_1563_; lean_object* v_traceState_1564_; lean_object* v_cache_1565_; lean_object* v_recordedDeps_1566_; lean_object* v_messages_1567_; lean_object* v_infoState_1568_; lean_object* v_snapshotTasks_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1579_; 
v_currNamespace_1554_ = lean_ctor_get(v_toCold_1552_, 4);
v_openDecls_1555_ = lean_ctor_get(v_toCold_1552_, 5);
lean_inc(v_openDecls_1555_);
lean_inc(v_currNamespace_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_currNamespace_1554_);
lean_ctor_set(v___x_1556_, 1, v_openDecls_1555_);
v___x_1557_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___y_1548_);
lean_inc_ref(v___y_1549_);
lean_inc_ref(v___y_1550_);
v___x_1558_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1558_, 0, v___y_1550_);
lean_ctor_set(v___x_1558_, 1, v___y_1546_);
lean_ctor_set(v___x_1558_, 2, v___y_1551_);
lean_ctor_set(v___x_1558_, 3, v___y_1549_);
lean_ctor_set(v___x_1558_, 4, v___x_1557_);
lean_ctor_set_uint8(v___x_1558_, sizeof(void*)*5, v___y_1547_);
lean_ctor_set_uint8(v___x_1558_, sizeof(void*)*5 + 1, v___y_1545_);
lean_ctor_set_uint8(v___x_1558_, sizeof(void*)*5 + 2, v_isSilent_1535_);
v___x_1559_ = lean_st_ref_take(v___y_1553_);
v_env_1560_ = lean_ctor_get(v___x_1559_, 0);
v_nextMacroScope_1561_ = lean_ctor_get(v___x_1559_, 1);
v_ngen_1562_ = lean_ctor_get(v___x_1559_, 2);
v_auxDeclNGen_1563_ = lean_ctor_get(v___x_1559_, 3);
v_traceState_1564_ = lean_ctor_get(v___x_1559_, 4);
v_cache_1565_ = lean_ctor_get(v___x_1559_, 5);
v_recordedDeps_1566_ = lean_ctor_get(v___x_1559_, 6);
v_messages_1567_ = lean_ctor_get(v___x_1559_, 7);
v_infoState_1568_ = lean_ctor_get(v___x_1559_, 8);
v_snapshotTasks_1569_ = lean_ctor_get(v___x_1559_, 9);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1571_ = v___x_1559_;
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_snapshotTasks_1569_);
lean_inc(v_infoState_1568_);
lean_inc(v_messages_1567_);
lean_inc(v_recordedDeps_1566_);
lean_inc(v_cache_1565_);
lean_inc(v_traceState_1564_);
lean_inc(v_auxDeclNGen_1563_);
lean_inc(v_ngen_1562_);
lean_inc(v_nextMacroScope_1561_);
lean_inc(v_env_1560_);
lean_dec(v___x_1559_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = l_Lean_MessageLog_add(v___x_1558_, v_messages_1567_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 7, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_env_1560_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_nextMacroScope_1561_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_ngen_1562_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_auxDeclNGen_1563_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_traceState_1564_);
lean_ctor_set(v_reuseFailAlloc_1578_, 5, v_cache_1565_);
lean_ctor_set(v_reuseFailAlloc_1578_, 6, v_recordedDeps_1566_);
lean_ctor_set(v_reuseFailAlloc_1578_, 7, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1578_, 8, v_infoState_1568_);
lean_ctor_set(v_reuseFailAlloc_1578_, 9, v_snapshotTasks_1569_);
v___x_1576_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_st_ref_put(v___y_1553_, v___x_1576_);
v_a_1541_ = v___x_1573_;
goto v___jp_1540_;
}
}
}
v___jp_1580_:
{
lean_object* v_fileName_1589_; lean_object* v_fileMap_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1605_; 
v_fileName_1589_ = lean_ctor_get(v___y_1587_, 0);
v_fileMap_1590_ = lean_ctor_get(v___y_1587_, 1);
v___x_1591_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1533_);
v___x_1592_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1591_, v___y_1537_, v___y_1538_);
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1605_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1605_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
lean_inc_ref_n(v_fileMap_1590_, 2);
v___x_1597_ = l_Lean_FileMap_toPosition(v_fileMap_1590_, v___y_1585_);
lean_dec(v___y_1585_);
v___x_1598_ = l_Lean_FileMap_toPosition(v_fileMap_1590_, v___y_1588_);
lean_dec(v___y_1588_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 1);
lean_ctor_set(v___x_1595_, 0, v___x_1598_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; 
v___x_1601_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1586_ == 0)
{
lean_dec_ref(v___y_1581_);
v___y_1545_ = v___y_1583_;
v___y_1546_ = v___x_1597_;
v___y_1547_ = v___y_1584_;
v___y_1548_ = v_a_1593_;
v___y_1549_ = v___x_1601_;
v___y_1550_ = v_fileName_1589_;
v___y_1551_ = v___x_1600_;
v_toCold_1552_ = v___y_1582_;
v___y_1553_ = v___y_1538_;
goto v___jp_1544_;
}
else
{
uint8_t v___x_1602_; 
lean_inc(v_a_1593_);
v___x_1602_ = l_Lean_MessageData_hasTag(v___y_1581_, v_a_1593_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; 
lean_dec_ref(v___x_1600_);
lean_dec_ref(v___x_1597_);
lean_dec(v_a_1593_);
v___x_1603_ = lean_box(0);
v_a_1541_ = v___x_1603_;
goto v___jp_1540_;
}
else
{
v___y_1545_ = v___y_1583_;
v___y_1546_ = v___x_1597_;
v___y_1547_ = v___y_1584_;
v___y_1548_ = v_a_1593_;
v___y_1549_ = v___x_1601_;
v___y_1550_ = v_fileName_1589_;
v___y_1551_ = v___x_1600_;
v_toCold_1552_ = v___y_1582_;
v___y_1553_ = v___y_1538_;
goto v___jp_1544_;
}
}
}
}
}
v___jp_1606_:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Syntax_getTailPos_x3f(v___y_1612_, v___y_1611_);
lean_dec(v___y_1612_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_inc(v___y_1613_);
v___y_1581_ = v___y_1608_;
v___y_1582_ = v___y_1609_;
v___y_1583_ = v___y_1610_;
v___y_1584_ = v___y_1611_;
v___y_1585_ = v___y_1613_;
v___y_1586_ = v___y_1607_;
v___y_1587_ = v___y_1609_;
v___y_1588_ = v___y_1613_;
goto v___jp_1580_;
}
else
{
lean_object* v_val_1615_; 
v_val_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___y_1581_ = v___y_1608_;
v___y_1582_ = v___y_1609_;
v___y_1583_ = v___y_1610_;
v___y_1584_ = v___y_1611_;
v___y_1585_ = v___y_1613_;
v___y_1586_ = v___y_1607_;
v___y_1587_ = v___y_1609_;
v___y_1588_ = v_val_1615_;
goto v___jp_1580_;
}
}
v___jp_1616_:
{
lean_object* v_toCold_1619_; lean_object* v_ref_1620_; uint8_t v_suppressElabErrors_1621_; lean_object* v___x_1622_; lean_object* v___f_1623_; lean_object* v_ref_1624_; lean_object* v___x_1625_; 
v_toCold_1619_ = lean_ctor_get(v___y_1537_, 0);
v_ref_1620_ = lean_ctor_get(v___y_1537_, 2);
v_suppressElabErrors_1621_ = lean_ctor_get_uint8(v___y_1537_, sizeof(void*)*3 + 2);
v___x_1622_ = lean_box(v_suppressElabErrors_1621_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1623_, 0, v___x_1622_);
v_ref_1624_ = l_Lean_replaceRef(v_ref_1532_, v_ref_1620_);
v___x_1625_ = l_Lean_Syntax_getPos_x3f(v_ref_1624_, v___y_1617_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_unsigned_to_nat(0u);
v___y_1607_ = v_suppressElabErrors_1621_;
v___y_1608_ = v___f_1623_;
v___y_1609_ = v_toCold_1619_;
v___y_1610_ = v___y_1618_;
v___y_1611_ = v___y_1617_;
v___y_1612_ = v_ref_1624_;
v___y_1613_ = v___x_1626_;
goto v___jp_1606_;
}
else
{
lean_object* v_val_1627_; 
v_val_1627_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_val_1627_);
lean_dec_ref_known(v___x_1625_, 1);
v___y_1607_ = v_suppressElabErrors_1621_;
v___y_1608_ = v___f_1623_;
v___y_1609_ = v_toCold_1619_;
v___y_1610_ = v___y_1618_;
v___y_1611_ = v___y_1617_;
v___y_1612_ = v_ref_1624_;
v___y_1613_ = v_val_1627_;
goto v___jp_1606_;
}
}
v___jp_1629_:
{
uint8_t v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = 1;
v___x_1632_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1534_, v___x_1631_);
if (v___x_1632_ == 0)
{
v___y_1617_ = v___y_1630_;
v___y_1618_ = v_severity_1534_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1633_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1537_);
v___x_1634_ = l_Lean_warningAsError;
v___x_1635_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v___x_1633_, v___x_1634_);
lean_dec_ref(v___x_1633_);
if (v___x_1635_ == 0)
{
v___y_1617_ = v___y_1630_;
v___y_1618_ = v_severity_1534_;
goto v___jp_1616_;
}
else
{
v___y_1617_ = v___y_1630_;
v___y_1618_ = v___x_1628_;
goto v___jp_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1641_, lean_object* v_msgData_1642_, lean_object* v_severity_1643_, lean_object* v_isSilent_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v_severity_boxed_1649_; uint8_t v_isSilent_boxed_1650_; lean_object* v_res_1651_; 
v_severity_boxed_1649_ = lean_unbox(v_severity_1643_);
v_isSilent_boxed_1650_ = lean_unbox(v_isSilent_1644_);
v_res_1651_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1641_, v_msgData_1642_, v_severity_boxed_1649_, v_isSilent_boxed_1650_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v_ref_1641_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1652_, lean_object* v_msgData_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
uint8_t v___x_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = 2;
v___x_1659_ = 0;
v___x_1660_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1652_, v_msgData_1653_, v___x_1658_, v___x_1659_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1661_, lean_object* v_msgData_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1661_, v_msgData_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v_ref_1661_);
return v_res_1667_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1671_ = l_Lean_MessageData_ofFormat(v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1672_, lean_object* v_as_1673_, size_t v_sz_1674_, size_t v_i_1675_, uint8_t v_b_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_snd_1682_; lean_object* v_snd_1683_; lean_object* v_a_1689_; uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_lt(v_i_1675_, v_sz_1674_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = lean_box(v_b_1676_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v___y_1677_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1713_; uint8_t v_recovering_1714_; 
v_a_1712_ = lean_array_uget_borrowed(v_as_1673_, v_i_1675_);
v___x_1713_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1712_);
v_recovering_1714_ = l_Lean_Syntax_isOfKind(v_a_1712_, v___x_1713_);
if (v_recovering_1714_ == 0)
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_a_1712_);
v___x_1716_ = l_Lean_Syntax_isOfKind(v_a_1712_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1717_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1712_);
v___x_1718_ = l_Lean_Syntax_isOfKind(v_a_1712_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1677_);
v___x_1720_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1712_, v___x_1719_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v_snd_1722_; lean_object* v___x_1723_; 
lean_dec_ref(v___y_1677_);
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v_snd_1722_ = lean_ctor_get(v_a_1721_, 1);
lean_inc(v_snd_1722_);
lean_dec(v_a_1721_);
v___x_1723_ = lean_box(v_b_1676_);
v_snd_1682_ = v___x_1723_;
v_snd_1683_ = v_snd_1722_;
goto v___jp_1681_;
}
else
{
lean_object* v_a_1724_; 
v_a_1724_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1720_, 1);
v_a_1689_ = v_a_1724_;
goto v___jp_1688_;
}
}
else
{
lean_object* v___x_1725_; 
lean_inc_ref(v___y_1677_);
lean_inc(v_a_1712_);
v___x_1725_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1712_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v_snd_1727_; lean_object* v___x_1728_; 
lean_dec_ref(v___y_1677_);
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v_snd_1727_ = lean_ctor_get(v_a_1726_, 1);
lean_inc(v_snd_1727_);
lean_dec(v_a_1726_);
v___x_1728_ = lean_box(v_recovering_1714_);
v_snd_1682_ = v___x_1728_;
v_snd_1683_ = v_snd_1727_;
goto v___jp_1681_;
}
else
{
lean_object* v_a_1729_; 
v_a_1729_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1725_, 1);
v_a_1689_ = v_a_1729_;
goto v___jp_1688_;
}
}
}
else
{
lean_object* v___x_1730_; 
lean_inc_ref(v___y_1677_);
lean_inc(v_a_1712_);
v___x_1730_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1712_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v_snd_1732_; lean_object* v___x_1733_; 
lean_dec_ref(v___y_1677_);
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v_snd_1732_ = lean_ctor_get(v_a_1731_, 1);
lean_inc(v_snd_1732_);
lean_dec(v_a_1731_);
v___x_1733_ = lean_box(v_recovering_1714_);
v_snd_1682_ = v___x_1733_;
v_snd_1683_ = v_snd_1732_;
goto v___jp_1681_;
}
else
{
lean_object* v_a_1734_; 
v_a_1734_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1730_, 1);
v_a_1689_ = v_a_1734_;
goto v___jp_1688_;
}
}
}
else
{
if (v_b_1676_ == 0)
{
lean_object* v___x_1735_; 
lean_inc_ref(v___y_1677_);
lean_inc(v_a_1712_);
v___x_1735_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1712_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v_snd_1737_; lean_object* v___x_1738_; 
lean_dec_ref(v___y_1677_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v_snd_1737_ = lean_ctor_get(v_a_1736_, 1);
lean_inc(v_snd_1737_);
lean_dec(v_a_1736_);
v___x_1738_ = lean_box(v_b_1676_);
v_snd_1682_ = v___x_1738_;
v_snd_1683_ = v_snd_1737_;
goto v___jp_1681_;
}
else
{
lean_object* v_a_1739_; 
v_a_1739_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1735_, 1);
v_a_1689_ = v_a_1739_;
goto v___jp_1688_;
}
}
else
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_box(v_b_1676_);
v_snd_1682_ = v___x_1740_;
v_snd_1683_ = v___y_1677_;
goto v___jp_1681_;
}
}
}
v___jp_1681_:
{
size_t v___x_1684_; size_t v___x_1685_; uint8_t v___x_1686_; 
v___x_1684_ = ((size_t)1ULL);
v___x_1685_ = lean_usize_add(v_i_1675_, v___x_1684_);
v___x_1686_ = lean_unbox(v_snd_1682_);
lean_dec(v_snd_1682_);
v_i_1675_ = v___x_1685_;
v_b_1676_ = v___x_1686_;
v___y_1677_ = v_snd_1683_;
goto _start;
}
v___jp_1688_:
{
uint8_t v___x_1690_; 
v___x_1690_ = l_Lean_Exception_isInterrupt(v_a_1689_);
if (v___x_1690_ == 0)
{
uint8_t v___x_1691_; 
lean_inc_ref(v_a_1689_);
v___x_1691_ = l_Lean_Exception_isRuntime(v_a_1689_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = l_Lean_Exception_getRef(v_a_1689_);
v___x_1693_ = l_Lean_Exception_toMessageData(v_a_1689_);
v___x_1694_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1692_, v___x_1693_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___x_1692_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v_snd_1696_; lean_object* v___x_1697_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v_snd_1696_ = lean_ctor_get(v_a_1695_, 1);
lean_inc(v_snd_1696_);
lean_dec(v_a_1695_);
v___x_1697_ = lean_box(v_recovering_1672_);
v_snd_1682_ = v___x_1697_;
v_snd_1683_ = v_snd_1696_;
goto v___jp_1681_;
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1694_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1694_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
lean_object* v___x_1706_; 
lean_dec_ref(v___y_1677_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1689_);
return v___x_1706_;
}
}
else
{
lean_object* v___x_1707_; 
lean_dec_ref(v___y_1677_);
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_a_1689_);
return v___x_1707_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1741_, lean_object* v_as_1742_, lean_object* v_sz_1743_, lean_object* v_i_1744_, lean_object* v_b_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
uint8_t v_recovering_boxed_1750_; size_t v_sz_boxed_1751_; size_t v_i_boxed_1752_; uint8_t v_b_boxed_1753_; lean_object* v_res_1754_; 
v_recovering_boxed_1750_ = lean_unbox(v_recovering_1741_);
v_sz_boxed_1751_ = lean_unbox_usize(v_sz_1743_);
lean_dec(v_sz_1743_);
v_i_boxed_1752_ = lean_unbox_usize(v_i_1744_);
lean_dec(v_i_1744_);
v_b_boxed_1753_ = lean_unbox(v_b_1745_);
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1750_, v_as_1742_, v_sz_boxed_1751_, v_i_boxed_1752_, v_b_boxed_1753_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec_ref(v_as_1742_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_ref_1759_; lean_object* v___x_1760_; lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1769_; 
v_ref_1759_ = lean_ctor_get(v___y_1756_, 2);
v___x_1760_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1755_, v___y_1756_, v___y_1757_);
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1769_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1769_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
lean_inc(v_ref_1759_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_ref_1759_);
lean_ctor_set(v___x_1765_, 1, v_a_1761_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set_tag(v___x_1763_, 1);
lean_ctor_set(v___x_1763_, 0, v___x_1765_);
v___x_1767_ = v___x_1763_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1775_, lean_object* v_msg_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_toCold_1780_; lean_object* v_currRecDepth_1781_; lean_object* v_ref_1782_; uint16_t v_optionFlags_1783_; uint8_t v_suppressElabErrors_1784_; uint8_t v_checkDeprecated_1785_; uint8_t v_isRecordingDeps_1786_; lean_object* v_ref_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_toCold_1780_ = lean_ctor_get(v___y_1777_, 0);
v_currRecDepth_1781_ = lean_ctor_get(v___y_1777_, 1);
v_ref_1782_ = lean_ctor_get(v___y_1777_, 2);
v_optionFlags_1783_ = lean_ctor_get_uint16(v___y_1777_, sizeof(void*)*3);
v_suppressElabErrors_1784_ = lean_ctor_get_uint8(v___y_1777_, sizeof(void*)*3 + 2);
v_checkDeprecated_1785_ = lean_ctor_get_uint8(v___y_1777_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1786_ = lean_ctor_get_uint8(v___y_1777_, sizeof(void*)*3 + 4);
v_ref_1787_ = l_Lean_replaceRef(v_ref_1775_, v_ref_1782_);
lean_inc(v_currRecDepth_1781_);
lean_inc_ref(v_toCold_1780_);
v___x_1788_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1788_, 0, v_toCold_1780_);
lean_ctor_set(v___x_1788_, 1, v_currRecDepth_1781_);
lean_ctor_set(v___x_1788_, 2, v_ref_1787_);
lean_ctor_set_uint16(v___x_1788_, sizeof(void*)*3, v_optionFlags_1783_);
lean_ctor_set_uint8(v___x_1788_, sizeof(void*)*3 + 2, v_suppressElabErrors_1784_);
lean_ctor_set_uint8(v___x_1788_, sizeof(void*)*3 + 3, v_checkDeprecated_1785_);
lean_ctor_set_uint8(v___x_1788_, sizeof(void*)*3 + 4, v_isRecordingDeps_1786_);
v___x_1789_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1776_, v___x_1788_, v___y_1778_);
lean_dec_ref_known(v___x_1788_, 3);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1790_, lean_object* v_msg_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1790_, v_msg_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v_ref_1790_);
return v_res_1795_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1808_);
v___x_1813_ = l_Lean_Syntax_isOfKind(v_x_1808_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1815_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1808_, v___x_1814_, v_a_1809_, v_a_1810_);
lean_dec(v_x_1808_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v_recovering_1819_; 
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = l_Lean_Syntax_getArg(v_x_1808_, v___x_1816_);
v___x_1818_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1819_ = l_Lean_Syntax_isOfKind(v___x_1817_, v___x_1818_);
if (v_recovering_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1821_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1808_, v___x_1820_, v_a_1809_, v_a_1810_);
lean_dec(v_x_1808_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_xs_1824_; uint8_t v_recovering_1825_; lean_object* v___x_1826_; size_t v_sz_1827_; size_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1822_ = lean_unsigned_to_nat(1u);
v___x_1823_ = l_Lean_Syntax_getArg(v_x_1808_, v___x_1822_);
lean_dec(v_x_1808_);
v_xs_1824_ = l_Lean_Syntax_getArgs(v___x_1823_);
lean_dec(v___x_1823_);
v_recovering_1825_ = 0;
v___x_1826_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1824_);
lean_dec_ref(v_xs_1824_);
v_sz_1827_ = lean_array_size(v___x_1826_);
v___x_1828_ = ((size_t)0ULL);
v___x_1829_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1819_, v___x_1826_, v_sz_1827_, v___x_1828_, v_recovering_1825_, v___x_1829_, v_a_1809_, v_a_1810_);
lean_dec_ref(v___x_1826_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1841_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_snd_1835_; lean_object* v_items_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v_snd_1835_ = lean_ctor_get(v_a_1831_, 1);
lean_inc(v_snd_1835_);
lean_dec(v_a_1831_);
v_items_1836_ = lean_ctor_get(v_snd_1835_, 5);
lean_inc_ref(v_items_1836_);
lean_dec(v_snd_1835_);
v___x_1837_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1836_);
lean_dec_ref(v_items_1836_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1837_);
v___x_1839_ = v___x_1833_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1830_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1830_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lake_Toml_elabToml(v_x_1850_, v_a_1851_, v_a_1852_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1855_, lean_object* v_ref_1856_, lean_object* v_msg_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1856_, v_msg_1857_, v___y_1858_, v___y_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1862_, lean_object* v_ref_1863_, lean_object* v_msg_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1862_, v_ref_1863_, v_msg_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v_ref_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1869_, lean_object* v_msg_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1870_, v___y_1871_, v___y_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1875_, lean_object* v_msg_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1875_, v_msg_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
return v_res_1880_;
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
