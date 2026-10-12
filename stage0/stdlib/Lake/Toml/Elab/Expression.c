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
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(lean_object* v_value_24_){
_start:
{
lean_inc(v_value_24_);
return v_value_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg___boxed(lean_object* v_value_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(v_value_25_);
lean_dec(v_value_25_);
return v_res_26_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_value_30_){
_start:
{
lean_inc(v_value_30_);
return v_value_30_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_value_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(lean_box(0), v_t_28_, lean_box(0), v_value_30_);
stack->m_obj
 = v_res_31_;
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
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_stdTable_44_){
_start:
{
lean_inc(v_stdTable_44_);
return v_stdTable_44_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_stdTable_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(lean_box(0), v_t_42_, lean_box(0), v_stdTable_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_stdTable_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_stdTable_49_);
lean_dec(v_stdTable_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(lean_object* v_array_52_){
_start:
{
lean_inc(v_array_52_);
return v_array_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg___boxed(lean_object* v_array_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(v_array_53_);
lean_dec(v_array_53_);
return v_res_54_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_array_58_){
_start:
{
lean_inc(v_array_58_);
return v_array_58_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_array_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(lean_box(0), v_t_56_, lean_box(0), v_array_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_array_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_array_63_);
lean_dec(v_array_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(lean_object* v_dottedPrefix_66_){
_start:
{
lean_inc(v_dottedPrefix_66_);
return v_dottedPrefix_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg___boxed(lean_object* v_dottedPrefix_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(v_dottedPrefix_67_);
lean_dec(v_dottedPrefix_67_);
return v_res_68_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_dottedPrefix_72_){
_start:
{
lean_inc(v_dottedPrefix_72_);
return v_dottedPrefix_72_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_dottedPrefix_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(lean_box(0), v_t_70_, lean_box(0), v_dottedPrefix_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_dottedPrefix_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_dottedPrefix_77_);
lean_dec(v_dottedPrefix_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(lean_object* v_headerPrefix_80_){
_start:
{
lean_inc(v_headerPrefix_80_);
return v_headerPrefix_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg___boxed(lean_object* v_headerPrefix_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(v_headerPrefix_81_);
lean_dec(v_headerPrefix_81_);
return v_res_82_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_headerPrefix_86_){
_start:
{
lean_inc(v_headerPrefix_86_);
return v_headerPrefix_86_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_84_ = stack[1].m_num;
lean_object* v_headerPrefix_86_ = stack[3].m_obj;
lean_object* v_res_87_;
v_res_87_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(lean_box(0), v_t_84_, lean_box(0), v_headerPrefix_86_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_headerPrefix_91_){
_start:
{
uint8_t v_t_boxed_92_; lean_object* v_res_93_; 
v_t_boxed_92_ = lean_unbox(v_t_89_);
v_res_93_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(v_motive_88_, v_t_boxed_92_, v_h_90_, v_headerPrefix_91_);
lean_dec(v_headerPrefix_91_);
return v_res_93_;
}
}
static uint8_t _init_l_Lake_Toml_instInhabitedKeyTy_default(void){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
static uint8_t _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy(void){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(uint8_t v_ty_101_){
_start:
{
switch(v_ty_101_)
{
case 0:
{
lean_object* v___x_102_; 
v___x_102_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0));
return v___x_102_;
}
case 1:
{
lean_object* v___x_103_; 
v___x_103_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1));
return v___x_103_;
}
case 2:
{
lean_object* v___x_104_; 
v___x_104_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2));
return v___x_104_;
}
case 3:
{
lean_object* v___x_105_; 
v___x_105_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3));
return v___x_105_;
}
default: 
{
lean_object* v___x_106_; 
v___x_106_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4));
return v___x_106_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_ty_101_ = stack[0].m_num;
lean_object* v_res_107_;
v_res_107_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v_ty_101_);
stack->m_obj
 = v_res_107_;
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
uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(uint8_t v_ty_113_){
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
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix_0interp(lean_interpreter_value* stack)
{
uint8_t v_ty_113_ = stack[0].m_num;
uint8_t v_res_118_;
v_res_118_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(v_ty_113_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix___boxed(lean_object* v_ty_119_){
_start:
{
uint8_t v_ty_boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v_ty_boxed_120_ = lean_unbox(v_ty_119_);
v_res_121_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(v_ty_boxed_120_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_131_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
lean_ctor_set(v___x_137_, 2, v___x_136_);
lean_ctor_set(v___x_137_, 3, v___x_136_);
lean_ctor_set(v___x_137_, 4, v___x_135_);
lean_ctor_set(v___x_137_, 5, v___x_135_);
lean_ctor_set(v___x_137_, 6, v___x_135_);
lean_ctor_set(v___x_137_, 7, v___x_135_);
lean_ctor_set(v___x_137_, 8, v___x_135_);
lean_ctor_set(v___x_137_, 9, v___x_135_);
lean_ctor_set(v___x_137_, 10, v___x_135_);
lean_ctor_set(v___x_137_, 11, v___x_134_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_unsigned_to_nat(32u);
v___x_139_ = lean_mk_empty_array_with_capacity(v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_141_ = ((size_t)5ULL);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_unsigned_to_nat(32u);
v___x_144_ = lean_mk_empty_array_with_capacity(v___x_143_);
v___x_145_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3);
v___x_146_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
lean_ctor_set(v___x_146_, 2, v___x_142_);
lean_ctor_set(v___x_146_, 3, v___x_142_);
lean_ctor_set_usize(v___x_146_, 4, v___x_141_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_box(1);
v___x_148_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4);
v___x_149_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
lean_ctor_set(v___x_150_, 2, v___x_147_);
return v___x_150_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(lean_object* v_msgData_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; lean_object* v_toCold_156_; lean_object* v_env_157_; lean_object* v_options_158_; uint8_t v___x_159_; lean_object* v_env_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_155_ = lean_st_ref_get(v___y_153_);
v_toCold_156_ = lean_ctor_get(v___y_152_, 0);
v_env_157_ = lean_ctor_get(v___x_155_, 0);
lean_inc_ref(v_env_157_);
lean_dec(v___x_155_);
v_options_158_ = lean_ctor_get(v_toCold_156_, 2);
v___x_159_ = 0;
v_env_160_ = l_Lean_Environment_setRecordingDeps(v_env_157_, v___x_159_);
v___x_161_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2);
v___x_162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_158_);
v___x_163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_163_, 0, v_env_160_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_162_);
lean_ctor_set(v___x_163_, 3, v_options_158_);
v___x_164_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_msgData_151_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_151_ = stack[0].m_obj;
lean_object* v___y_152_ = stack[1].m_obj;
lean_object* v___y_153_ = stack[2].m_obj;
lean_object* v_res_166_;
v_res_166_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msgData_151_, v___y_152_, v___y_153_);
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msgData_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_171_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(lean_object* v_msg_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_ref_176_; lean_object* v___x_177_; lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_186_; 
v_ref_176_ = lean_ctor_get(v___y_173_, 2);
v___x_177_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_172_, v___y_173_, v___y_174_);
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_186_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
lean_inc(v_ref_176_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_ref_176_);
lean_ctor_set(v___x_182_, 1, v_a_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 1);
lean_ctor_set(v___x_180_, 0, v___x_182_);
v___x_184_ = v___x_180_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_172_ = stack[0].m_obj;
lean_object* v___y_173_ = stack[1].m_obj;
lean_object* v___y_174_ = stack[2].m_obj;
lean_object* v_res_187_;
v_res_187_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_172_, v___y_173_, v___y_174_);
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg___boxed(lean_object* v_msg_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_192_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(lean_object* v_ref_193_, lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_toCold_199_; lean_object* v_currRecDepth_200_; lean_object* v_ref_201_; uint16_t v_optionFlags_202_; uint8_t v_suppressElabErrors_203_; uint8_t v_isRecordingDeps_204_; lean_object* v_ref_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_toCold_199_ = lean_ctor_get(v___y_196_, 0);
v_currRecDepth_200_ = lean_ctor_get(v___y_196_, 1);
v_ref_201_ = lean_ctor_get(v___y_196_, 2);
v_optionFlags_202_ = lean_ctor_get_uint16(v___y_196_, sizeof(void*)*3);
v_suppressElabErrors_203_ = lean_ctor_get_uint8(v___y_196_, sizeof(void*)*3 + 2);
v_isRecordingDeps_204_ = lean_ctor_get_uint8(v___y_196_, sizeof(void*)*3 + 3);
v_ref_205_ = l_Lean_replaceRef(v_ref_193_, v_ref_201_);
lean_inc(v_currRecDepth_200_);
lean_inc_ref(v_toCold_199_);
v___x_206_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_206_, 0, v_toCold_199_);
lean_ctor_set(v___x_206_, 1, v_currRecDepth_200_);
lean_ctor_set(v___x_206_, 2, v_ref_205_);
lean_ctor_set_uint16(v___x_206_, sizeof(void*)*3, v_optionFlags_202_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*3 + 2, v_suppressElabErrors_203_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*3 + 3, v_isRecordingDeps_204_);
v___x_207_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_194_, v___x_206_, v___y_197_);
lean_dec_ref_known(v___x_206_, 3);
return v___x_207_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_193_ = stack[0].m_obj;
lean_object* v_msg_194_ = stack[1].m_obj;
lean_object* v___y_195_ = stack[2].m_obj;
lean_object* v___y_196_ = stack[3].m_obj;
lean_object* v___y_197_ = stack[4].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_193_, v_msg_194_, v___y_195_, v___y_196_, v___y_197_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object* v_ref_209_, lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_209_, v_msg_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v_ref_209_);
return v_res_215_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_218_ = l_Lean_stringToMessageData(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_221_ = l_Lean_stringToMessageData(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_224_ = l_Lean_stringToMessageData(v___x_223_);
return v___x_224_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object* v_as_225_, size_t v_i_226_, size_t v_stop_227_, lean_object* v_b_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_fst_234_; lean_object* v_snd_235_; uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_eq(v_i_226_, v_stop_227_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_array_uget_borrowed(v_as_225_, v_i_226_);
lean_inc(v___x_240_);
v___x_241_ = l_Lake_Toml_elabSimpleKey(v___x_240_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v_keyTys_243_; lean_object* v_arrKeyTys_244_; lean_object* v_arrParents_245_; lean_object* v_currArrKey_246_; lean_object* v_currKey_247_; lean_object* v_items_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v___x_241_, 1);
v_keyTys_243_ = lean_ctor_get(v___y_229_, 0);
v_arrKeyTys_244_ = lean_ctor_get(v___y_229_, 1);
v_arrParents_245_ = lean_ctor_get(v___y_229_, 2);
v_currArrKey_246_ = lean_ctor_get(v___y_229_, 3);
v_currKey_247_ = lean_ctor_get(v___y_229_, 4);
v_items_248_ = lean_ctor_get(v___y_229_, 5);
v___x_249_ = l_Lean_Name_str___override(v_b_228_, v_a_242_);
v___x_250_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_243_, v___x_249_);
if (lean_obj_tag(v___x_250_) == 1)
{
lean_object* v_val_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_281_; 
v_val_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_281_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_281_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_val_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_281_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
uint8_t v___x_255_; 
v___x_255_ = lean_unbox(v_val_251_);
if (v___x_255_ == 3)
{
lean_del_object(v___x_253_);
lean_dec(v_val_251_);
v_fst_234_ = v___x_249_;
v_snd_235_ = v___y_229_;
goto v___jp_233_;
}
else
{
lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_256_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_257_ = lean_unbox(v_val_251_);
lean_dec(v_val_251_);
v___x_258_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_257_);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 3);
lean_ctor_set(v___x_253_, 0, v___x_258_);
v___x_260_ = v___x_253_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_280_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_261_ = l_Lean_MessageData_ofFormat(v___x_260_);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_256_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
lean_inc(v___x_249_);
v___x_265_ = l_Lean_MessageData_ofName(v___x_249_);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_240_, v___x_268_, v___y_229_, v___y_230_, v___y_231_);
lean_dec_ref(v___y_229_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v_snd_271_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_269_, 1);
v_snd_271_ = lean_ctor_get(v_a_270_, 1);
lean_inc(v_snd_271_);
lean_dec(v_a_270_);
v_fst_234_ = v___x_249_;
v_snd_235_ = v_snd_271_;
goto v___jp_233_;
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec(v___x_249_);
v_a_272_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_269_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_269_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_291_; 
lean_inc_ref(v_items_248_);
lean_inc(v_currKey_247_);
lean_inc(v_currArrKey_246_);
lean_inc(v_arrParents_245_);
lean_inc(v_arrKeyTys_244_);
lean_inc(v_keyTys_243_);
lean_dec(v___x_250_);
v_isSharedCheck_291_ = !lean_is_exclusive(v___y_229_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; lean_object* v_unused_293_; lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; 
v_unused_292_ = lean_ctor_get(v___y_229_, 5);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v___y_229_, 4);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v___y_229_, 3);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v___y_229_, 2);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v___y_229_, 1);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v___y_229_, 0);
lean_dec(v_unused_297_);
v___x_283_ = v___y_229_;
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
else
{
lean_dec(v___y_229_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_285_ = 3;
v___x_286_ = lean_box(v___x_285_);
lean_inc(v___x_249_);
v___x_287_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_249_, v___x_286_, v_keyTys_243_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_287_);
v___x_289_ = v___x_283_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_arrKeyTys_244_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_arrParents_245_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_currArrKey_246_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v_currKey_247_);
lean_ctor_set(v_reuseFailAlloc_290_, 5, v_items_248_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
v_fst_234_ = v___x_249_;
v_snd_235_ = v___x_289_;
goto v___jp_233_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v___y_229_);
lean_dec(v_b_228_);
v_a_298_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_241_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_241_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_b_228_);
lean_ctor_set(v___x_306_, 1, v___y_229_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
v___jp_233_:
{
size_t v___x_236_; size_t v___x_237_; 
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_add(v_i_226_, v___x_236_);
v_i_226_ = v___x_237_;
v_b_228_ = v_fst_234_;
v___y_229_ = v_snd_235_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_225_ = stack[0].m_obj;
size_t v_i_226_ = stack[1].m_num;
size_t v_stop_227_ = stack[2].m_num;
lean_object* v_b_228_ = stack[3].m_obj;
lean_object* v___y_229_ = stack[4].m_obj;
lean_object* v___y_230_ = stack[5].m_obj;
lean_object* v___y_231_ = stack[6].m_obj;
lean_object* v_res_308_;
v_res_308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_225_, v_i_226_, v_stop_227_, v_b_228_, v___y_229_, v___y_230_, v___y_231_);
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object* v_as_309_, lean_object* v_i_310_, lean_object* v_stop_311_, lean_object* v_b_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
size_t v_i_boxed_317_; size_t v_stop_boxed_318_; lean_object* v_res_319_; 
v_i_boxed_317_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v_stop_boxed_318_ = lean_unbox_usize(v_stop_311_);
lean_dec(v_stop_311_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_309_, v_i_boxed_317_, v_stop_boxed_318_, v_b_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec_ref(v_as_309_);
return v_res_319_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object* v_ks_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_currKey_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_currKey_325_ = lean_ctor_get(v_a_321_, 4);
lean_inc(v_currKey_325_);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_array_get_size(v_ks_320_);
v___x_328_ = lean_nat_dec_lt(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_currKey_325_);
lean_ctor_set(v___x_329_, 1, v_a_321_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
else
{
uint8_t v___x_331_; 
v___x_331_ = lean_nat_dec_le(v___x_327_, v___x_327_);
if (v___x_331_ == 0)
{
if (v___x_328_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_currKey_325_);
lean_ctor_set(v___x_332_, 1, v_a_321_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
else
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((size_t)0ULL);
v___x_335_ = lean_usize_of_nat(v___x_327_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_320_, v___x_334_, v___x_335_, v_currKey_325_, v_a_321_, v_a_322_, v_a_323_);
return v___x_336_;
}
}
else
{
size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((size_t)0ULL);
v___x_338_ = lean_usize_of_nat(v___x_327_);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_320_, v___x_337_, v___x_338_, v_currKey_325_, v_a_321_, v_a_322_, v_a_323_);
return v___x_339_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_0interp(lean_interpreter_value* stack)
{
lean_object* v_ks_320_ = stack[0].m_obj;
lean_object* v_a_321_ = stack[1].m_obj;
lean_object* v_a_322_ = stack[2].m_obj;
lean_object* v_a_323_ = stack[3].m_obj;
lean_object* v_res_340_;
v_res_340_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_320_, v_a_321_, v_a_322_, v_a_323_);
stack->m_obj
 = v_res_340_;
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
lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_347_, lean_object* v_ref_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_348_, v_msg_349_, v___y_350_, v___y_351_, v___y_352_);
return v___x_354_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_348_ = stack[1].m_obj;
lean_object* v_msg_349_ = stack[2].m_obj;
lean_object* v___y_350_ = stack[3].m_obj;
lean_object* v___y_351_ = stack[4].m_obj;
lean_object* v___y_352_ = stack[5].m_obj;
lean_object* v_res_355_;
v_res_355_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_box(0), v_ref_348_, v_msg_349_, v___y_350_, v___y_351_, v___y_352_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_356_, lean_object* v_ref_357_, lean_object* v_msg_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_356_, v_ref_357_, v_msg_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v_ref_357_);
return v_res_363_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_364_, lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_365_, v___y_367_, v___y_368_);
return v___x_370_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_365_ = stack[1].m_obj;
lean_object* v___y_366_ = stack[2].m_obj;
lean_object* v___y_367_ = stack[3].m_obj;
lean_object* v___y_368_ = stack[4].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_box(0), v_msg_365_, v___y_366_, v___y_367_, v___y_368_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_372_, lean_object* v_msg_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_372_, v_msg_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_378_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_379_, lean_object* v_as_380_, size_t v_i_381_, size_t v_stop_382_, lean_object* v_b_383_){
_start:
{
lean_object* v___y_385_; uint8_t v___x_389_; 
v___x_389_ = lean_usize_dec_eq(v_i_381_, v_stop_382_);
if (v___x_389_ == 0)
{
lean_object* v_fst_390_; uint8_t v___x_391_; 
v_fst_390_ = lean_ctor_get(v_b_383_, 0);
v___x_391_ = lean_unbox(v_fst_390_);
if (v___x_391_ == 0)
{
lean_object* v_snd_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
v_snd_392_ = lean_ctor_get(v_b_383_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_b_383_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v_b_383_, 0);
lean_dec(v_unused_401_);
v___x_394_ = v_b_383_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_snd_392_);
lean_dec(v_b_383_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = lean_box(v___x_379_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_snd_392_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
v___y_385_ = v___x_398_;
goto v___jp_384_;
}
}
}
else
{
lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_412_; 
v_snd_402_ = lean_ctor_get(v_b_383_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_b_383_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v_b_383_, 0);
lean_dec(v_unused_413_);
v___x_404_ = v_b_383_;
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_dec(v_b_383_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_406_ = lean_array_uget_borrowed(v_as_380_, v_i_381_);
lean_inc(v___x_406_);
v___x_407_ = lean_array_push(v_snd_402_, v___x_406_);
v___x_408_ = lean_box(v___x_389_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_407_);
lean_ctor_set(v___x_404_, 0, v___x_408_);
v___x_410_ = v___x_404_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_407_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
v___y_385_ = v___x_410_;
goto v___jp_384_;
}
}
}
}
else
{
return v_b_383_;
}
v___jp_384_:
{
size_t v___x_386_; size_t v___x_387_; 
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_add(v_i_381_, v___x_386_);
v_i_381_ = v___x_387_;
v_b_383_ = v___y_385_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_379_ = stack[0].m_num;
lean_object* v_as_380_ = stack[1].m_obj;
size_t v_i_381_ = stack[2].m_num;
size_t v_stop_382_ = stack[3].m_num;
lean_object* v_b_383_ = stack[4].m_obj;
lean_object* v_res_414_;
v_res_414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_379_, v_as_380_, v_i_381_, v_stop_382_, v_b_383_);
stack->m_obj
 = v_res_414_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_415_, lean_object* v_as_416_, lean_object* v_i_417_, lean_object* v_stop_418_, lean_object* v_b_419_){
_start:
{
uint8_t v___x_2936__boxed_420_; size_t v_i_boxed_421_; size_t v_stop_boxed_422_; lean_object* v_res_423_; 
v___x_2936__boxed_420_ = lean_unbox(v___x_415_);
v_i_boxed_421_ = lean_unbox_usize(v_i_417_);
lean_dec(v_i_417_);
v_stop_boxed_422_ = lean_unbox_usize(v_stop_418_);
lean_dec(v_stop_418_);
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2936__boxed_420_, v_as_416_, v_i_boxed_421_, v_stop_boxed_422_, v_b_419_);
lean_dec_ref(v_as_416_);
return v_res_423_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_431_, size_t v_i_432_, lean_object* v_bs_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_432_, v_sz_431_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v_bs_433_);
return v___x_435_;
}
else
{
lean_object* v_v_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_v_436_ = lean_array_uget(v_bs_433_, v_i_432_);
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_436_);
v___x_438_ = l_Lean_Syntax_isOfKind(v_v_436_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_dec(v_v_436_);
lean_dec_ref(v_bs_433_);
v___x_439_ = lean_box(0);
return v___x_439_;
}
else
{
lean_object* v___x_440_; lean_object* v_bs_x27_441_; size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v_bs_x27_441_ = lean_array_uset(v_bs_433_, v_i_432_, v___x_440_);
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_add(v_i_432_, v___x_442_);
v___x_444_ = lean_array_uset(v_bs_x27_441_, v_i_432_, v_v_436_);
v_i_432_ = v___x_443_;
v_bs_433_ = v___x_444_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_431_ = stack[0].m_num;
size_t v_i_432_ = stack[1].m_num;
lean_object* v_bs_433_ = stack[2].m_obj;
lean_object* v_res_446_;
v_res_446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_431_, v_i_432_, v_bs_433_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_447_, lean_object* v_i_448_, lean_object* v_bs_449_){
_start:
{
size_t v_sz_boxed_450_; size_t v_i_boxed_451_; lean_object* v_res_452_; 
v_sz_boxed_450_ = lean_unbox_usize(v_sz_447_);
lean_dec(v_sz_447_);
v_i_boxed_451_ = lean_unbox_usize(v_i_448_);
lean_dec(v_i_448_);
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_450_, v_i_boxed_451_, v_bs_449_);
return v_res_452_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_471_);
v___x_477_ = l_Lean_Syntax_isOfKind(v_kv_471_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_479_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_471_, v___x_478_, v_a_472_, v_a_473_, v_a_474_);
lean_dec_ref(v_a_472_);
lean_dec(v_kv_471_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = l_Lean_Syntax_getArg(v_kv_471_, v___x_480_);
v___x_482_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_481_);
v___x_483_ = l_Lean_Syntax_isOfKind(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_kv_471_);
v___x_484_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_485_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_481_, v___x_484_, v_a_472_, v_a_473_, v_a_474_);
lean_dec_ref(v_a_472_);
lean_dec(v___x_481_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; lean_object* v_v_487_; lean_object* v___y_489_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_486_ = lean_unsigned_to_nat(2u);
v_v_487_ = l_Lean_Syntax_getArg(v_kv_471_, v___x_486_);
lean_dec(v_kv_471_);
v___x_595_ = l_Lean_Syntax_getArg(v___x_481_, v___x_480_);
v___x_596_ = l_Lean_Syntax_getArgs(v___x_595_);
lean_dec(v___x_595_);
v___x_597_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_598_ = lean_array_get_size(v___x_596_);
v___x_599_ = lean_nat_dec_lt(v___x_480_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec_ref(v___x_596_);
v___y_489_ = v___x_597_;
goto v___jp_488_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; lean_object* v_snd_605_; 
v___x_600_ = lean_box(v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_597_);
v___x_602_ = ((size_t)0ULL);
v___x_603_ = lean_usize_of_nat(v___x_598_);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_483_, v___x_596_, v___x_602_, v___x_603_, v___x_601_);
lean_dec_ref(v___x_596_);
v_snd_605_ = lean_ctor_get(v___x_604_, 1);
lean_inc(v_snd_605_);
lean_dec_ref(v___x_604_);
v___y_489_ = v_snd_605_;
goto v___jp_488_;
}
v___jp_488_:
{
size_t v_sz_490_; size_t v___x_491_; lean_object* v___x_492_; 
v_sz_490_ = lean_array_size(v___y_489_);
v___x_491_ = ((size_t)0ULL);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_490_, v___x_491_, v___y_489_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v_v_487_);
v___x_493_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_494_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_481_, v___x_493_, v_a_472_, v_a_473_, v_a_474_);
lean_dec_ref(v_a_472_);
lean_dec(v___x_481_);
return v___x_494_;
}
else
{
lean_object* v_val_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_tailKeyStx_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_val_495_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v___x_492_, 1);
v___x_496_ = lean_box(0);
v___x_497_ = lean_array_get_size(v_val_495_);
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_sub(v___x_497_, v___x_498_);
v_tailKeyStx_500_ = lean_array_get(v___x_496_, v_val_495_, v___x_499_);
lean_dec(v___x_499_);
v___x_501_ = lean_array_pop(v_val_495_);
v___x_502_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_501_, v_a_472_, v_a_473_, v_a_474_);
lean_dec_ref(v___x_501_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v_fst_504_; lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_586_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v_fst_504_ = lean_ctor_get(v_a_503_, 0);
v_snd_505_ = lean_ctor_get(v_a_503_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_586_ == 0)
{
v___x_507_ = v_a_503_;
v_isShared_508_ = v_isSharedCheck_586_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_inc(v_fst_504_);
lean_dec(v_a_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_586_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; 
lean_inc(v_tailKeyStx_500_);
v___x_509_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_500_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v_keyTys_511_; lean_object* v_arrKeyTys_512_; lean_object* v_arrParents_513_; lean_object* v_currArrKey_514_; lean_object* v_currKey_515_; lean_object* v_items_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v_keyTys_511_ = lean_ctor_get(v_snd_505_, 0);
v_arrKeyTys_512_ = lean_ctor_get(v_snd_505_, 1);
v_arrParents_513_ = lean_ctor_get(v_snd_505_, 2);
v_currArrKey_514_ = lean_ctor_get(v_snd_505_, 3);
v_currKey_515_ = lean_ctor_get(v_snd_505_, 4);
v_items_516_ = lean_ctor_get(v_snd_505_, 5);
v___x_517_ = l_Lean_Name_str___override(v_fst_504_, v_a_510_);
v___x_518_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_511_, v___x_517_);
if (lean_obj_tag(v___x_518_) == 1)
{
lean_object* v_val_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_538_; 
lean_del_object(v___x_507_);
lean_dec(v_v_487_);
lean_dec(v___x_481_);
v_val_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_538_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_val_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_523_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_524_ = lean_unbox(v_val_519_);
lean_dec(v_val_519_);
v___x_525_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_524_);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 3);
lean_ctor_set(v___x_521_, 0, v___x_525_);
v___x_527_ = v___x_521_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_537_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_528_ = l_Lean_MessageData_ofFormat(v___x_527_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_523_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_MessageData_ofName(v___x_517_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_500_, v___x_535_, v_snd_505_, v_a_473_, v_a_474_);
lean_dec(v_snd_505_);
lean_dec(v_tailKeyStx_500_);
return v___x_536_;
}
}
}
else
{
lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_571_; 
lean_inc_ref(v_items_516_);
lean_inc(v_currKey_515_);
lean_inc(v_currArrKey_514_);
lean_inc(v_arrParents_513_);
lean_inc(v_arrKeyTys_512_);
lean_inc(v_keyTys_511_);
lean_dec(v___x_518_);
lean_dec(v_tailKeyStx_500_);
v_isSharedCheck_571_ = !lean_is_exclusive(v_snd_505_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; lean_object* v_unused_576_; lean_object* v_unused_577_; 
v_unused_572_ = lean_ctor_get(v_snd_505_, 5);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_snd_505_, 4);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_snd_505_, 3);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_snd_505_, 2);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_snd_505_, 1);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_snd_505_, 0);
lean_dec(v_unused_577_);
v___x_540_ = v_snd_505_;
v_isShared_541_ = v_isSharedCheck_571_;
goto v_resetjp_539_;
}
else
{
lean_dec(v_snd_505_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_571_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lake_Toml_elabVal(v_v_487_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_562_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_562_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_562_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_562_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_547_ = lean_box(0);
v___x_548_ = 0;
v___x_549_ = lean_box(v___x_548_);
lean_inc(v___x_517_);
v___x_550_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_517_, v___x_549_, v_keyTys_511_);
v___x_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_551_, 0, v___x_481_);
lean_ctor_set(v___x_551_, 1, v___x_517_);
lean_ctor_set(v___x_551_, 2, v_a_543_);
v___x_552_ = lean_array_push(v_items_516_, v___x_551_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 5, v___x_552_);
lean_ctor_set(v___x_540_, 0, v___x_550_);
v___x_554_ = v___x_540_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_arrKeyTys_512_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_arrParents_513_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_currArrKey_514_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_currKey_515_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v___x_552_);
v___x_554_ = v_reuseFailAlloc_561_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_554_);
lean_ctor_set(v___x_507_, 0, v___x_547_);
v___x_556_ = v___x_507_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_556_);
v___x_558_ = v___x_545_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_540_);
lean_dec(v___x_517_);
lean_dec_ref(v_items_516_);
lean_dec(v_currKey_515_);
lean_dec(v_currArrKey_514_);
lean_dec(v_arrParents_513_);
lean_dec(v_arrKeyTys_512_);
lean_dec(v_keyTys_511_);
lean_del_object(v___x_507_);
lean_dec(v___x_481_);
v_a_563_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_542_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_542_);
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
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_del_object(v___x_507_);
lean_dec(v_snd_505_);
lean_dec(v_fst_504_);
lean_dec(v_tailKeyStx_500_);
lean_dec(v_v_487_);
lean_dec(v___x_481_);
v_a_578_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_509_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_509_);
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
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec(v_tailKeyStx_500_);
lean_dec(v_v_487_);
lean_dec(v___x_481_);
v_a_587_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_502_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_502_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_0interp(lean_interpreter_value* stack)
{
lean_object* v_kv_471_ = stack[0].m_obj;
lean_object* v_a_472_ = stack[1].m_obj;
lean_object* v_a_473_ = stack[2].m_obj;
lean_object* v_a_474_ = stack[3].m_obj;
lean_object* v_res_606_;
v_res_606_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_471_, v_a_472_, v_a_473_, v_a_474_);
stack->m_obj
 = v_res_606_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_616_, size_t v_i_617_, size_t v_stop_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
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
lean_dec_ref_known(v___x_632_, 1);
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
lean_dec_ref_known(v___x_650_, 1);
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
lean_dec_ref_known(v___x_660_, 1);
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
lean_dec_ref_known(v___x_691_, 1);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_616_ = stack[0].m_obj;
size_t v_i_617_ = stack[1].m_num;
size_t v_stop_618_ = stack[2].m_num;
lean_object* v_b_619_ = stack[3].m_obj;
lean_object* v___y_620_ = stack[4].m_obj;
lean_object* v___y_621_ = stack[5].m_obj;
lean_object* v___y_622_ = stack[6].m_obj;
lean_object* v_res_730_;
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_616_, v_i_617_, v_stop_618_, v_b_619_, v___y_620_, v___y_621_, v___y_622_);
stack->m_obj
 = v_res_730_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_731_, lean_object* v_i_732_, lean_object* v_stop_733_, lean_object* v_b_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
size_t v_i_boxed_739_; size_t v_stop_boxed_740_; lean_object* v_res_741_; 
v_i_boxed_739_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_stop_boxed_740_ = lean_unbox_usize(v_stop_733_);
lean_dec(v_stop_733_);
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_731_, v_i_boxed_739_, v_stop_boxed_740_, v_b_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec_ref(v_as_731_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_742_, lean_object* v_k_743_){
_start:
{
if (lean_obj_tag(v_t_742_) == 0)
{
lean_object* v_k_744_; lean_object* v_v_745_; lean_object* v_l_746_; lean_object* v_r_747_; uint8_t v___x_748_; 
v_k_744_ = lean_ctor_get(v_t_742_, 1);
v_v_745_ = lean_ctor_get(v_t_742_, 2);
v_l_746_ = lean_ctor_get(v_t_742_, 3);
v_r_747_ = lean_ctor_get(v_t_742_, 4);
v___x_748_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_743_, v_k_744_);
switch(v___x_748_)
{
case 0:
{
v_t_742_ = v_l_746_;
goto _start;
}
case 1:
{
lean_object* v___x_750_; 
lean_inc(v_v_745_);
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v_v_745_);
return v___x_750_;
}
default: 
{
v_t_742_ = v_r_747_;
goto _start;
}
}
}
else
{
lean_object* v___x_752_; 
v___x_752_ = lean_box(0);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_753_, lean_object* v_k_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_753_, v_k_754_);
lean_dec(v_k_754_);
lean_dec(v_t_753_);
return v_res_755_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_keyTys_761_; lean_object* v_arrKeyTys_762_; lean_object* v_arrParents_763_; lean_object* v_currArrKey_764_; lean_object* v_currKey_765_; lean_object* v_items_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_794_; 
v_keyTys_761_ = lean_ctor_get(v_a_757_, 0);
v_arrKeyTys_762_ = lean_ctor_get(v_a_757_, 1);
v_arrParents_763_ = lean_ctor_get(v_a_757_, 2);
v_currArrKey_764_ = lean_ctor_get(v_a_757_, 3);
v_currKey_765_ = lean_ctor_get(v_a_757_, 4);
v_items_766_ = lean_ctor_get(v_a_757_, 5);
v_isSharedCheck_794_ = !lean_is_exclusive(v_a_757_);
if (v_isSharedCheck_794_ == 0)
{
v___x_768_ = v_a_757_;
v_isShared_769_ = v_isSharedCheck_794_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_items_766_);
lean_inc(v_currKey_765_);
lean_inc(v_currArrKey_764_);
lean_inc(v_arrParents_763_);
lean_inc(v_arrKeyTys_762_);
lean_inc(v_keyTys_761_);
lean_dec(v_a_757_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_794_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_arrKeyTys_770_; lean_object* v___x_771_; lean_object* v___y_773_; lean_object* v___x_791_; 
v_arrKeyTys_770_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_764_, v_keyTys_761_, v_arrKeyTys_762_);
v___x_771_ = lean_box(0);
v___x_791_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_770_, v___x_771_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_box(1);
v___y_773_ = v___x_792_;
goto v___jp_772_;
}
else
{
lean_object* v_val_793_; 
v_val_793_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v___x_791_, 1);
v___y_773_ = v_val_793_;
goto v___jp_772_;
}
v___jp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 3, v___x_771_);
lean_ctor_set(v___x_768_, 1, v_arrKeyTys_770_);
lean_ctor_set(v___x_768_, 0, v___y_773_);
v___x_775_ = v___x_768_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___y_773_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_arrKeyTys_770_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_arrParents_763_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_currKey_765_);
lean_ctor_set(v_reuseFailAlloc_790_, 5, v_items_766_);
v___x_775_ = v_reuseFailAlloc_790_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_array_get_size(v_ks_756_);
v___x_778_ = lean_nat_dec_lt(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_771_);
lean_ctor_set(v___x_779_, 1, v___x_775_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = lean_nat_dec_le(v___x_777_, v___x_777_);
if (v___x_781_ == 0)
{
if (v___x_778_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_771_);
lean_ctor_set(v___x_782_, 1, v___x_775_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
else
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((size_t)0ULL);
v___x_785_ = lean_usize_of_nat(v___x_777_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_756_, v___x_784_, v___x_785_, v___x_771_, v___x_775_, v_a_758_, v_a_759_);
return v___x_786_;
}
}
else
{
size_t v___x_787_; size_t v___x_788_; lean_object* v___x_789_; 
v___x_787_ = ((size_t)0ULL);
v___x_788_ = lean_usize_of_nat(v___x_777_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_756_, v___x_787_, v___x_788_, v___x_771_, v___x_775_, v_a_758_, v_a_759_);
return v___x_789_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_0interp(lean_interpreter_value* stack)
{
lean_object* v_ks_756_ = stack[0].m_obj;
lean_object* v_a_757_ = stack[1].m_obj;
lean_object* v_a_758_ = stack[2].m_obj;
lean_object* v_a_759_ = stack[3].m_obj;
lean_object* v_res_795_;
v_res_795_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_756_, v_a_757_, v_a_758_, v_a_759_);
stack->m_obj
 = v_res_795_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_796_, v_a_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec_ref(v_ks_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_802_, lean_object* v_t_803_, lean_object* v_k_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_803_, v_k_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_806_, lean_object* v_t_807_, lean_object* v_k_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_806_, v_t_807_, v_k_808_);
lean_dec(v_k_808_);
lean_dec(v_t_807_);
return v_res_809_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0(void){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_810_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
v___x_818_ = l_Lean_stringToMessageData(v___x_817_);
return v___x_818_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___y_825_; lean_object* v_keyTys_826_; lean_object* v_arrKeyTys_827_; lean_object* v_arrParents_828_; lean_object* v_currArrKey_829_; lean_object* v_items_830_; lean_object* v_toCold_842_; lean_object* v_currRecDepth_843_; lean_object* v_ref_844_; uint16_t v_optionFlags_845_; uint8_t v_suppressElabErrors_846_; uint8_t v_isRecordingDeps_847_; lean_object* v___x_848_; uint8_t v___x_849_; lean_object* v_ref_850_; lean_object* v___x_851_; 
v_toCold_842_ = lean_ctor_get(v_a_821_, 0);
v_currRecDepth_843_ = lean_ctor_get(v_a_821_, 1);
v_ref_844_ = lean_ctor_get(v_a_821_, 2);
v_optionFlags_845_ = lean_ctor_get_uint16(v_a_821_, sizeof(void*)*3);
v_suppressElabErrors_846_ = lean_ctor_get_uint8(v_a_821_, sizeof(void*)*3 + 2);
v_isRecordingDeps_847_ = lean_ctor_get_uint8(v_a_821_, sizeof(void*)*3 + 3);
v___x_848_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_819_);
v___x_849_ = l_Lean_Syntax_isOfKind(v_x_819_, v___x_848_);
v_ref_850_ = l_Lean_replaceRef(v_x_819_, v_ref_844_);
lean_inc(v_currRecDepth_843_);
lean_inc_ref(v_toCold_842_);
v___x_851_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_851_, 0, v_toCold_842_);
lean_ctor_set(v___x_851_, 1, v_currRecDepth_843_);
lean_ctor_set(v___x_851_, 2, v_ref_850_);
lean_ctor_set_uint16(v___x_851_, sizeof(void*)*3, v_optionFlags_845_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*3 + 2, v_suppressElabErrors_846_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*3 + 3, v_isRecordingDeps_847_);
if (v___x_849_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4);
v___x_853_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_819_, v___x_852_, v_a_820_, v___x_851_, v_a_822_);
lean_dec_ref_known(v___x_851_, 3);
lean_dec_ref(v_a_820_);
lean_dec(v_x_819_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___y_857_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = l_Lean_Syntax_getArg(v_x_819_, v___x_854_);
v___x_925_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_855_);
v___x_926_ = l_Lean_Syntax_isOfKind(v___x_855_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v_x_819_);
v___x_927_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_928_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_855_, v___x_927_, v_a_820_, v___x_851_, v_a_822_);
lean_dec_ref_known(v___x_851_, 3);
lean_dec_ref(v_a_820_);
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
lean_dec(v_x_819_);
v___x_861_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_862_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_855_, v___x_861_, v_a_820_, v___x_851_, v_a_822_);
lean_dec_ref_known(v___x_851_, 3);
lean_dec_ref(v_a_820_);
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
v___x_869_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_868_, v_a_820_, v___x_851_, v_a_822_);
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
v___x_876_ = l_Lake_Toml_elabSimpleKey(v_tailKey_867_, v___x_851_, v_a_822_);
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
lean_dec_ref_known(v___x_851_, 3);
v___y_825_ = v___x_883_;
v_keyTys_826_ = v_keyTys_878_;
v_arrKeyTys_827_ = v_arrKeyTys_879_;
v_arrParents_828_ = v_arrParents_880_;
v_currArrKey_829_ = v_currArrKey_881_;
v_items_830_ = v_items_882_;
goto v___jp_824_;
}
else
{
lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
lean_dec(v_x_819_);
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
v___x_904_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_867_, v___x_903_, v_snd_872_, v___x_851_, v_a_822_);
lean_dec_ref_known(v___x_851_, 3);
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
lean_dec_ref_known(v___x_851_, 3);
v___y_825_ = v___x_883_;
v_keyTys_826_ = v_keyTys_878_;
v_arrKeyTys_827_ = v_arrKeyTys_879_;
v_arrParents_828_ = v_arrParents_880_;
v_currArrKey_829_ = v_currArrKey_881_;
v_items_830_ = v_items_882_;
goto v___jp_824_;
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_del_object(v___x_874_);
lean_dec(v_snd_872_);
lean_dec(v_fst_871_);
lean_dec(v_tailKey_867_);
lean_dec_ref_known(v___x_851_, 3);
lean_dec(v_x_819_);
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
lean_dec_ref_known(v___x_851_, 3);
lean_dec(v_x_819_);
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
v___jp_824_:
{
lean_object* v___x_831_; uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_831_ = lean_box(0);
v___x_832_ = 1;
v___x_833_ = lean_box(v___x_832_);
lean_inc_n(v___y_825_, 2);
v___x_834_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_825_, v___x_833_, v_keyTys_826_);
v___x_835_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
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
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_819_ = stack[0].m_obj;
lean_object* v_a_820_ = stack[1].m_obj;
lean_object* v_a_821_ = stack[2].m_obj;
lean_object* v_a_822_ = stack[3].m_obj;
lean_object* v_res_941_;
v_res_941_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_819_, v_a_820_, v_a_821_, v_a_822_);
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
return v_res_947_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_toCold_961_; lean_object* v_currRecDepth_962_; lean_object* v_ref_963_; uint16_t v_optionFlags_964_; uint8_t v_suppressElabErrors_965_; uint8_t v_isRecordingDeps_966_; lean_object* v___x_967_; uint8_t v___x_968_; lean_object* v_ref_969_; lean_object* v___x_970_; lean_object* v___y_972_; 
v_toCold_961_ = lean_ctor_get(v_a_958_, 0);
v_currRecDepth_962_ = lean_ctor_get(v_a_958_, 1);
v_ref_963_ = lean_ctor_get(v_a_958_, 2);
v_optionFlags_964_ = lean_ctor_get_uint16(v_a_958_, sizeof(void*)*3);
v_suppressElabErrors_965_ = lean_ctor_get_uint8(v_a_958_, sizeof(void*)*3 + 2);
v_isRecordingDeps_966_ = lean_ctor_get_uint8(v_a_958_, sizeof(void*)*3 + 3);
v___x_967_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_956_);
v___x_968_ = l_Lean_Syntax_isOfKind(v_x_956_, v___x_967_);
v_ref_969_ = l_Lean_replaceRef(v_x_956_, v_ref_963_);
lean_inc(v_currRecDepth_962_);
lean_inc_ref(v_toCold_961_);
v___x_970_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_970_, 0, v_toCold_961_);
lean_ctor_set(v___x_970_, 1, v_currRecDepth_962_);
lean_ctor_set(v___x_970_, 2, v_ref_969_);
lean_ctor_set_uint16(v___x_970_, sizeof(void*)*3, v_optionFlags_964_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*3 + 2, v_suppressElabErrors_965_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*3 + 3, v_isRecordingDeps_966_);
if (v___x_968_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_980_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_956_, v___x_979_, v_a_957_, v___x_970_, v_a_959_);
lean_dec_ref_known(v___x_970_, 3);
lean_dec_ref(v_a_957_);
lean_dec(v_x_956_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; lean_object* v___y_986_; 
v___x_981_ = lean_unsigned_to_nat(2u);
v___x_982_ = l_Lean_Syntax_getArg(v_x_956_, v___x_981_);
v___x_983_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_982_);
v___x_984_ = l_Lean_Syntax_isOfKind(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v___x_982_);
v___x_1120_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1121_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_956_, v___x_1120_, v_a_957_, v___x_970_, v_a_959_);
lean_dec_ref_known(v___x_970_, 3);
lean_dec_ref(v_a_957_);
lean_dec(v_x_956_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = l_Lean_Syntax_getArg(v___x_982_, v___x_1122_);
lean_dec(v___x_982_);
v___x_1124_ = l_Lean_Syntax_getArgs(v___x_1123_);
lean_dec(v___x_1123_);
v___x_1125_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1126_ = lean_array_get_size(v___x_1124_);
v___x_1127_ = lean_nat_dec_lt(v___x_1122_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_dec_ref(v___x_1124_);
v___y_986_ = v___x_1125_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; lean_object* v___x_1132_; lean_object* v_snd_1133_; 
v___x_1128_ = lean_box(v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___x_1125_);
v___x_1130_ = ((size_t)0ULL);
v___x_1131_ = lean_usize_of_nat(v___x_1126_);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_984_, v___x_1124_, v___x_1130_, v___x_1131_, v___x_1129_);
lean_dec_ref(v___x_1124_);
v_snd_1133_ = lean_ctor_get(v___x_1132_, 1);
lean_inc(v_snd_1133_);
lean_dec_ref(v___x_1132_);
v___y_986_ = v_snd_1133_;
goto v___jp_985_;
}
}
v___jp_985_:
{
size_t v_sz_987_; size_t v___x_988_; lean_object* v___x_989_; 
v_sz_987_ = lean_array_size(v___y_986_);
v___x_988_ = ((size_t)0ULL);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_987_, v___x_988_, v___y_986_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_991_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_956_, v___x_990_, v_a_957_, v___x_970_, v_a_959_);
lean_dec_ref_known(v___x_970_, 3);
lean_dec_ref(v_a_957_);
lean_dec(v_x_956_);
return v___x_991_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_tailKey_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_val_992_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v___x_989_, 1);
v___x_993_ = lean_box(0);
v___x_994_ = lean_array_get_size(v_val_992_);
v___x_995_ = lean_unsigned_to_nat(1u);
v___x_996_ = lean_nat_sub(v___x_994_, v___x_995_);
v_tailKey_997_ = lean_array_get(v___x_993_, v_val_992_, v___x_996_);
lean_dec(v___x_996_);
v___x_998_ = lean_array_pop(v_val_992_);
v___x_999_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_998_, v_a_957_, v___x_970_, v_a_959_);
lean_dec_ref(v___x_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1111_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v_fst_1001_ = lean_ctor_get(v_a_1000_, 0);
v_snd_1002_ = lean_ctor_get(v_a_1000_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_a_1000_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1004_ = v_a_1000_;
v_isShared_1005_ = v_isSharedCheck_1111_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_snd_1002_);
lean_inc(v_fst_1001_);
lean_dec(v_a_1000_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1111_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; 
lean_inc(v_tailKey_997_);
v___x_1006_ = l_Lake_Toml_elabSimpleKey(v_tailKey_997_, v___x_970_, v_a_959_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1102_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1102_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1102_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_keyTys_1011_; lean_object* v_arrKeyTys_1012_; lean_object* v_arrParents_1013_; lean_object* v_currArrKey_1014_; lean_object* v_items_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_keyTys_1011_ = lean_ctor_get(v_snd_1002_, 0);
v_arrKeyTys_1012_ = lean_ctor_get(v_snd_1002_, 1);
v_arrParents_1013_ = lean_ctor_get(v_snd_1002_, 2);
v_currArrKey_1014_ = lean_ctor_get(v_snd_1002_, 3);
v_items_1015_ = lean_ctor_get(v_snd_1002_, 5);
v___x_1016_ = l_Lean_Name_str___override(v_fst_1001_, v_a_1007_);
v___x_1017_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_1011_, v___x_1016_);
if (lean_obj_tag(v___x_1017_) == 1)
{
lean_object* v_val_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1069_; 
v_val_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1069_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_val_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1069_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_unbox(v_val_1018_);
if (v___x_1022_ == 2)
{
lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1047_; 
lean_inc_ref(v_items_1015_);
lean_inc(v_arrParents_1013_);
lean_inc(v_arrKeyTys_1012_);
lean_del_object(v___x_1020_);
lean_dec(v_val_1018_);
lean_dec(v_tailKey_997_);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_snd_1002_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; lean_object* v_unused_1049_; lean_object* v_unused_1050_; lean_object* v_unused_1051_; lean_object* v_unused_1052_; lean_object* v_unused_1053_; 
v_unused_1048_ = lean_ctor_get(v_snd_1002_, 5);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_snd_1002_, 4);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_snd_1002_, 3);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v_snd_1002_, 2);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v_snd_1002_, 1);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v_snd_1002_, 0);
lean_dec(v_unused_1053_);
v___x_1024_ = v_snd_1002_;
v_isShared_1025_ = v_isSharedCheck_1047_;
goto v_resetjp_1023_;
}
else
{
lean_dec(v_snd_1002_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1047_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_1013_, v___x_1016_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_del_object(v___x_1024_);
lean_dec_ref(v_items_1015_);
lean_dec(v_arrParents_1013_);
lean_dec(v_arrKeyTys_1012_);
lean_del_object(v___x_1009_);
lean_del_object(v___x_1004_);
lean_dec(v_x_956_);
v___y_972_ = v___x_1016_;
goto v___jp_971_;
}
else
{
lean_object* v_val_1027_; lean_object* v___x_1028_; 
v_val_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_val_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_1012_, v_val_1027_);
lean_dec(v_val_1027_);
if (lean_obj_tag(v___x_1028_) == 1)
{
lean_object* v_val_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
lean_dec_ref_known(v___x_970_, 3);
v_val_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_956_, 2);
v___x_1032_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_x_956_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_mk_empty_array_with_capacity(v___x_995_);
v___x_1034_ = lean_array_push(v___x_1033_, v___x_1032_);
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_x_956_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
lean_inc_n(v___x_1016_, 2);
v___x_1036_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1036_, 0, v_x_956_);
lean_ctor_set(v___x_1036_, 1, v___x_1016_);
lean_ctor_set(v___x_1036_, 2, v___x_1035_);
v___x_1037_ = lean_array_push(v_items_1015_, v___x_1036_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 5, v___x_1037_);
lean_ctor_set(v___x_1024_, 4, v___x_1016_);
lean_ctor_set(v___x_1024_, 3, v___x_1016_);
lean_ctor_set(v___x_1024_, 0, v_val_1029_);
v___x_1039_ = v___x_1024_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_val_1029_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_arrKeyTys_1012_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_arrParents_1013_);
lean_ctor_set(v_reuseFailAlloc_1046_, 3, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1046_, 4, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1046_, 5, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___x_1039_);
lean_ctor_set(v___x_1004_, 0, v___x_1030_);
v___x_1041_ = v___x_1004_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1041_);
v___x_1043_ = v___x_1009_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_dec(v___x_1028_);
lean_del_object(v___x_1024_);
lean_dec_ref(v_items_1015_);
lean_dec(v_arrParents_1013_);
lean_dec(v_arrKeyTys_1012_);
lean_del_object(v___x_1009_);
lean_del_object(v___x_1004_);
lean_dec(v_x_956_);
v___y_972_ = v___x_1016_;
goto v___jp_971_;
}
}
}
}
else
{
lean_object* v___x_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
lean_del_object(v___x_1009_);
lean_del_object(v___x_1004_);
lean_dec(v_x_956_);
v___x_1054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1055_ = lean_unbox(v_val_1018_);
lean_dec(v_val_1018_);
v___x_1056_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1055_);
v___x_1057_ = lean_string_append(v___x_1054_, v___x_1056_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1059_ = lean_string_append(v___x_1057_, v___x_1058_);
v___x_1060_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1016_, v___x_984_);
v___x_1061_ = lean_string_append(v___x_1059_, v___x_1060_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1063_ = lean_string_append(v___x_1061_, v___x_1062_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 3);
lean_ctor_set(v___x_1020_, 0, v___x_1063_);
v___x_1065_ = v___x_1020_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_Lean_MessageData_ofFormat(v___x_1065_);
v___x_1067_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_997_, v___x_1066_, v_snd_1002_, v___x_970_, v_a_959_);
lean_dec_ref_known(v___x_970_, 3);
lean_dec(v_snd_1002_);
lean_dec(v_tailKey_997_);
return v___x_1067_;
}
}
}
}
else
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1095_; 
lean_inc_ref(v_items_1015_);
lean_inc(v_currArrKey_1014_);
lean_inc(v_arrParents_1013_);
lean_inc(v_arrKeyTys_1012_);
lean_inc(v_keyTys_1011_);
lean_dec(v___x_1017_);
lean_dec(v_tailKey_997_);
lean_dec_ref_known(v___x_970_, 3);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_snd_1002_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; lean_object* v_unused_1097_; lean_object* v_unused_1098_; lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1096_ = lean_ctor_get(v_snd_1002_, 5);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_snd_1002_, 4);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_snd_1002_, 3);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_snd_1002_, 2);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_snd_1002_, 1);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_snd_1002_, 0);
lean_dec(v_unused_1101_);
v___x_1071_ = v_snd_1002_;
v_isShared_1072_ = v_isSharedCheck_1095_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v_snd_1002_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1095_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = 2;
v___x_1075_ = lean_box(v___x_1074_);
lean_inc_n(v___x_1016_, 4);
v___x_1076_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1016_, v___x_1075_, v_keyTys_1011_);
lean_inc(v___x_1076_);
lean_inc(v_currArrKey_1014_);
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_1014_, v___x_1076_, v_arrKeyTys_1012_);
v___x_1078_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1016_, v_currArrKey_1014_, v_arrParents_1013_);
v___x_1079_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_956_, 2);
v___x_1080_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_x_956_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_mk_empty_array_with_capacity(v___x_995_);
v___x_1082_ = lean_array_push(v___x_1081_, v___x_1080_);
v___x_1083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1083_, 0, v_x_956_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1084_, 0, v_x_956_);
lean_ctor_set(v___x_1084_, 1, v___x_1016_);
lean_ctor_set(v___x_1084_, 2, v___x_1083_);
v___x_1085_ = lean_array_push(v_items_1015_, v___x_1084_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 5, v___x_1085_);
lean_ctor_set(v___x_1071_, 4, v___x_1016_);
lean_ctor_set(v___x_1071_, 3, v___x_1016_);
lean_ctor_set(v___x_1071_, 2, v___x_1078_);
lean_ctor_set(v___x_1071_, 1, v___x_1077_);
lean_ctor_set(v___x_1071_, 0, v___x_1076_);
v___x_1087_ = v___x_1071_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1094_, 4, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1094_, 5, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___x_1087_);
lean_ctor_set(v___x_1004_, 0, v___x_1073_);
v___x_1089_ = v___x_1004_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1089_);
v___x_1091_ = v___x_1009_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_del_object(v___x_1004_);
lean_dec(v_snd_1002_);
lean_dec(v_fst_1001_);
lean_dec(v_tailKey_997_);
lean_dec_ref_known(v___x_970_, 3);
lean_dec(v_x_956_);
v_a_1103_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1006_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1006_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v_tailKey_997_);
lean_dec_ref_known(v___x_970_, 3);
lean_dec(v_x_956_);
v_a_1112_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_999_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_999_);
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
}
v___jp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_973_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_974_ = l_Lean_MessageData_ofName(v___y_972_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_977_, v___x_970_, v_a_959_);
lean_dec_ref_known(v___x_970_, 3);
return v___x_978_;
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_956_ = stack[0].m_obj;
lean_object* v_a_957_ = stack[1].m_obj;
lean_object* v_a_958_ = stack[2].m_obj;
lean_object* v_a_959_ = stack[3].m_obj;
lean_object* v_res_1134_;
v_res_1134_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_956_, v_a_957_, v_a_958_, v_a_959_);
stack->m_obj
 = v_res_1134_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1140_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1144_);
v___x_1150_ = l_Lean_Syntax_isOfKind(v_x_1144_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_1144_);
v___x_1152_ = l_Lean_Syntax_isOfKind(v_x_1144_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1144_);
v___x_1154_ = l_Lean_Syntax_isOfKind(v_x_1144_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1156_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1144_, v___x_1155_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec_ref(v_a_1145_);
lean_dec(v_x_1144_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1157_;
}
}
else
{
lean_object* v___x_1158_; 
v___x_1158_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1158_;
}
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1159_;
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1144_ = stack[0].m_obj;
lean_object* v_a_1145_ = stack[1].m_obj;
lean_object* v_a_1146_ = stack[2].m_obj;
lean_object* v_a_1147_ = stack[3].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1166_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1168_, lean_object* v_as_1169_, size_t v_i_1170_, size_t v_stop_1171_, lean_object* v_b_1172_){
_start:
{
lean_object* v___y_1174_; uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_eq(v_i_1170_, v_stop_1171_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1182_; 
v___x_1179_ = lean_array_uget_borrowed(v_as_1169_, v_i_1170_);
v_fst_1180_ = lean_ctor_get(v___x_1179_, 0);
v_snd_1181_ = lean_ctor_get(v___x_1179_, 1);
lean_inc(v_fst_1180_);
v___x_1182_ = l_Lean_Name_components(v_fst_1180_);
if (lean_obj_tag(v___x_1182_) == 0)
{
v___y_1174_ = v_b_1172_;
goto v___jp_1173_;
}
else
{
lean_object* v_head_1183_; lean_object* v_tail_1184_; lean_object* v___x_1185_; 
v_head_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_head_1183_);
v_tail_1184_ = lean_ctor_get(v___x_1182_, 1);
lean_inc(v_tail_1184_);
lean_dec_ref_known(v___x_1182_, 2);
lean_inc(v_snd_1181_);
lean_inc(v_ref_1168_);
v___x_1185_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1172_, v_ref_1168_, v_head_1183_, v_tail_1184_, v_snd_1181_);
v___y_1174_ = v___x_1185_;
goto v___jp_1173_;
}
}
else
{
lean_dec(v_ref_1168_);
return v_b_1172_;
}
v___jp_1173_:
{
size_t v___x_1175_; size_t v___x_1176_; 
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_add(v_i_1170_, v___x_1175_);
v_i_1170_ = v___x_1176_;
v_b_1172_ = v___y_1174_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1168_ = stack[0].m_obj;
lean_object* v_as_1169_ = stack[1].m_obj;
size_t v_i_1170_ = stack[2].m_num;
size_t v_stop_1171_ = stack[3].m_num;
lean_object* v_b_1172_ = stack[4].m_obj;
lean_object* v_res_1186_;
v_res_1186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1168_, v_as_1169_, v_i_1170_, v_stop_1171_, v_b_1172_);
stack->m_obj
 = v_res_1186_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1187_, size_t v_i_1188_, lean_object* v_bs_1189_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_usize_dec_lt(v_i_1188_, v_sz_1187_);
if (v___x_1190_ == 0)
{
return v_bs_1189_;
}
else
{
lean_object* v_v_1191_; lean_object* v___x_1192_; lean_object* v_bs_x27_1193_; lean_object* v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v_v_1191_ = lean_array_uget(v_bs_1189_, v_i_1188_);
v___x_1192_ = lean_unsigned_to_nat(0u);
v_bs_x27_1193_ = lean_array_uset(v_bs_1189_, v_i_1188_, v___x_1192_);
v___x_1194_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1191_);
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_add(v_i_1188_, v___x_1195_);
v___x_1197_ = lean_array_uset(v_bs_x27_1193_, v_i_1188_, v___x_1194_);
v_i_1188_ = v___x_1196_;
v_bs_1189_ = v___x_1197_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1187_ = stack[0].m_num;
size_t v_i_1188_ = stack[1].m_num;
lean_object* v_bs_1189_ = stack[2].m_obj;
lean_object* v_res_1199_;
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1187_, v_i_1188_, v_bs_1189_);
stack->m_obj
 = v_res_1199_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1200_){
_start:
{
switch(lean_obj_tag(v_a_1200_))
{
case 6:
{
lean_object* v_xs_1201_; lean_object* v_ref_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1230_; 
v_xs_1201_ = lean_ctor_get(v_a_1200_, 1);
v_ref_1202_ = lean_ctor_get(v_a_1200_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_a_1200_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1204_ = v_a_1200_;
v_isShared_1205_ = v_isSharedCheck_1230_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_xs_1201_);
lean_inc(v_ref_1202_);
lean_dec(v_a_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1230_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_items_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_items_1206_ = lean_ctor_get(v_xs_1201_, 0);
lean_inc_ref(v_items_1206_);
lean_dec_ref(v_xs_1201_);
v___x_1207_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_array_get_size(v_items_1206_);
v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1212_; 
lean_dec_ref(v_items_1206_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1207_);
v___x_1212_ = v___x_1204_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_ref_1202_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
else
{
uint8_t v___x_1214_; 
v___x_1214_ = lean_nat_dec_le(v___x_1209_, v___x_1209_);
if (v___x_1214_ == 0)
{
if (v___x_1210_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v_items_1206_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1207_);
v___x_1216_ = v___x_1204_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_ref_1202_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1207_);
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
size_t v___x_1218_; size_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1218_ = ((size_t)0ULL);
v___x_1219_ = lean_usize_of_nat(v___x_1209_);
lean_inc(v_ref_1202_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1202_, v_items_1206_, v___x_1218_, v___x_1219_, v___x_1207_);
lean_dec_ref(v_items_1206_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1220_);
v___x_1222_ = v___x_1204_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_ref_1202_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
size_t v___x_1224_; size_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1224_ = ((size_t)0ULL);
v___x_1225_ = lean_usize_of_nat(v___x_1209_);
lean_inc(v_ref_1202_);
v___x_1226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1202_, v_items_1206_, v___x_1224_, v___x_1225_, v___x_1207_);
lean_dec_ref(v_items_1206_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1226_);
v___x_1228_ = v___x_1204_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_ref_1202_);
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
}
}
case 5:
{
lean_object* v_ref_1231_; lean_object* v_xs_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1242_; 
v_ref_1231_ = lean_ctor_get(v_a_1200_, 0);
v_xs_1232_ = lean_ctor_get(v_a_1200_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_a_1200_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1234_ = v_a_1200_;
v_isShared_1235_ = v_isSharedCheck_1242_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_xs_1232_);
lean_inc(v_ref_1231_);
lean_dec(v_a_1200_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1242_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
size_t v_sz_1236_; size_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v_sz_1236_ = lean_array_size(v_xs_1232_);
v___x_1237_ = ((size_t)0ULL);
v___x_1238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1236_, v___x_1237_, v_xs_1232_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v___x_1238_);
v___x_1240_ = v___x_1234_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_ref_1231_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
default: 
{
return v_a_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1243_, lean_object* v___x_1244_, lean_object* v_v_x3f_1245_){
_start:
{
if (lean_obj_tag(v_v_x3f_1245_) == 1)
{
lean_object* v_val_1246_; 
v_val_1246_ = lean_ctor_get(v_v_x3f_1245_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v_v_x3f_1245_, 1);
switch(lean_obj_tag(v_val_1246_))
{
case 6:
{
lean_object* v_ref_1247_; lean_object* v_xs_1248_; lean_object* v___x_1249_; 
v_ref_1247_ = lean_ctor_get(v_val_1246_, 0);
lean_inc(v_ref_1247_);
v_xs_1248_ = lean_ctor_get(v_val_1246_, 1);
lean_inc_ref(v_xs_1248_);
lean_dec_ref_known(v_val_1246_, 2);
v___x_1249_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1243_);
if (lean_obj_tag(v___x_1249_) == 6)
{
lean_object* v_xs_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1259_; 
v_xs_1250_ = lean_ctor_get(v___x_1249_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1249_, 0);
lean_dec(v_unused_1260_);
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_xs_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_items_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v_items_1254_ = lean_ctor_get(v_xs_1250_, 0);
lean_inc_ref(v_items_1254_);
lean_dec_ref(v_xs_1250_);
v___x_1255_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1244_, v_xs_1248_, v_items_1254_);
lean_dec_ref(v_items_1254_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v___x_1255_);
lean_ctor_set(v___x_1252_, 0, v_ref_1247_);
v___x_1257_ = v___x_1252_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_ref_1247_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
else
{
lean_dec_ref(v_xs_1248_);
lean_dec(v_ref_1247_);
lean_dec_ref(v___x_1244_);
return v___x_1249_;
}
}
case 5:
{
lean_object* v_ref_1261_; lean_object* v_xs_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v___x_1244_);
v_ref_1261_ = lean_ctor_get(v_val_1246_, 0);
v_xs_1262_ = lean_ctor_get(v_val_1246_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_val_1246_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1264_ = v_val_1246_;
v_isShared_1265_ = v_isSharedCheck_1281_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_xs_1262_);
lean_inc(v_ref_1261_);
lean_dec(v_val_1246_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1281_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; 
v___x_1266_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1243_);
if (lean_obj_tag(v___x_1266_) == 5)
{
lean_object* v_xs_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1275_; 
lean_del_object(v___x_1264_);
v_xs_1267_ = lean_ctor_get(v___x_1266_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1266_, 0);
lean_dec(v_unused_1276_);
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_xs_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = l_Array_append___redArg(v_xs_1262_, v_xs_1267_);
lean_dec_ref(v_xs_1267_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v___x_1271_);
lean_ctor_set(v___x_1269_, 0, v_ref_1261_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_ref_1261_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_array_push(v_xs_1262_, v___x_1266_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v___x_1277_);
v___x_1279_ = v___x_1264_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_ref_1261_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
default: 
{
lean_object* v___x_1282_; 
lean_dec(v_val_1246_);
lean_dec_ref(v___x_1244_);
v___x_1282_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1243_);
return v___x_1282_;
}
}
}
else
{
lean_object* v___x_1283_; 
lean_dec(v_v_x3f_1245_);
lean_dec_ref(v___x_1244_);
v___x_1283_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1243_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1284_, lean_object* v_k_1285_, lean_object* v_t_1286_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1286_);
lean_inc(v_k_1285_);
v___x_1288_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1287_, v_k_1285_, v_t_1286_);
if (lean_obj_tag(v___x_1288_) == 1)
{
lean_object* v_val_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_k_1285_);
v_val_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1324_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_val_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1324_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_items_1293_; lean_object* v_indices_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1323_; 
v_items_1293_ = lean_ctor_get(v_t_1286_, 0);
v_indices_1294_ = lean_ctor_get(v_t_1286_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_t_1286_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1296_ = v_t_1286_;
v_isShared_1297_ = v_isSharedCheck_1323_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_indices_1294_);
lean_inc(v_items_1293_);
lean_dec(v_t_1286_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1323_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = lean_array_get_size(v_items_1293_);
v___x_1299_ = lean_nat_dec_lt(v_val_1289_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1301_; 
lean_del_object(v___x_1291_);
lean_dec(v_val_1289_);
lean_dec_ref(v_newV_1284_);
if (v_isShared_1297_ == 0)
{
v___x_1301_ = v___x_1296_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_items_1293_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_indices_1294_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
else
{
lean_object* v_v_1303_; lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1322_; 
v_v_1303_ = lean_array_fget(v_items_1293_, v_val_1289_);
v_fst_1304_ = lean_ctor_get(v_v_1303_, 0);
v_snd_1305_ = lean_ctor_get(v_v_1303_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_v_1303_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1307_ = v_v_1303_;
v_isShared_1308_ = v_isSharedCheck_1322_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_snd_1305_);
lean_inc(v_fst_1304_);
lean_dec(v_v_1303_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1322_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v_xs_x27_1310_; lean_object* v___x_1312_; 
v___x_1309_ = lean_box(0);
v_xs_x27_1310_ = lean_array_fset(v_items_1293_, v_val_1289_, v___x_1309_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v_snd_1305_);
v___x_1312_ = v___x_1291_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_snd_1305_);
v___x_1312_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1284_, v___x_1287_, v___x_1312_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1313_);
v___x_1315_ = v___x_1307_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_fst_1304_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_array_fset(v_xs_x27_1310_, v_val_1289_, v___x_1315_);
lean_dec(v_val_1289_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1316_);
v___x_1318_ = v___x_1296_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_indices_1294_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
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
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec(v___x_1288_);
v___x_1325_ = lean_box(0);
v___x_1326_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1284_, v___x_1287_, v___x_1325_);
v___x_1327_ = l_Lake_Toml_RBDict_push___redArg(v___x_1287_, v_k_1285_, v___x_1326_, v_t_1286_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1328_, lean_object* v_head_1329_, lean_object* v_tail_1330_, lean_object* v_newV_1331_, lean_object* v_v_x3f_1332_){
_start:
{
if (lean_obj_tag(v_v_x3f_1332_) == 1)
{
lean_object* v_val_1333_; 
v_val_1333_ = lean_ctor_get(v_v_x3f_1332_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_v_x3f_1332_, 1);
switch(lean_obj_tag(v_val_1333_))
{
case 5:
{
lean_object* v_ref_1334_; lean_object* v_xs_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_ref_1334_ = lean_ctor_get(v_val_1333_, 0);
v_xs_1335_ = lean_ctor_get(v_val_1333_, 1);
v___x_1336_ = lean_array_get_size(v_xs_1335_);
v___x_1337_ = lean_unsigned_to_nat(1u);
v___x_1338_ = lean_nat_sub(v___x_1336_, v___x_1337_);
v___x_1339_ = lean_nat_dec_lt(v___x_1338_, v___x_1336_);
if (v___x_1339_ == 0)
{
lean_dec(v___x_1338_);
lean_dec_ref(v_newV_1331_);
lean_dec(v_tail_1330_);
lean_dec(v_head_1329_);
lean_dec(v_kRef_1328_);
return v_val_1333_;
}
else
{
lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1364_; 
lean_inc_ref(v_xs_1335_);
lean_inc(v_ref_1334_);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_val_1333_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; lean_object* v_unused_1366_; 
v_unused_1365_ = lean_ctor_get(v_val_1333_, 1);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_val_1333_, 0);
lean_dec(v_unused_1366_);
v___x_1341_ = v_val_1333_;
v_isShared_1342_ = v_isSharedCheck_1364_;
goto v_resetjp_1340_;
}
else
{
lean_dec(v_val_1333_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1364_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_v_1343_; lean_object* v___x_1344_; lean_object* v_xs_x27_1345_; lean_object* v___y_1347_; 
v_v_1343_ = lean_array_fget(v_xs_1335_, v___x_1338_);
v___x_1344_ = lean_box(0);
v_xs_x27_1345_ = lean_array_fset(v_xs_1335_, v___x_1338_, v___x_1344_);
if (lean_obj_tag(v_v_1343_) == 6)
{
lean_object* v_ref_1352_; lean_object* v_xs_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_ref_1352_ = lean_ctor_get(v_v_1343_, 0);
v_xs_1353_ = lean_ctor_get(v_v_1343_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_v_1343_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v_v_1343_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_xs_1353_);
lean_inc(v_ref_1352_);
lean_dec(v_v_1343_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1353_, v_kRef_1328_, v_head_1329_, v_tail_1330_, v_newV_1331_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_ref_1352_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
v___y_1347_ = v___x_1359_;
goto v___jp_1346_;
}
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec(v_v_1343_);
lean_dec_ref(v_newV_1331_);
lean_dec(v_tail_1330_);
lean_dec(v_head_1329_);
v___x_1362_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1363_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_kRef_1328_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___y_1347_ = v___x_1363_;
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_array_fset(v_xs_x27_1345_, v___x_1338_, v___y_1347_);
lean_dec(v___x_1338_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1348_);
v___x_1350_ = v___x_1341_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_ref_1334_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1367_; lean_object* v_xs_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_ref_1367_ = lean_ctor_get(v_val_1333_, 0);
v_xs_1368_ = lean_ctor_get(v_val_1333_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_val_1333_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v_val_1333_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_xs_1368_);
lean_inc(v_ref_1367_);
lean_dec(v_val_1333_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1368_, v_kRef_1328_, v_head_1329_, v_tail_1330_, v_newV_1331_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_ref_1367_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
default: 
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec(v_val_1333_);
v___x_1377_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1328_);
v___x_1378_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1377_, v_kRef_1328_, v_head_1329_, v_tail_1330_, v_newV_1331_);
v___x_1379_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_kRef_1328_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
return v___x_1379_;
}
}
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec(v_v_x3f_1332_);
v___x_1380_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1328_);
v___x_1381_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1380_, v_kRef_1328_, v_head_1329_, v_tail_1330_, v_newV_1331_);
v___x_1382_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_kRef_1328_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1383_, lean_object* v_head_1384_, lean_object* v_tail_1385_, lean_object* v_newV_1386_, lean_object* v_k_1387_, lean_object* v_t_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1388_);
lean_inc(v_k_1387_);
v___x_1390_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1389_, v_k_1387_, v_t_1388_);
if (lean_obj_tag(v___x_1390_) == 1)
{
lean_object* v_val_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v_k_1387_);
v_val_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1426_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_val_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1426_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_items_1395_; lean_object* v_indices_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1425_; 
v_items_1395_ = lean_ctor_get(v_t_1388_, 0);
v_indices_1396_ = lean_ctor_get(v_t_1388_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_t_1388_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1398_ = v_t_1388_;
v_isShared_1399_ = v_isSharedCheck_1425_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_indices_1396_);
lean_inc(v_items_1395_);
lean_dec(v_t_1388_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1425_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = lean_array_get_size(v_items_1395_);
v___x_1401_ = lean_nat_dec_lt(v_val_1391_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1403_; 
lean_del_object(v___x_1393_);
lean_dec(v_val_1391_);
lean_dec_ref(v_newV_1386_);
lean_dec(v_tail_1385_);
lean_dec(v_head_1384_);
lean_dec(v_kRef_1383_);
if (v_isShared_1399_ == 0)
{
v___x_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_items_1395_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_indices_1396_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
else
{
lean_object* v_v_1405_; lean_object* v_fst_1406_; lean_object* v_snd_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1424_; 
v_v_1405_ = lean_array_fget(v_items_1395_, v_val_1391_);
v_fst_1406_ = lean_ctor_get(v_v_1405_, 0);
v_snd_1407_ = lean_ctor_get(v_v_1405_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_v_1405_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1409_ = v_v_1405_;
v_isShared_1410_ = v_isSharedCheck_1424_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_snd_1407_);
lean_inc(v_fst_1406_);
lean_dec(v_v_1405_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1424_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v_xs_x27_1412_; lean_object* v___x_1414_; 
v___x_1411_ = lean_box(0);
v_xs_x27_1412_ = lean_array_fset(v_items_1395_, v_val_1391_, v___x_1411_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v_snd_1407_);
v___x_1414_ = v___x_1393_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_snd_1407_);
v___x_1414_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1383_, v_head_1384_, v_tail_1385_, v_newV_1386_, v___x_1414_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v___x_1415_);
v___x_1417_ = v___x_1409_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_fst_1406_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_array_fset(v_xs_x27_1412_, v_val_1391_, v___x_1417_);
lean_dec(v_val_1391_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1418_);
v___x_1420_ = v___x_1398_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_indices_1396_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
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
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec(v___x_1390_);
v___x_1427_ = lean_box(0);
v___x_1428_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1383_, v_head_1384_, v_tail_1385_, v_newV_1386_, v___x_1427_);
v___x_1429_ = l_Lake_Toml_RBDict_push___redArg(v___x_1389_, v_k_1387_, v___x_1428_, v_t_1388_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1430_, lean_object* v_kRef_1431_, lean_object* v_k_1432_, lean_object* v_ks_1433_, lean_object* v_newV_1434_){
_start:
{
if (lean_obj_tag(v_ks_1433_) == 0)
{
lean_object* v___x_1435_; 
lean_dec(v_kRef_1431_);
v___x_1435_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1434_, v_k_1432_, v_t_1430_);
return v___x_1435_;
}
else
{
lean_object* v_head_1436_; lean_object* v_tail_1437_; lean_object* v___x_1438_; 
v_head_1436_ = lean_ctor_get(v_ks_1433_, 0);
lean_inc(v_head_1436_);
v_tail_1437_ = lean_ctor_get(v_ks_1433_, 1);
lean_inc(v_tail_1437_);
lean_dec_ref_known(v_ks_1433_, 2);
v___x_1438_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1431_, v_head_1436_, v_tail_1437_, v_newV_1434_, v_k_1432_, v_t_1430_);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1439_, lean_object* v_i_1440_, lean_object* v_bs_1441_){
_start:
{
size_t v_sz_boxed_1442_; size_t v_i_boxed_1443_; lean_object* v_res_1444_; 
v_sz_boxed_1442_ = lean_unbox_usize(v_sz_1439_);
lean_dec(v_sz_1439_);
v_i_boxed_1443_ = lean_unbox_usize(v_i_1440_);
lean_dec(v_i_1440_);
v_res_1444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1442_, v_i_boxed_1443_, v_bs_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1445_, lean_object* v_as_1446_, lean_object* v_i_1447_, lean_object* v_stop_1448_, lean_object* v_b_1449_){
_start:
{
size_t v_i_boxed_1450_; size_t v_stop_boxed_1451_; lean_object* v_res_1452_; 
v_i_boxed_1450_ = lean_unbox_usize(v_i_1447_);
lean_dec(v_i_1447_);
v_stop_boxed_1451_ = lean_unbox_usize(v_stop_1448_);
lean_dec(v_stop_1448_);
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1445_, v_as_1446_, v_i_boxed_1450_, v_stop_boxed_1451_, v_b_1449_);
lean_dec_ref(v_as_1446_);
return v_res_1452_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1453_, size_t v_i_1454_, size_t v_stop_1455_, lean_object* v_b_1456_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1453_ = stack[0].m_obj;
size_t v_i_1454_ = stack[1].m_num;
size_t v_stop_1455_ = stack[2].m_num;
lean_object* v_b_1456_ = stack[3].m_obj;
lean_object* v_res_1471_;
v_res_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1453_, v_i_1454_, v_stop_1455_, v_b_1456_);
stack->m_obj
 = v_res_1471_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1472_, lean_object* v_i_1473_, lean_object* v_stop_1474_, lean_object* v_b_1475_){
_start:
{
size_t v_i_boxed_1476_; size_t v_stop_boxed_1477_; lean_object* v_res_1478_; 
v_i_boxed_1476_ = lean_unbox_usize(v_i_1473_);
lean_dec(v_i_1473_);
v_stop_boxed_1477_ = lean_unbox_usize(v_stop_1474_);
lean_dec(v_stop_1474_);
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1472_, v_i_boxed_1476_, v_stop_boxed_1477_, v_b_1475_);
lean_dec_ref(v_as_1472_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1479_){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1480_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_array_get_size(v_items_1479_);
v___x_1483_ = lean_nat_dec_lt(v___x_1481_, v___x_1482_);
if (v___x_1483_ == 0)
{
return v___x_1480_;
}
else
{
uint8_t v___x_1484_; 
v___x_1484_ = lean_nat_dec_le(v___x_1482_, v___x_1482_);
if (v___x_1484_ == 0)
{
if (v___x_1483_ == 0)
{
return v___x_1480_;
}
else
{
size_t v___x_1485_; size_t v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((size_t)0ULL);
v___x_1486_ = lean_usize_of_nat(v___x_1482_);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1479_, v___x_1485_, v___x_1486_, v___x_1480_);
return v___x_1487_;
}
}
else
{
size_t v___x_1488_; size_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = lean_usize_of_nat(v___x_1482_);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1479_, v___x_1488_, v___x_1489_, v___x_1480_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1491_);
lean_dec_ref(v_items_1491_);
return v_res_1492_;
}
}
lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1495_);
lean_inc_ref(v_a_1494_);
v___x_1498_ = lean_apply_4(v_x_1493_, v___x_1497_, v_a_1494_, v_a_1495_, lean_box(0));
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1509_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_snd_1503_; lean_object* v_items_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v_snd_1503_ = lean_ctor_get(v_a_1499_, 1);
lean_inc(v_snd_1503_);
lean_dec(v_a_1499_);
v_items_1504_ = lean_ctor_get(v_snd_1503_, 5);
lean_inc_ref(v_items_1504_);
lean_dec(v_snd_1503_);
v___x_1505_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1504_);
lean_dec_ref(v_items_1504_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1505_);
v___x_1507_ = v___x_1501_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_a_1510_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1498_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1498_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1493_ = stack[0].m_obj;
lean_object* v_a_1494_ = stack[1].m_obj;
lean_object* v_a_1495_ = stack[2].m_obj;
lean_object* v_res_1518_;
v_res_1518_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1493_, v_a_1494_, v_a_1495_);
stack->m_obj
 = v_res_1518_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1519_, v_a_1520_, v_a_1521_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
return v_res_1523_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1532_, uint8_t v___y_1533_, lean_object* v_x_1534_){
_start:
{
if (lean_obj_tag(v_x_1534_) == 1)
{
lean_object* v_pre_1535_; 
v_pre_1535_ = lean_ctor_get(v_x_1534_, 0);
switch(lean_obj_tag(v_pre_1535_))
{
case 1:
{
lean_object* v_pre_1536_; 
v_pre_1536_ = lean_ctor_get(v_pre_1535_, 0);
switch(lean_obj_tag(v_pre_1536_))
{
case 0:
{
lean_object* v_str_1537_; lean_object* v_str_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_str_1537_ = lean_ctor_get(v_x_1534_, 1);
v_str_1538_ = lean_ctor_get(v_pre_1535_, 1);
v___x_1539_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1540_ = lean_string_dec_eq(v_str_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1542_ = lean_string_dec_eq(v_str_1538_, v___x_1541_);
if (v___x_1542_ == 0)
{
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1544_ = lean_string_dec_eq(v_str_1537_, v___x_1543_);
if (v___x_1544_ == 0)
{
return v___x_1544_;
}
else
{
return v_suppressElabErrors_1532_;
}
}
}
else
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1546_ = lean_string_dec_eq(v_str_1537_, v___x_1545_);
if (v___x_1546_ == 0)
{
return v___x_1546_;
}
else
{
return v_suppressElabErrors_1532_;
}
}
}
case 1:
{
lean_object* v_pre_1547_; 
v_pre_1547_ = lean_ctor_get(v_pre_1536_, 0);
if (lean_obj_tag(v_pre_1547_) == 0)
{
lean_object* v_str_1548_; lean_object* v_str_1549_; lean_object* v_str_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_str_1548_ = lean_ctor_get(v_x_1534_, 1);
v_str_1549_ = lean_ctor_get(v_pre_1535_, 1);
v_str_1550_ = lean_ctor_get(v_pre_1536_, 1);
v___x_1551_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1552_ = lean_string_dec_eq(v_str_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1554_ = lean_string_dec_eq(v_str_1549_, v___x_1553_);
if (v___x_1554_ == 0)
{
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1556_ = lean_string_dec_eq(v_str_1548_, v___x_1555_);
if (v___x_1556_ == 0)
{
return v___x_1556_;
}
else
{
return v_suppressElabErrors_1532_;
}
}
}
}
else
{
return v___y_1533_;
}
}
default: 
{
return v___y_1533_;
}
}
}
case 0:
{
lean_object* v_str_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_str_1557_ = lean_ctor_get(v_x_1534_, 1);
v___x_1558_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1559_ = lean_string_dec_eq(v_str_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
return v___x_1559_;
}
else
{
return v_suppressElabErrors_1532_;
}
}
default: 
{
return v___y_1533_;
}
}
}
else
{
return v___y_1533_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_1532_ = stack[0].m_num;
uint8_t v___y_1533_ = stack[1].m_num;
lean_object* v_x_1534_ = stack[2].m_obj;
uint8_t v_res_1560_;
v_res_1560_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_1532_, v___y_1533_, v_x_1534_);
stack->m_num = v_res_1560_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1561_, lean_object* v___y_1562_, lean_object* v_x_1563_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1564_; uint8_t v___y_10676__boxed_1565_; uint8_t v_res_1566_; lean_object* v_r_1567_; 
v_suppressElabErrors_boxed_1564_ = lean_unbox(v_suppressElabErrors_1561_);
v___y_10676__boxed_1565_ = lean_unbox(v___y_1562_);
v_res_1566_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1564_, v___y_10676__boxed_1565_, v_x_1563_);
lean_dec(v_x_1563_);
v_r_1567_ = lean_box(v_res_1566_);
return v_r_1567_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1568_, lean_object* v_opt_1569_){
_start:
{
lean_object* v_name_1570_; lean_object* v_defValue_1571_; lean_object* v_map_1572_; lean_object* v___x_1573_; 
v_name_1570_ = lean_ctor_get(v_opt_1569_, 0);
v_defValue_1571_ = lean_ctor_get(v_opt_1569_, 1);
v_map_1572_ = lean_ctor_get(v_opts_1568_, 0);
v___x_1573_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1572_, v_name_1570_);
if (lean_obj_tag(v___x_1573_) == 0)
{
uint8_t v___x_1574_; 
v___x_1574_ = lean_unbox(v_defValue_1571_);
return v___x_1574_;
}
else
{
lean_object* v_val_1575_; 
v_val_1575_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_val_1575_);
lean_dec_ref_known(v___x_1573_, 1);
if (lean_obj_tag(v_val_1575_) == 1)
{
uint8_t v_v_1576_; 
v_v_1576_ = lean_ctor_get_uint8(v_val_1575_, 0);
lean_dec_ref_known(v_val_1575_, 0);
return v_v_1576_;
}
else
{
uint8_t v___x_1577_; 
lean_dec(v_val_1575_);
v___x_1577_ = lean_unbox(v_defValue_1571_);
return v___x_1577_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1568_ = stack[0].m_obj;
lean_object* v_opt_1569_ = stack[1].m_obj;
uint8_t v_res_1578_;
v_res_1578_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1568_, v_opt_1569_);
stack->m_num = v_res_1578_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1579_, lean_object* v_opt_1580_){
_start:
{
uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_res_1581_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1579_, v_opt_1580_);
lean_dec_ref(v_opt_1580_);
lean_dec_ref(v_opts_1579_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1584_, lean_object* v_msgData_1585_, uint8_t v_severity_1586_, uint8_t v_isSilent_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_a_1593_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; uint8_t v___y_1601_; uint8_t v___y_1602_; lean_object* v___y_1603_; lean_object* v_toCold_1604_; lean_object* v___y_1605_; lean_object* v___y_1633_; lean_object* v___y_1634_; uint8_t v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; uint8_t v___y_1638_; uint8_t v___y_1639_; lean_object* v___y_1640_; uint8_t v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; uint8_t v___y_1663_; uint8_t v___y_1664_; lean_object* v___y_1665_; uint8_t v___y_1669_; uint8_t v___y_1670_; uint8_t v___y_1671_; uint8_t v___x_1682_; uint8_t v___y_1684_; uint8_t v___y_1685_; uint8_t v___y_1686_; uint8_t v___y_1688_; uint8_t v___x_1697_; 
v___x_1682_ = 2;
v___x_1697_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1586_, v___x_1682_);
if (v___x_1697_ == 0)
{
v___y_1688_ = v___x_1697_;
goto v___jp_1687_;
}
else
{
uint8_t v___x_1698_; 
lean_inc_ref(v_msgData_1585_);
v___x_1698_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1585_);
v___y_1688_ = v___x_1698_;
goto v___jp_1687_;
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v_a_1593_);
lean_ctor_set(v___x_1594_, 1, v___y_1588_);
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
return v___x_1595_;
}
v___jp_1596_:
{
lean_object* v_currNamespace_1606_; lean_object* v_openDecls_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v_env_1612_; lean_object* v_nextMacroScope_1613_; lean_object* v_ngen_1614_; lean_object* v_auxDeclNGen_1615_; lean_object* v_traceState_1616_; lean_object* v_cache_1617_; lean_object* v_recordedDeps_1618_; lean_object* v_messages_1619_; lean_object* v_infoState_1620_; lean_object* v_snapshotTasks_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1631_; 
v_currNamespace_1606_ = lean_ctor_get(v_toCold_1604_, 4);
v_openDecls_1607_ = lean_ctor_get(v_toCold_1604_, 5);
lean_inc(v_openDecls_1607_);
lean_inc(v_currNamespace_1606_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v_currNamespace_1606_);
lean_ctor_set(v___x_1608_, 1, v_openDecls_1607_);
v___x_1609_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___y_1597_);
lean_inc_ref(v___y_1599_);
lean_inc_ref(v___y_1600_);
v___x_1610_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1610_, 0, v___y_1600_);
lean_ctor_set(v___x_1610_, 1, v___y_1598_);
lean_ctor_set(v___x_1610_, 2, v___y_1603_);
lean_ctor_set(v___x_1610_, 3, v___y_1599_);
lean_ctor_set(v___x_1610_, 4, v___x_1609_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*5, v___y_1601_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*5 + 1, v___y_1602_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*5 + 2, v_isSilent_1587_);
v___x_1611_ = lean_st_ref_take(v___y_1605_);
v_env_1612_ = lean_ctor_get(v___x_1611_, 0);
v_nextMacroScope_1613_ = lean_ctor_get(v___x_1611_, 1);
v_ngen_1614_ = lean_ctor_get(v___x_1611_, 2);
v_auxDeclNGen_1615_ = lean_ctor_get(v___x_1611_, 3);
v_traceState_1616_ = lean_ctor_get(v___x_1611_, 4);
v_cache_1617_ = lean_ctor_get(v___x_1611_, 5);
v_recordedDeps_1618_ = lean_ctor_get(v___x_1611_, 6);
v_messages_1619_ = lean_ctor_get(v___x_1611_, 7);
v_infoState_1620_ = lean_ctor_get(v___x_1611_, 8);
v_snapshotTasks_1621_ = lean_ctor_get(v___x_1611_, 9);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1623_ = v___x_1611_;
v_isShared_1624_ = v_isSharedCheck_1631_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_snapshotTasks_1621_);
lean_inc(v_infoState_1620_);
lean_inc(v_messages_1619_);
lean_inc(v_recordedDeps_1618_);
lean_inc(v_cache_1617_);
lean_inc(v_traceState_1616_);
lean_inc(v_auxDeclNGen_1615_);
lean_inc(v_ngen_1614_);
lean_inc(v_nextMacroScope_1613_);
lean_inc(v_env_1612_);
lean_dec(v___x_1611_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1631_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1625_ = lean_box(0);
v___x_1626_ = l_Lean_MessageLog_add(v___x_1610_, v_messages_1619_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 7, v___x_1626_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_env_1612_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_nextMacroScope_1613_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_ngen_1614_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_auxDeclNGen_1615_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_traceState_1616_);
lean_ctor_set(v_reuseFailAlloc_1630_, 5, v_cache_1617_);
lean_ctor_set(v_reuseFailAlloc_1630_, 6, v_recordedDeps_1618_);
lean_ctor_set(v_reuseFailAlloc_1630_, 7, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1630_, 8, v_infoState_1620_);
lean_ctor_set(v_reuseFailAlloc_1630_, 9, v_snapshotTasks_1621_);
v___x_1628_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_st_ref_put(v___y_1605_, v___x_1628_);
v_a_1593_ = v___x_1625_;
goto v___jp_1592_;
}
}
}
v___jp_1632_:
{
lean_object* v_fileName_1641_; lean_object* v_fileMap_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1657_; 
v_fileName_1641_ = lean_ctor_get(v___y_1636_, 0);
v_fileMap_1642_ = lean_ctor_get(v___y_1636_, 1);
v___x_1643_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1585_);
v___x_1644_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1643_, v___y_1589_, v___y_1590_);
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1657_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1657_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
lean_inc_ref_n(v_fileMap_1642_, 2);
v___x_1649_ = l_Lean_FileMap_toPosition(v_fileMap_1642_, v___y_1637_);
lean_dec(v___y_1637_);
v___x_1650_ = l_Lean_FileMap_toPosition(v_fileMap_1642_, v___y_1640_);
lean_dec(v___y_1640_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
lean_ctor_set(v___x_1647_, 0, v___x_1650_);
v___x_1652_ = v___x_1647_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; 
v___x_1653_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1635_ == 0)
{
lean_dec_ref(v___y_1633_);
v___y_1597_ = v_a_1645_;
v___y_1598_ = v___x_1649_;
v___y_1599_ = v___x_1653_;
v___y_1600_ = v_fileName_1641_;
v___y_1601_ = v___y_1638_;
v___y_1602_ = v___y_1639_;
v___y_1603_ = v___x_1652_;
v_toCold_1604_ = v___y_1634_;
v___y_1605_ = v___y_1590_;
goto v___jp_1596_;
}
else
{
uint8_t v___x_1654_; 
lean_inc(v_a_1645_);
v___x_1654_ = l_Lean_MessageData_hasTag(v___y_1633_, v_a_1645_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_dec_ref(v___x_1652_);
lean_dec_ref(v___x_1649_);
lean_dec(v_a_1645_);
v___x_1655_ = lean_box(0);
v_a_1593_ = v___x_1655_;
goto v___jp_1592_;
}
else
{
v___y_1597_ = v_a_1645_;
v___y_1598_ = v___x_1649_;
v___y_1599_ = v___x_1653_;
v___y_1600_ = v_fileName_1641_;
v___y_1601_ = v___y_1638_;
v___y_1602_ = v___y_1639_;
v___y_1603_ = v___x_1652_;
v_toCold_1604_ = v___y_1634_;
v___y_1605_ = v___y_1590_;
goto v___jp_1596_;
}
}
}
}
}
v___jp_1658_:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Syntax_getTailPos_x3f(v___y_1662_, v___y_1663_);
lean_dec(v___y_1662_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_inc(v___y_1665_);
v___y_1633_ = v___y_1660_;
v___y_1634_ = v___y_1661_;
v___y_1635_ = v___y_1659_;
v___y_1636_ = v___y_1661_;
v___y_1637_ = v___y_1665_;
v___y_1638_ = v___y_1663_;
v___y_1639_ = v___y_1664_;
v___y_1640_ = v___y_1665_;
goto v___jp_1632_;
}
else
{
lean_object* v_val_1667_; 
v_val_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_val_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___y_1633_ = v___y_1660_;
v___y_1634_ = v___y_1661_;
v___y_1635_ = v___y_1659_;
v___y_1636_ = v___y_1661_;
v___y_1637_ = v___y_1665_;
v___y_1638_ = v___y_1663_;
v___y_1639_ = v___y_1664_;
v___y_1640_ = v_val_1667_;
goto v___jp_1632_;
}
}
v___jp_1668_:
{
lean_object* v_toCold_1672_; lean_object* v_ref_1673_; uint8_t v_suppressElabErrors_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___f_1677_; lean_object* v_ref_1678_; lean_object* v___x_1679_; 
v_toCold_1672_ = lean_ctor_get(v___y_1589_, 0);
v_ref_1673_ = lean_ctor_get(v___y_1589_, 2);
v_suppressElabErrors_1674_ = lean_ctor_get_uint8(v___y_1589_, sizeof(void*)*3 + 2);
v___x_1675_ = lean_box(v_suppressElabErrors_1674_);
v___x_1676_ = lean_box(v___y_1669_);
v___f_1677_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1677_, 0, v___x_1675_);
lean_closure_set(v___f_1677_, 1, v___x_1676_);
v_ref_1678_ = l_Lean_replaceRef(v_ref_1584_, v_ref_1673_);
v___x_1679_ = l_Lean_Syntax_getPos_x3f(v_ref_1678_, v___y_1670_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_unsigned_to_nat(0u);
v___y_1659_ = v_suppressElabErrors_1674_;
v___y_1660_ = v___f_1677_;
v___y_1661_ = v_toCold_1672_;
v___y_1662_ = v_ref_1678_;
v___y_1663_ = v___y_1670_;
v___y_1664_ = v___y_1671_;
v___y_1665_ = v___x_1680_;
goto v___jp_1658_;
}
else
{
lean_object* v_val_1681_; 
v_val_1681_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v___x_1679_, 1);
v___y_1659_ = v_suppressElabErrors_1674_;
v___y_1660_ = v___f_1677_;
v___y_1661_ = v_toCold_1672_;
v___y_1662_ = v_ref_1678_;
v___y_1663_ = v___y_1670_;
v___y_1664_ = v___y_1671_;
v___y_1665_ = v_val_1681_;
goto v___jp_1658_;
}
}
v___jp_1683_:
{
if (v___y_1686_ == 0)
{
v___y_1669_ = v___y_1684_;
v___y_1670_ = v___y_1685_;
v___y_1671_ = v_severity_1586_;
goto v___jp_1668_;
}
else
{
v___y_1669_ = v___y_1684_;
v___y_1670_ = v___y_1685_;
v___y_1671_ = v___x_1682_;
goto v___jp_1668_;
}
}
v___jp_1687_:
{
if (v___y_1688_ == 0)
{
uint8_t v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = 1;
v___x_1690_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1586_, v___x_1689_);
if (v___x_1690_ == 0)
{
v___y_1684_ = v___y_1688_;
v___y_1685_ = v___y_1688_;
v___y_1686_ = v___x_1690_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1691_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1589_);
v___x_1692_ = l_Lean_warningAsError;
v___x_1693_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v___x_1691_, v___x_1692_);
lean_dec_ref(v___x_1691_);
v___y_1684_ = v___y_1688_;
v___y_1685_ = v___y_1688_;
v___y_1686_ = v___x_1693_;
goto v___jp_1683_;
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec_ref(v_msgData_1585_);
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___y_1588_);
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
return v___x_1696_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1584_ = stack[0].m_obj;
lean_object* v_msgData_1585_ = stack[1].m_obj;
uint8_t v_severity_1586_ = stack[2].m_num;
uint8_t v_isSilent_1587_ = stack[3].m_num;
lean_object* v___y_1588_ = stack[4].m_obj;
lean_object* v___y_1589_ = stack[5].m_obj;
lean_object* v___y_1590_ = stack[6].m_obj;
lean_object* v_res_1699_;
v_res_1699_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1584_, v_msgData_1585_, v_severity_1586_, v_isSilent_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
stack->m_obj
 = v_res_1699_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1700_, lean_object* v_msgData_1701_, lean_object* v_severity_1702_, lean_object* v_isSilent_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_severity_boxed_1708_; uint8_t v_isSilent_boxed_1709_; lean_object* v_res_1710_; 
v_severity_boxed_1708_ = lean_unbox(v_severity_1702_);
v_isSilent_boxed_1709_ = lean_unbox(v_isSilent_1703_);
v_res_1710_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1700_, v_msgData_1701_, v_severity_boxed_1708_, v_isSilent_boxed_1709_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v_ref_1700_);
return v_res_1710_;
}
}
lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1711_, lean_object* v_msgData_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v___x_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = 2;
v___x_1718_ = 0;
v___x_1719_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1711_, v_msgData_1712_, v___x_1717_, v___x_1718_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1719_;
}
}
LEAN_EXPORT void l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1711_ = stack[0].m_obj;
lean_object* v_msgData_1712_ = stack[1].m_obj;
lean_object* v___y_1713_ = stack[2].m_obj;
lean_object* v___y_1714_ = stack[3].m_obj;
lean_object* v___y_1715_ = stack[4].m_obj;
lean_object* v_res_1720_;
v_res_1720_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1711_, v_msgData_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
stack->m_obj
 = v_res_1720_;
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1721_, lean_object* v_msgData_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1721_, v_msgData_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v_ref_1721_);
return v_res_1727_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1731_ = l_Lean_MessageData_ofFormat(v___x_1730_);
return v___x_1731_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1732_, lean_object* v_as_1733_, size_t v_sz_1734_, size_t v_i_1735_, uint8_t v_b_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_snd_1742_; lean_object* v_snd_1743_; lean_object* v___y_1749_; uint8_t v___y_1750_; lean_object* v_a_1767_; uint8_t v___x_1770_; 
v___x_1770_ = lean_usize_dec_lt(v_i_1735_, v_sz_1734_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_box(v_b_1736_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___y_1737_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1775_; uint8_t v_recovering_1776_; 
v_a_1774_ = lean_array_uget_borrowed(v_as_1733_, v_i_1735_);
v___x_1775_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1774_);
v_recovering_1776_ = l_Lean_Syntax_isOfKind(v_a_1774_, v___x_1775_);
if (v_recovering_1776_ == 0)
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_a_1774_);
v___x_1778_ = l_Lean_Syntax_isOfKind(v_a_1774_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1774_);
v___x_1780_ = l_Lean_Syntax_isOfKind(v_a_1774_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1737_);
v___x_1782_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1774_, v___x_1781_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v_snd_1784_; lean_object* v___x_1785_; 
lean_dec_ref(v___y_1737_);
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v_snd_1784_ = lean_ctor_get(v_a_1783_, 1);
lean_inc(v_snd_1784_);
lean_dec(v_a_1783_);
v___x_1785_ = lean_box(v_b_1736_);
v_snd_1742_ = v___x_1785_;
v_snd_1743_ = v_snd_1784_;
goto v___jp_1741_;
}
else
{
lean_object* v_a_1786_; 
v_a_1786_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1782_, 1);
v_a_1767_ = v_a_1786_;
goto v___jp_1766_;
}
}
else
{
lean_object* v___x_1787_; 
lean_inc_ref(v___y_1737_);
lean_inc(v_a_1774_);
v___x_1787_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1774_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v_snd_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v___y_1737_);
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v_snd_1789_ = lean_ctor_get(v_a_1788_, 1);
lean_inc(v_snd_1789_);
lean_dec(v_a_1788_);
v___x_1790_ = lean_box(v_recovering_1776_);
v_snd_1742_ = v___x_1790_;
v_snd_1743_ = v_snd_1789_;
goto v___jp_1741_;
}
else
{
lean_object* v_a_1791_; 
v_a_1791_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1787_, 1);
v_a_1767_ = v_a_1791_;
goto v___jp_1766_;
}
}
}
else
{
lean_object* v___x_1792_; 
lean_inc_ref(v___y_1737_);
lean_inc(v_a_1774_);
v___x_1792_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1774_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v_snd_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v___y_1737_);
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v_snd_1794_ = lean_ctor_get(v_a_1793_, 1);
lean_inc(v_snd_1794_);
lean_dec(v_a_1793_);
v___x_1795_ = lean_box(v_recovering_1776_);
v_snd_1742_ = v___x_1795_;
v_snd_1743_ = v_snd_1794_;
goto v___jp_1741_;
}
else
{
lean_object* v_a_1796_; 
v_a_1796_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1792_, 1);
v_a_1767_ = v_a_1796_;
goto v___jp_1766_;
}
}
}
else
{
if (v_b_1736_ == 0)
{
lean_object* v___x_1797_; 
lean_inc_ref(v___y_1737_);
lean_inc(v_a_1774_);
v___x_1797_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1774_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v_snd_1799_; lean_object* v___x_1800_; 
lean_dec_ref(v___y_1737_);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v_snd_1799_ = lean_ctor_get(v_a_1798_, 1);
lean_inc(v_snd_1799_);
lean_dec(v_a_1798_);
v___x_1800_ = lean_box(v_b_1736_);
v_snd_1742_ = v___x_1800_;
v_snd_1743_ = v_snd_1799_;
goto v___jp_1741_;
}
else
{
lean_object* v_a_1801_; 
v_a_1801_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1797_, 1);
v_a_1767_ = v_a_1801_;
goto v___jp_1766_;
}
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_box(v_b_1736_);
v_snd_1742_ = v___x_1802_;
v_snd_1743_ = v___y_1737_;
goto v___jp_1741_;
}
}
}
v___jp_1741_:
{
size_t v___x_1744_; size_t v___x_1745_; uint8_t v___x_1746_; 
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1735_, v___x_1744_);
v___x_1746_ = lean_unbox(v_snd_1742_);
lean_dec(v_snd_1742_);
v_i_1735_ = v___x_1745_;
v_b_1736_ = v___x_1746_;
v___y_1737_ = v_snd_1743_;
goto _start;
}
v___jp_1748_:
{
if (v___y_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = l_Lean_Exception_getRef(v___y_1749_);
v___x_1752_ = l_Lean_Exception_toMessageData(v___y_1749_);
v___x_1753_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1751_, v___x_1752_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___x_1751_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v_snd_1755_; lean_object* v___x_1756_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v_snd_1755_ = lean_ctor_get(v_a_1754_, 1);
lean_inc(v_snd_1755_);
lean_dec(v_a_1754_);
v___x_1756_ = lean_box(v_recovering_1732_);
v_snd_1742_ = v___x_1756_;
v_snd_1743_ = v_snd_1755_;
goto v___jp_1741_;
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_a_1757_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1753_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1753_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_object* v___x_1765_; 
lean_dec_ref(v___y_1737_);
v___x_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___y_1749_);
return v___x_1765_;
}
}
v___jp_1766_:
{
uint8_t v___x_1768_; 
v___x_1768_ = l_Lean_Exception_isInterrupt(v_a_1767_);
if (v___x_1768_ == 0)
{
uint8_t v___x_1769_; 
lean_inc_ref(v_a_1767_);
v___x_1769_ = l_Lean_Exception_isRuntime(v_a_1767_);
v___y_1749_ = v_a_1767_;
v___y_1750_ = v___x_1769_;
goto v___jp_1748_;
}
else
{
v___y_1749_ = v_a_1767_;
v___y_1750_ = v___x_1768_;
goto v___jp_1748_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_recovering_1732_ = stack[0].m_num;
lean_object* v_as_1733_ = stack[1].m_obj;
size_t v_sz_1734_ = stack[2].m_num;
size_t v_i_1735_ = stack[3].m_num;
uint8_t v_b_1736_ = stack[4].m_num;
lean_object* v___y_1737_ = stack[5].m_obj;
lean_object* v___y_1738_ = stack[6].m_obj;
lean_object* v___y_1739_ = stack[7].m_obj;
lean_object* v_res_1803_;
v_res_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1732_, v_as_1733_, v_sz_1734_, v_i_1735_, v_b_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
stack->m_obj
 = v_res_1803_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1804_, lean_object* v_as_1805_, lean_object* v_sz_1806_, lean_object* v_i_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
uint8_t v_recovering_boxed_1813_; size_t v_sz_boxed_1814_; size_t v_i_boxed_1815_; uint8_t v_b_boxed_1816_; lean_object* v_res_1817_; 
v_recovering_boxed_1813_ = lean_unbox(v_recovering_1804_);
v_sz_boxed_1814_ = lean_unbox_usize(v_sz_1806_);
lean_dec(v_sz_1806_);
v_i_boxed_1815_ = lean_unbox_usize(v_i_1807_);
lean_dec(v_i_1807_);
v_b_boxed_1816_ = lean_unbox(v_b_1808_);
v_res_1817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1813_, v_as_1805_, v_sz_boxed_1814_, v_i_boxed_1815_, v_b_boxed_1816_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec_ref(v_as_1805_);
return v_res_1817_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_ref_1822_; lean_object* v___x_1823_; lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1832_; 
v_ref_1822_ = lean_ctor_get(v___y_1819_, 2);
v___x_1823_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1818_, v___y_1819_, v___y_1820_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1832_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1832_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
lean_inc(v_ref_1822_);
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_ref_1822_);
lean_ctor_set(v___x_1828_, 1, v_a_1824_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 1);
lean_ctor_set(v___x_1826_, 0, v___x_1828_);
v___x_1830_ = v___x_1826_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1818_ = stack[0].m_obj;
lean_object* v___y_1819_ = stack[1].m_obj;
lean_object* v___y_1820_ = stack[2].m_obj;
lean_object* v_res_1833_;
v_res_1833_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1818_, v___y_1819_, v___y_1820_);
stack->m_obj
 = v_res_1833_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1838_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1839_, lean_object* v_msg_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_toCold_1844_; lean_object* v_currRecDepth_1845_; lean_object* v_ref_1846_; uint16_t v_optionFlags_1847_; uint8_t v_suppressElabErrors_1848_; uint8_t v_isRecordingDeps_1849_; lean_object* v_ref_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_toCold_1844_ = lean_ctor_get(v___y_1841_, 0);
v_currRecDepth_1845_ = lean_ctor_get(v___y_1841_, 1);
v_ref_1846_ = lean_ctor_get(v___y_1841_, 2);
v_optionFlags_1847_ = lean_ctor_get_uint16(v___y_1841_, sizeof(void*)*3);
v_suppressElabErrors_1848_ = lean_ctor_get_uint8(v___y_1841_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1849_ = lean_ctor_get_uint8(v___y_1841_, sizeof(void*)*3 + 3);
v_ref_1850_ = l_Lean_replaceRef(v_ref_1839_, v_ref_1846_);
lean_inc(v_currRecDepth_1845_);
lean_inc_ref(v_toCold_1844_);
v___x_1851_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1851_, 0, v_toCold_1844_);
lean_ctor_set(v___x_1851_, 1, v_currRecDepth_1845_);
lean_ctor_set(v___x_1851_, 2, v_ref_1850_);
lean_ctor_set_uint16(v___x_1851_, sizeof(void*)*3, v_optionFlags_1847_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*3 + 2, v_suppressElabErrors_1848_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*3 + 3, v_isRecordingDeps_1849_);
v___x_1852_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1840_, v___x_1851_, v___y_1842_);
lean_dec_ref_known(v___x_1851_, 3);
return v___x_1852_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1839_ = stack[0].m_obj;
lean_object* v_msg_1840_ = stack[1].m_obj;
lean_object* v___y_1841_ = stack[2].m_obj;
lean_object* v___y_1842_ = stack[3].m_obj;
lean_object* v_res_1853_;
v_res_1853_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1839_, v_msg_1840_, v___y_1841_, v___y_1842_);
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1854_, lean_object* v_msg_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1854_, v_msg_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v_ref_1854_);
return v_res_1859_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1867_ = l_Lean_stringToMessageData(v___x_1866_);
return v___x_1867_;
}
}
lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1872_);
v___x_1877_ = l_Lean_Syntax_isOfKind(v_x_1872_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1879_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1872_, v___x_1878_, v_a_1873_, v_a_1874_);
lean_dec(v_x_1872_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v_recovering_1883_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = l_Lean_Syntax_getArg(v_x_1872_, v___x_1880_);
v___x_1882_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1883_ = l_Lean_Syntax_isOfKind(v___x_1881_, v___x_1882_);
if (v_recovering_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1885_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1872_, v___x_1884_, v_a_1873_, v_a_1874_);
lean_dec(v_x_1872_);
return v___x_1885_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v_xs_1888_; uint8_t v_recovering_1889_; lean_object* v___x_1890_; size_t v_sz_1891_; size_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1886_ = lean_unsigned_to_nat(1u);
v___x_1887_ = l_Lean_Syntax_getArg(v_x_1872_, v___x_1886_);
lean_dec(v_x_1872_);
v_xs_1888_ = l_Lean_Syntax_getArgs(v___x_1887_);
lean_dec(v___x_1887_);
v_recovering_1889_ = 0;
v___x_1890_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1888_);
lean_dec_ref(v_xs_1888_);
v_sz_1891_ = lean_array_size(v___x_1890_);
v___x_1892_ = ((size_t)0ULL);
v___x_1893_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1883_, v___x_1890_, v_sz_1891_, v___x_1892_, v_recovering_1889_, v___x_1893_, v_a_1873_, v_a_1874_);
lean_dec_ref(v___x_1890_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1905_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1905_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1905_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_snd_1899_; lean_object* v_items_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v_snd_1899_ = lean_ctor_get(v_a_1895_, 1);
lean_inc(v_snd_1899_);
lean_dec(v_a_1895_);
v_items_1900_ = lean_ctor_get(v_snd_1899_, 5);
lean_inc_ref(v_items_1900_);
lean_dec(v_snd_1899_);
v___x_1901_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1900_);
lean_dec_ref(v_items_1900_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1901_);
v___x_1903_ = v___x_1897_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1906_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1894_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1894_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_Toml_elabToml_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1872_ = stack[0].m_obj;
lean_object* v_a_1873_ = stack[1].m_obj;
lean_object* v_a_1874_ = stack[2].m_obj;
lean_object* v_res_1914_;
v_res_1914_ = l_Lake_Toml_elabToml(v_x_1872_, v_a_1873_, v_a_1874_);
stack->m_obj
 = v_res_1914_;
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
lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1920_, lean_object* v_ref_1921_, lean_object* v_msg_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1921_, v_msg_1922_, v___y_1923_, v___y_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1921_ = stack[1].m_obj;
lean_object* v_msg_1922_ = stack[2].m_obj;
lean_object* v___y_1923_ = stack[3].m_obj;
lean_object* v___y_1924_ = stack[4].m_obj;
lean_object* v_res_1927_;
v_res_1927_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_box(0), v_ref_1921_, v_msg_1922_, v___y_1923_, v___y_1924_);
stack->m_obj
 = v_res_1927_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1928_, lean_object* v_ref_1929_, lean_object* v_msg_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1928_, v_ref_1929_, v_msg_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v_ref_1929_);
return v_res_1934_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1935_, lean_object* v_msg_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1936_, v___y_1937_, v___y_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1936_ = stack[1].m_obj;
lean_object* v___y_1937_ = stack[2].m_obj;
lean_object* v___y_1938_ = stack[3].m_obj;
lean_object* v_res_1941_;
v_res_1941_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_box(0), v_msg_1936_, v___y_1937_, v___y_1938_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1942_, lean_object* v_msg_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1942_, v_msg_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1947_;
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
