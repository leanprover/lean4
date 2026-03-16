// Lean compiler output
// Module: Lean.Elab.AssertExists
// Imports: public import Lean.Elab.Command
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t l_Bool_instDecidableLt(uint8_t, uint8_t);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Std_HashSet_instInhabited(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_crossEmoji;
extern lean_object* l_Lean_checkEmoji;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Environment_importPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Environment_importPath___closed__0 = (const lean_object*)&l_Lean_Environment_importPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Environment_importPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_importPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_instBEqAssertExists_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instBEqAssertExists_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_instBEqAssertExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instBEqAssertExists_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_instBEqAssertExists___closed__0 = (const lean_object*)&l_Lean_Elab_Command_instBEqAssertExists___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Command_instBEqAssertExists = (const lean_object*)&l_Lean_Elab_Command_instBEqAssertExists___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_Elab_Command_instHashableAssertExists_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instHashableAssertExists_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Command_instHashableAssertExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instHashableAssertExists_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_instHashableAssertExists___closed__0 = (const lean_object*)&l_Lean_Elab_Command_instHashableAssertExists___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Command_instHashableAssertExists = (const lean_object*)&l_Lean_Elab_Command_instHashableAssertExists___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn___lam__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn___lam__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_initFn___lam__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_initFn___lam__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "assertExistsExt"};
static const lean_object* l_Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 190, 77, 153, 163, 56, 32, 184)}};
static const lean_object* l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_assertExistsExt;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addAssertExistsEntry___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addAssertExistsEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addAssertExistsEntry(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addAssertExistsEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Command_getSortedAssertExists_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Command_getSortedAssertExists___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_getSortedAssertExists___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getSortedAssertExists(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "\n  which is imported by "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_importPathMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "\n  which is imported by this file."};
static const lean_object* l_Lean_Elab_Command_importPathMessage___closed__0 = (const lean_object*)&l_Lean_Elab_Command_importPathMessage___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Command_importPathMessage___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_importPathMessage___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_importPathMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_importPathMessage___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabImportPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Declaration "};
static const lean_object* l_Lean_Elab_Command_elabImportPath___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Command_elabImportPath___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabImportPath___closed__1;
static const lean_string_object l_Lean_Elab_Command_elabImportPath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " is imported via\n"};
static const lean_object* l_Lean_Elab_Command_elabImportPath___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Command_elabImportPath___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabImportPath___closed__3;
static const lean_string_object l_Lean_Elab_Command_elabImportPath___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " is defined in this file."};
static const lean_object* l_Lean_Elab_Command_elabImportPath___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Command_elabImportPath___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabImportPath___closed__5;
static const lean_string_object l_Lean_Elab_Command_elabImportPath___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Declaration '"};
static const lean_object* l_Lean_Elab_Command_elabImportPath___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Command_elabImportPath___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabImportPath___closed__7;
static const lean_string_object l_Lean_Elab_Command_elabImportPath___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "' is not in scope."};
static const lean_object* l_Lean_Elab_Command_elabImportPath___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Command_elabImportPath___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabImportPath___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "importPath"};
static const lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(107, 162, 88, 45, 100, 199, 50, 9)}};
static const lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabImportPath"};
static const lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(132, 84, 165, 83, 249, 15, 141, 145)}};
static const lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 248, .m_capacity = 248, .m_length = 247, .m_data = "`#import_path Foo` prints the transitive import chain that brings the declaration `Foo`\ninto the current file's scope.\n\nThis is useful for understanding why a particular declaration is available,\nespecially when debugging unexpected dependencies.\n"};
static const lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 220, .m_capacity = 220, .m_length = 219, .m_data = "\n\nThese invariants are maintained by `assert_not_exists` statements, and exist in order to ensure that \"complicated\" parts of the library are not accidentally introduced as dependencies of \"simple\" parts of the library."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = " is not allowed to be imported by this file.\nIt is defined in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "assertNotExists"};
static const lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 12, 165, 84, 72, 16, 34, 200)}};
static const lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabAssertNotExists"};
static const lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(26, 89, 203, 163, 167, 88, 147, 25)}};
static const lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 822, .m_capacity = 822, .m_length = 807, .m_data = "`assert_not_exists d₁ d₂ ... dₙ` is a command that asserts that the declarations named\n`d₁ d₂ ... dₙ` *do not exist* in the current import scope.\n\nBe careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).\n\nIt may be used (sparingly!) to enforce plans that certain files are independent of each other.\n\nIf you encounter an error on an `assert_not_exists` command while developing a library,\nit is probably because you have introduced new import dependencies to a file.\nIn this case, you should refactor your work\n(for example by creating new files rather than adding imports to existing files).\nYou should *not* delete the `assert_not_exists` statement without careful discussion ahead of time.\n\n`assert_not_exists` statements should generally live at the top of the file, after the module doc.\n"};
static const lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "the module '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "' is (transitively) imported via\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "assertNotImported"};
static const lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 142, 19, 163, 216, 15, 246, 138)}};
static const lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabAssertNotImported"};
static const lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 106, 174, 153, 200, 206, 100, 97)}};
static const lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 251, .m_capacity = 251, .m_length = 232, .m_data = "`assert_not_imported m₁ m₂ ... mₙ` checks that each one of the modules `m₁ m₂ ... mₙ` is not\namong the transitive imports of the current file.\n\nThe command does not currently check whether the modules `m₁ m₂ ... mₙ` actually exist.\n"};
static const lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "' ("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ") asserted in '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__11_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__0;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__1;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__2;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__3;
static const lean_string_object l_Lean_Elab_Command_elabCheckAssertions___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "---"};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__5;
static const lean_string_object l_Lean_Elab_Command_elabCheckAssertions___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = " means the declaration or import exists."};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__7;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__8;
static const lean_string_object l_Lean_Elab_Command_elabCheckAssertions___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = " means the declaration or import does not exist."};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__10;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__11;
static const lean_string_object l_Lean_Elab_Command_elabCheckAssertions___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___closed__12_value)}};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__14;
static const lean_string_object l_Lean_Elab_Command_elabCheckAssertions___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "No assertions made."};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___closed__15_value)}};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCheckAssertions___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCheckAssertions___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "checkAssertions"};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 218, 120, 53, 168, 205, 138, 249)}};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabCheckAssertions"};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(110, 95, 94, 234, 82, 254, 243, 188)}};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 776, .m_capacity = 776, .m_length = 772, .m_data = "`#check_assertions` retrieves all declarations and all imports that were declared\nnot to exist so far (including in transitively imported files) and reports their current\nstatus:\n* ✓ means the declaration or import exists,\n* × means the declaration or import does not exist.\n\nThis means that the expectation is that all checks *succeed* by the time `#check_assertions`\nis used, typically once all of the library has been built.\n\nIf all declarations and imports are available when `#check_assertions` is used,\nthen the command logs an info message. Otherwise, it emits a warning.\n\nThe variant `#check_assertions!` only prints declarations/imports that are not present in the\nenvironment. In particular, it is silent if everything is imported, making it useful for testing.\n"};
static const lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0(lean_object* v___x_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_3_, v_stop_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v_module_7_; uint8_t v___x_8_; 
v___x_6_ = lean_array_uget_borrowed(v_as_2_, v_i_3_);
v_module_7_ = lean_ctor_get(v___x_6_, 0);
v___x_8_ = lean_name_eq(v_module_7_, v___x_1_);
if (v___x_8_ == 0)
{
size_t v___x_9_; size_t v___x_10_; 
v___x_9_ = ((size_t)1ULL);
v___x_10_ = lean_usize_add(v_i_3_, v___x_9_);
v_i_3_ = v___x_10_;
goto _start;
}
else
{
return v___x_8_;
}
}
else
{
uint8_t v___x_12_; 
v___x_12_ = 0;
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0___boxed(lean_object* v___x_13_, lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_){
_start:
{
size_t v_i_boxed_17_; size_t v_stop_boxed_18_; uint8_t v_res_19_; lean_object* v_r_20_; 
v_i_boxed_17_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_18_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0(v___x_13_, v_as_14_, v_i_boxed_17_, v_stop_boxed_18_);
lean_dec_ref(v_as_14_);
lean_dec(v___x_13_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg(lean_object* v_modData_21_, lean_object* v_modNames_22_, lean_object* v_range_23_, lean_object* v_b_24_, lean_object* v_i_25_){
_start:
{
lean_object* v_stop_26_; lean_object* v_step_27_; lean_object* v_a_29_; uint8_t v___x_32_; 
v_stop_26_ = lean_ctor_get(v_range_23_, 1);
v_step_27_ = lean_ctor_get(v_range_23_, 2);
v___x_32_ = lean_nat_dec_lt(v_i_25_, v_stop_26_);
if (v___x_32_ == 0)
{
lean_dec(v_i_25_);
return v_b_24_;
}
else
{
lean_object* v_fst_33_; lean_object* v_snd_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_55_; 
v_fst_33_ = lean_ctor_get(v_b_24_, 0);
v_snd_34_ = lean_ctor_get(v_b_24_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_b_24_);
if (v_isSharedCheck_55_ == 0)
{
v___x_36_ = v_b_24_;
v_isShared_37_ = v_isSharedCheck_55_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_snd_34_);
lean_inc(v_fst_33_);
lean_dec(v_b_24_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_55_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_imports_44_; lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_42_ = l_Lean_instInhabitedModuleData_default;
v___x_43_ = lean_array_get_borrowed(v___x_42_, v_modData_21_, v_i_25_);
v_imports_44_ = lean_ctor_get(v___x_43_, 0);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_array_get_size(v_imports_44_);
v___x_47_ = lean_nat_dec_lt(v___x_45_, v___x_46_);
if (v___x_47_ == 0)
{
goto v___jp_38_;
}
else
{
if (v___x_47_ == 0)
{
goto v___jp_38_;
}
else
{
size_t v___x_48_; size_t v___x_49_; uint8_t v___x_50_; 
v___x_48_ = ((size_t)0ULL);
v___x_49_ = lean_usize_of_nat(v___x_46_);
v___x_50_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0(v_snd_34_, v_imports_44_, v___x_48_, v___x_49_);
if (v___x_50_ == 0)
{
goto v___jp_38_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_del_object(v___x_36_);
lean_dec(v_snd_34_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_array_get_borrowed(v___x_51_, v_modNames_22_, v_i_25_);
lean_inc(v___x_52_);
v___x_53_ = lean_array_push(v_fst_33_, v___x_52_);
lean_inc(v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_52_);
v_a_29_ = v___x_54_;
goto v___jp_28_;
}
}
}
v___jp_38_:
{
lean_object* v___x_40_; 
if (v_isShared_37_ == 0)
{
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_fst_33_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_snd_34_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
v_a_29_ = v___x_40_;
goto v___jp_28_;
}
}
}
}
v___jp_28_:
{
lean_object* v___x_30_; 
v___x_30_ = lean_nat_add(v_i_25_, v_step_27_);
lean_dec(v_i_25_);
v_b_24_ = v_a_29_;
v_i_25_ = v___x_30_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg___boxed(lean_object* v_modData_56_, lean_object* v_modNames_57_, lean_object* v_range_58_, lean_object* v_b_59_, lean_object* v_i_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg(v_modData_56_, v_modNames_57_, v_range_58_, v_b_59_, v_i_60_);
lean_dec_ref(v_range_58_);
lean_dec_ref(v_modNames_57_);
lean_dec_ref(v_modData_56_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_importPath(lean_object* v_env_64_, lean_object* v_imported_65_){
_start:
{
lean_object* v___x_66_; lean_object* v_moduleData_67_; lean_object* v_result_68_; lean_object* v___x_69_; 
v___x_66_ = l_Lean_Environment_header(v_env_64_);
v_moduleData_67_ = lean_ctor_get(v___x_66_, 6);
lean_inc_ref(v_moduleData_67_);
v_result_68_ = ((lean_object*)(l_Lean_Environment_importPath___closed__0));
v___x_69_ = l_Lean_Environment_getModuleIdx_x3f(v_env_64_, v_imported_65_);
if (lean_obj_tag(v___x_69_) == 1)
{
lean_object* v_val_70_; lean_object* v_modNames_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v_fst_78_; 
v_val_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_val_70_);
lean_dec_ref(v___x_69_);
v_modNames_71_ = l_Lean_EnvironmentHeader_moduleNames(v___x_66_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_val_70_, v___x_72_);
lean_dec(v_val_70_);
v___x_74_ = lean_array_get_size(v_moduleData_67_);
lean_inc(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
lean_ctor_set(v___x_75_, 2, v___x_72_);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v_result_68_);
lean_ctor_set(v___x_76_, 1, v_imported_65_);
v___x_77_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg(v_moduleData_67_, v_modNames_71_, v___x_75_, v___x_76_, v___x_73_);
lean_dec_ref(v___x_75_);
lean_dec_ref(v_modNames_71_);
lean_dec_ref(v_moduleData_67_);
v_fst_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_fst_78_);
lean_dec_ref(v___x_77_);
return v_fst_78_;
}
else
{
lean_dec(v___x_69_);
lean_dec_ref(v_moduleData_67_);
lean_dec_ref(v___x_66_);
lean_dec(v_imported_65_);
return v_result_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_importPath___boxed(lean_object* v_env_79_, lean_object* v_imported_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Environment_importPath(v_env_79_, v_imported_80_);
lean_dec_ref(v_env_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1(lean_object* v_modData_82_, lean_object* v_modNames_83_, lean_object* v_range_84_, lean_object* v_b_85_, lean_object* v_i_86_, lean_object* v_hs_87_, lean_object* v_hl_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg(v_modData_82_, v_modNames_83_, v_range_84_, v_b_85_, v_i_86_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___boxed(lean_object* v_modData_90_, lean_object* v_modNames_91_, lean_object* v_range_92_, lean_object* v_b_93_, lean_object* v_i_94_, lean_object* v_hs_95_, lean_object* v_hl_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1(v_modData_90_, v_modNames_91_, v_range_92_, v_b_93_, v_i_94_, v_hs_95_, v_hl_96_);
lean_dec_ref(v_range_92_);
lean_dec_ref(v_modNames_91_);
lean_dec_ref(v_modData_90_);
return v_res_97_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_instBEqAssertExists_beq(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
uint8_t v_isDecl_100_; lean_object* v_givenName_101_; lean_object* v_modName_102_; uint8_t v_isDecl_103_; lean_object* v_givenName_104_; lean_object* v_modName_105_; 
v_isDecl_100_ = lean_ctor_get_uint8(v_x_98_, sizeof(void*)*2);
v_givenName_101_ = lean_ctor_get(v_x_98_, 0);
v_modName_102_ = lean_ctor_get(v_x_98_, 1);
v_isDecl_103_ = lean_ctor_get_uint8(v_x_99_, sizeof(void*)*2);
v_givenName_104_ = lean_ctor_get(v_x_99_, 0);
v_modName_105_ = lean_ctor_get(v_x_99_, 1);
if (v_isDecl_100_ == 0)
{
if (v_isDecl_103_ == 0)
{
goto v___jp_106_;
}
else
{
return v_isDecl_100_;
}
}
else
{
if (v_isDecl_103_ == 0)
{
return v_isDecl_103_;
}
else
{
goto v___jp_106_;
}
}
v___jp_106_:
{
uint8_t v___x_107_; 
v___x_107_ = lean_name_eq(v_givenName_101_, v_givenName_104_);
if (v___x_107_ == 0)
{
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = lean_name_eq(v_modName_102_, v_modName_105_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instBEqAssertExists_beq___boxed(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Lean_Elab_Command_instBEqAssertExists_beq(v_x_109_, v_x_110_);
lean_dec_ref(v_x_110_);
lean_dec_ref(v_x_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
static uint64_t _init_l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0(void){
_start:
{
lean_object* v___x_115_; uint64_t v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(1723u);
v___x_116_ = lean_uint64_of_nat(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT uint64_t l_Lean_Elab_Command_instHashableAssertExists_hash(lean_object* v_x_117_){
_start:
{
uint8_t v_isDecl_118_; lean_object* v_givenName_119_; lean_object* v_modName_120_; uint64_t v___y_122_; uint64_t v___y_123_; uint64_t v___x_129_; uint64_t v___y_131_; 
v_isDecl_118_ = lean_ctor_get_uint8(v_x_117_, sizeof(void*)*2);
v_givenName_119_ = lean_ctor_get(v_x_117_, 0);
v_modName_120_ = lean_ctor_get(v_x_117_, 1);
v___x_129_ = 0ULL;
if (v_isDecl_118_ == 0)
{
uint64_t v___x_135_; 
v___x_135_ = 13ULL;
v___y_131_ = v___x_135_;
goto v___jp_130_;
}
else
{
uint64_t v___x_136_; 
v___x_136_ = 11ULL;
v___y_131_ = v___x_136_;
goto v___jp_130_;
}
v___jp_121_:
{
uint64_t v___x_124_; 
v___x_124_ = lean_uint64_mix_hash(v___y_122_, v___y_123_);
if (lean_obj_tag(v_modName_120_) == 0)
{
uint64_t v___x_125_; uint64_t v___x_126_; 
v___x_125_ = lean_uint64_once(&l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0, &l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0_once, _init_l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0);
v___x_126_ = lean_uint64_mix_hash(v___x_124_, v___x_125_);
return v___x_126_;
}
else
{
uint64_t v_hash_127_; uint64_t v___x_128_; 
v_hash_127_ = lean_ctor_get_uint64(v_modName_120_, sizeof(void*)*2);
v___x_128_ = lean_uint64_mix_hash(v___x_124_, v_hash_127_);
return v___x_128_;
}
}
v___jp_130_:
{
uint64_t v___x_132_; 
v___x_132_ = lean_uint64_mix_hash(v___x_129_, v___y_131_);
if (lean_obj_tag(v_givenName_119_) == 0)
{
uint64_t v___x_133_; 
v___x_133_ = lean_uint64_once(&l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0, &l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0_once, _init_l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0);
v___y_122_ = v___x_132_;
v___y_123_ = v___x_133_;
goto v___jp_121_;
}
else
{
uint64_t v_hash_134_; 
v_hash_134_ = lean_ctor_get_uint64(v_givenName_119_, sizeof(void*)*2);
v___y_122_ = v___x_132_;
v___y_123_ = v_hash_134_;
goto v___jp_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instHashableAssertExists_hash___boxed(lean_object* v_x_137_){
_start:
{
uint64_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lean_Elab_Command_instHashableAssertExists_hash(v_x_137_);
lean_dec_ref(v_x_137_);
v_r_139_ = lean_box_uint64(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn___lam__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(lean_object* v_es_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_array_mk(v_es_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
return v_x_144_;
}
else
{
lean_object* v_key_146_; lean_object* v_value_147_; lean_object* v_tail_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_171_; 
v_key_146_ = lean_ctor_get(v_x_145_, 0);
v_value_147_ = lean_ctor_get(v_x_145_, 1);
v_tail_148_ = lean_ctor_get(v_x_145_, 2);
v_isSharedCheck_171_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_171_ == 0)
{
v___x_150_ = v_x_145_;
v_isShared_151_ = v_isSharedCheck_171_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_tail_148_);
lean_inc(v_value_147_);
lean_inc(v_key_146_);
lean_dec(v_x_145_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_171_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v_fold_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_152_ = lean_array_get_size(v_x_144_);
v___x_153_ = l_Lean_Elab_Command_instHashableAssertExists_hash(v_key_146_);
v___x_154_ = 32ULL;
v___x_155_ = lean_uint64_shift_right(v___x_153_, v___x_154_);
v_fold_156_ = lean_uint64_xor(v___x_153_, v___x_155_);
v___x_157_ = 16ULL;
v___x_158_ = lean_uint64_shift_right(v_fold_156_, v___x_157_);
v___x_159_ = lean_uint64_xor(v_fold_156_, v___x_158_);
v___x_160_ = lean_uint64_to_usize(v___x_159_);
v___x_161_ = lean_usize_of_nat(v___x_152_);
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_sub(v___x_161_, v___x_162_);
v___x_164_ = lean_usize_land(v___x_160_, v___x_163_);
v___x_165_ = lean_array_uget_borrowed(v_x_144_, v___x_164_);
lean_inc(v___x_165_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 2, v___x_165_);
v___x_167_ = v___x_150_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_key_146_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_value_147_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v___x_165_);
v___x_167_ = v_reuseFailAlloc_170_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; 
v___x_168_ = lean_array_uset(v_x_144_, v___x_164_, v___x_167_);
v_x_144_ = v___x_168_;
v_x_145_ = v_tail_148_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5___redArg(lean_object* v_i_172_, lean_object* v_source_173_, lean_object* v_target_174_){
_start:
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = lean_array_get_size(v_source_173_);
v___x_176_ = lean_nat_dec_lt(v_i_172_, v___x_175_);
if (v___x_176_ == 0)
{
lean_dec_ref(v_source_173_);
lean_dec(v_i_172_);
return v_target_174_;
}
else
{
lean_object* v_es_177_; lean_object* v___x_178_; lean_object* v_source_179_; lean_object* v_target_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_es_177_ = lean_array_fget(v_source_173_, v_i_172_);
v___x_178_ = lean_box(0);
v_source_179_ = lean_array_fset(v_source_173_, v_i_172_, v___x_178_);
v_target_180_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6___redArg(v_target_174_, v_es_177_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_i_172_, v___x_181_);
lean_dec(v_i_172_);
v_i_172_ = v___x_182_;
v_source_173_ = v_source_179_;
v_target_174_ = v_target_180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_data_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_nbuckets_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_185_ = lean_array_get_size(v_data_184_);
v___x_186_ = lean_unsigned_to_nat(2u);
v_nbuckets_187_ = lean_nat_mul(v___x_185_, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_box(0);
v___x_190_ = lean_mk_array(v_nbuckets_187_, v___x_189_);
v___x_191_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5___redArg(v___x_188_, v_data_184_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
uint8_t v___x_194_; 
v___x_194_ = 0;
return v___x_194_;
}
else
{
lean_object* v_key_195_; lean_object* v_tail_196_; uint8_t v___x_197_; 
v_key_195_ = lean_ctor_get(v_x_193_, 0);
v_tail_196_ = lean_ctor_get(v_x_193_, 2);
v___x_197_ = l_Lean_Elab_Command_instBEqAssertExists_beq(v_key_195_, v_a_192_);
if (v___x_197_ == 0)
{
v_x_193_ = v_tail_196_;
goto _start;
}
else
{
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg(v_a_199_, v_x_200_);
lean_dec(v_x_200_);
lean_dec_ref(v_a_199_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2___redArg(lean_object* v_m_203_, lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
lean_object* v_size_206_; lean_object* v_buckets_207_; lean_object* v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v_fold_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; lean_object* v_bkt_221_; uint8_t v___x_222_; 
v_size_206_ = lean_ctor_get(v_m_203_, 0);
v_buckets_207_ = lean_ctor_get(v_m_203_, 1);
v___x_208_ = lean_array_get_size(v_buckets_207_);
v___x_209_ = l_Lean_Elab_Command_instHashableAssertExists_hash(v_a_204_);
v___x_210_ = 32ULL;
v___x_211_ = lean_uint64_shift_right(v___x_209_, v___x_210_);
v_fold_212_ = lean_uint64_xor(v___x_209_, v___x_211_);
v___x_213_ = 16ULL;
v___x_214_ = lean_uint64_shift_right(v_fold_212_, v___x_213_);
v___x_215_ = lean_uint64_xor(v_fold_212_, v___x_214_);
v___x_216_ = lean_uint64_to_usize(v___x_215_);
v___x_217_ = lean_usize_of_nat(v___x_208_);
v___x_218_ = ((size_t)1ULL);
v___x_219_ = lean_usize_sub(v___x_217_, v___x_218_);
v___x_220_ = lean_usize_land(v___x_216_, v___x_219_);
v_bkt_221_ = lean_array_uget_borrowed(v_buckets_207_, v___x_220_);
v___x_222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg(v_a_204_, v_bkt_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_243_; 
lean_inc_ref(v_buckets_207_);
lean_inc(v_size_206_);
v_isSharedCheck_243_ = !lean_is_exclusive(v_m_203_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; lean_object* v_unused_245_; 
v_unused_244_ = lean_ctor_get(v_m_203_, 1);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_m_203_, 0);
lean_dec(v_unused_245_);
v___x_224_ = v_m_203_;
v_isShared_225_ = v_isSharedCheck_243_;
goto v_resetjp_223_;
}
else
{
lean_dec(v_m_203_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_243_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v_size_x27_227_; lean_object* v___x_228_; lean_object* v_buckets_x27_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v_size_x27_227_ = lean_nat_add(v_size_206_, v___x_226_);
lean_dec(v_size_206_);
lean_inc(v_bkt_221_);
v___x_228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_228_, 0, v_a_204_);
lean_ctor_set(v___x_228_, 1, v_b_205_);
lean_ctor_set(v___x_228_, 2, v_bkt_221_);
v_buckets_x27_229_ = lean_array_uset(v_buckets_207_, v___x_220_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(4u);
v___x_231_ = lean_nat_mul(v_size_x27_227_, v___x_230_);
v___x_232_ = lean_unsigned_to_nat(3u);
v___x_233_ = lean_nat_div(v___x_231_, v___x_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_array_get_size(v_buckets_x27_229_);
v___x_235_ = lean_nat_dec_le(v___x_233_, v___x_234_);
lean_dec(v___x_233_);
if (v___x_235_ == 0)
{
lean_object* v_val_236_; lean_object* v___x_238_; 
v_val_236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4___redArg(v_buckets_x27_229_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_val_236_);
lean_ctor_set(v___x_224_, 0, v_size_x27_227_);
v___x_238_ = v___x_224_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_size_x27_227_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_val_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
else
{
lean_object* v___x_241_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_buckets_x27_229_);
lean_ctor_set(v___x_224_, 0, v_size_x27_227_);
v___x_241_ = v___x_224_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_size_x27_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_buckets_x27_229_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_dec(v_b_205_);
lean_dec_ref(v_a_204_);
return v_m_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_246_, size_t v_sz_247_, size_t v_i_248_, lean_object* v_b_249_){
_start:
{
uint8_t v___x_250_; 
v___x_250_ = lean_usize_dec_lt(v_i_248_, v_sz_247_);
if (v___x_250_ == 0)
{
return v_b_249_;
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v_r_253_; size_t v___x_254_; size_t v___x_255_; 
v_a_251_ = lean_array_uget_borrowed(v_as_246_, v_i_248_);
v___x_252_ = lean_box(0);
lean_inc(v_a_251_);
v_r_253_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2___redArg(v_b_249_, v_a_251_, v___x_252_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_i_248_, v___x_254_);
v_i_248_ = v___x_255_;
v_b_249_ = v_r_253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_257_, lean_object* v_sz_258_, lean_object* v_i_259_, lean_object* v_b_260_){
_start:
{
size_t v_sz_boxed_261_; size_t v_i_boxed_262_; lean_object* v_res_263_; 
v_sz_boxed_261_ = lean_unbox_usize(v_sz_258_);
lean_dec(v_sz_258_);
v_i_boxed_262_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_res_263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0(v_as_257_, v_sz_boxed_261_, v_i_boxed_262_, v_b_260_);
lean_dec_ref(v_as_257_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0(lean_object* v_m_264_, lean_object* v_l_265_){
_start:
{
size_t v_sz_266_; size_t v___x_267_; lean_object* v___x_268_; 
v_sz_266_ = lean_array_size(v_l_265_);
v___x_267_ = ((size_t)0ULL);
v___x_268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0(v_l_265_, v_sz_266_, v___x_267_, v_m_264_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0___boxed(lean_object* v_m_269_, lean_object* v_l_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0(v_m_269_, v_l_270_);
lean_dec_ref(v_l_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1(lean_object* v_as_272_, size_t v_i_273_, size_t v_stop_274_, lean_object* v_b_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = lean_usize_dec_eq(v_i_273_, v_stop_274_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; size_t v___x_279_; size_t v___x_280_; 
v___x_277_ = lean_array_uget_borrowed(v_as_272_, v_i_273_);
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0(v_b_275_, v___x_277_);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_add(v_i_273_, v___x_279_);
v_i_273_ = v___x_280_;
v_b_275_ = v___x_278_;
goto _start;
}
else
{
return v_b_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_282_, lean_object* v_i_283_, lean_object* v_stop_284_, lean_object* v_b_285_){
_start:
{
size_t v_i_boxed_286_; size_t v_stop_boxed_287_; lean_object* v_res_288_; 
v_i_boxed_286_ = lean_unbox_usize(v_i_283_);
lean_dec(v_i_283_);
v_stop_boxed_287_ = lean_unbox_usize(v_stop_284_);
lean_dec(v_stop_284_);
v_res_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1(v_as_282_, v_i_boxed_286_, v_stop_boxed_287_, v_b_285_);
lean_dec_ref(v_as_282_);
return v_res_288_;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_box(0);
v___x_290_ = lean_unsigned_to_nat(16u);
v___x_291_ = lean_mk_array(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_obj_once(&l_Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_, &l_Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__once, _init_l_Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v___x_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(lean_object* v_as_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_obj_once(&l_Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_, &l_Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__once, _init_l_Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_);
v___x_298_ = lean_array_get_size(v_as_295_);
v___x_299_ = lean_nat_dec_lt(v___x_296_, v___x_298_);
if (v___x_299_ == 0)
{
return v___x_297_;
}
else
{
uint8_t v___x_300_; 
v___x_300_ = lean_nat_dec_le(v___x_298_, v___x_298_);
if (v___x_300_ == 0)
{
if (v___x_299_ == 0)
{
return v___x_297_;
}
else
{
size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; 
v___x_301_ = ((size_t)0ULL);
v___x_302_ = lean_usize_of_nat(v___x_298_);
v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1(v_as_295_, v___x_301_, v___x_302_, v___x_297_);
return v___x_303_;
}
}
else
{
size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___x_304_ = ((size_t)0ULL);
v___x_305_ = lean_usize_of_nat(v___x_298_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1(v_as_295_, v___x_304_, v___x_305_, v___x_297_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2____boxed(lean_object* v_as_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(v_as_307_);
lean_dec_ref(v_as_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn___lam__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_box(0);
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2___redArg(v___y_309_, v___y_310_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_));
v___x_334_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2____boxed(lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_();
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_337_, lean_object* v_m_338_, lean_object* v_a_339_, lean_object* v_b_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2___redArg(v_m_338_, v_a_339_, v_b_340_);
return v___x_341_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_342_, lean_object* v_a_343_, lean_object* v_x_344_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg(v_a_343_, v_x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_346_, lean_object* v_a_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_346_, v_a_347_, v_x_348_);
lean_dec(v_x_348_);
lean_dec_ref(v_a_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_00_u03b2_351_, lean_object* v_data_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4___redArg(v_data_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5(lean_object* v_00_u03b2_354_, lean_object* v_i_355_, lean_object* v_source_356_, lean_object* v_target_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5___redArg(v_i_355_, v_source_356_, v_target_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6___redArg(v_x_360_, v_x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addAssertExistsEntry___redArg(uint8_t v_isDecl_363_, lean_object* v_declName_364_, lean_object* v_mod_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_368_; lean_object* v_env_369_; lean_object* v_messages_370_; lean_object* v_scopes_371_; lean_object* v_usedQuotCtxts_372_; lean_object* v_nextMacroScope_373_; lean_object* v_maxRecDepth_374_; lean_object* v_ngen_375_; lean_object* v_auxDeclNGen_376_; lean_object* v_infoState_377_; lean_object* v_traceState_378_; lean_object* v_snapshotTasks_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_395_; 
v___x_368_ = lean_st_ref_take(v_a_366_);
v_env_369_ = lean_ctor_get(v___x_368_, 0);
v_messages_370_ = lean_ctor_get(v___x_368_, 1);
v_scopes_371_ = lean_ctor_get(v___x_368_, 2);
v_usedQuotCtxts_372_ = lean_ctor_get(v___x_368_, 3);
v_nextMacroScope_373_ = lean_ctor_get(v___x_368_, 4);
v_maxRecDepth_374_ = lean_ctor_get(v___x_368_, 5);
v_ngen_375_ = lean_ctor_get(v___x_368_, 6);
v_auxDeclNGen_376_ = lean_ctor_get(v___x_368_, 7);
v_infoState_377_ = lean_ctor_get(v___x_368_, 8);
v_traceState_378_ = lean_ctor_get(v___x_368_, 9);
v_snapshotTasks_379_ = lean_ctor_get(v___x_368_, 10);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_395_ == 0)
{
v___x_381_ = v___x_368_;
v_isShared_382_ = v_isSharedCheck_395_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snapshotTasks_379_);
lean_inc(v_traceState_378_);
lean_inc(v_infoState_377_);
lean_inc(v_auxDeclNGen_376_);
lean_inc(v_ngen_375_);
lean_inc(v_maxRecDepth_374_);
lean_inc(v_nextMacroScope_373_);
lean_inc(v_usedQuotCtxts_372_);
lean_inc(v_scopes_371_);
lean_inc(v_messages_370_);
lean_inc(v_env_369_);
lean_dec(v___x_368_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_395_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v_toEnvExtension_384_; lean_object* v_asyncMode_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_383_ = l_Lean_Elab_Command_assertExistsExt;
v_toEnvExtension_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_toEnvExtension_384_);
v_asyncMode_385_ = lean_ctor_get(v_toEnvExtension_384_, 2);
lean_inc(v_asyncMode_385_);
lean_dec_ref(v_toEnvExtension_384_);
v___x_386_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_386_, 0, v_declName_364_);
lean_ctor_set(v___x_386_, 1, v_mod_365_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*2, v_isDecl_363_);
v___x_387_ = lean_box(0);
v___x_388_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_383_, v_env_369_, v___x_386_, v_asyncMode_385_, v___x_387_);
lean_dec(v_asyncMode_385_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_388_);
v___x_390_ = v___x_381_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_messages_370_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_scopes_371_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_usedQuotCtxts_372_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_nextMacroScope_373_);
lean_ctor_set(v_reuseFailAlloc_394_, 5, v_maxRecDepth_374_);
lean_ctor_set(v_reuseFailAlloc_394_, 6, v_ngen_375_);
lean_ctor_set(v_reuseFailAlloc_394_, 7, v_auxDeclNGen_376_);
lean_ctor_set(v_reuseFailAlloc_394_, 8, v_infoState_377_);
lean_ctor_set(v_reuseFailAlloc_394_, 9, v_traceState_378_);
lean_ctor_set(v_reuseFailAlloc_394_, 10, v_snapshotTasks_379_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_st_ref_set(v_a_366_, v___x_390_);
v___x_392_ = lean_box(0);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addAssertExistsEntry___redArg___boxed(lean_object* v_isDecl_396_, lean_object* v_declName_397_, lean_object* v_mod_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_isDecl_boxed_401_; lean_object* v_res_402_; 
v_isDecl_boxed_401_ = lean_unbox(v_isDecl_396_);
v_res_402_ = l_Lean_Elab_Command_addAssertExistsEntry___redArg(v_isDecl_boxed_401_, v_declName_397_, v_mod_398_, v_a_399_);
lean_dec(v_a_399_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addAssertExistsEntry(uint8_t v_isDecl_403_, lean_object* v_declName_404_, lean_object* v_mod_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Elab_Command_addAssertExistsEntry___redArg(v_isDecl_403_, v_declName_404_, v_mod_405_, v_a_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addAssertExistsEntry___boxed(lean_object* v_isDecl_410_, lean_object* v_declName_411_, lean_object* v_mod_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
uint8_t v_isDecl_boxed_416_; lean_object* v_res_417_; 
v_isDecl_boxed_416_ = lean_unbox(v_isDecl_410_);
v_res_417_ = l_Lean_Elab_Command_addAssertExistsEntry(v_isDecl_boxed_416_, v_declName_411_, v_mod_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
return v_res_417_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0(uint8_t v___x_418_, lean_object* v_d_419_, lean_object* v_e_420_){
_start:
{
uint8_t v_isDecl_421_; lean_object* v_givenName_422_; uint8_t v_isDecl_423_; lean_object* v_givenName_424_; uint8_t v___y_426_; uint8_t v___x_430_; 
v_isDecl_421_ = lean_ctor_get_uint8(v_e_420_, sizeof(void*)*2);
v_givenName_422_ = lean_ctor_get(v_e_420_, 0);
lean_inc(v_givenName_422_);
lean_dec_ref(v_e_420_);
v_isDecl_423_ = lean_ctor_get_uint8(v_d_419_, sizeof(void*)*2);
v_givenName_424_ = lean_ctor_get(v_d_419_, 0);
lean_inc(v_givenName_424_);
lean_dec_ref(v_d_419_);
v___x_430_ = l_Bool_instDecidableLt(v_isDecl_421_, v_isDecl_423_);
if (v___x_430_ == 0)
{
if (v_isDecl_421_ == 0)
{
if (v_isDecl_423_ == 0)
{
v___y_426_ = v___x_418_;
goto v___jp_425_;
}
else
{
lean_dec(v_givenName_424_);
lean_dec(v_givenName_422_);
return v_isDecl_421_;
}
}
else
{
if (v_isDecl_423_ == 0)
{
lean_dec(v_givenName_424_);
lean_dec(v_givenName_422_);
return v_isDecl_423_;
}
else
{
v___y_426_ = v_isDecl_423_;
goto v___jp_425_;
}
}
}
else
{
lean_dec(v_givenName_424_);
lean_dec(v_givenName_422_);
return v___x_430_;
}
v___jp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_427_ = l_Lean_Name_toString(v_givenName_424_, v___y_426_);
v___x_428_ = l_Lean_Name_toString(v_givenName_422_, v___y_426_);
v___x_429_ = lean_string_dec_lt(v___x_427_, v___x_428_);
lean_dec_ref(v___x_428_);
lean_dec_ref(v___x_427_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0___boxed(lean_object* v___x_431_, lean_object* v_d_432_, lean_object* v_e_433_){
_start:
{
uint8_t v___x_481__boxed_434_; uint8_t v_res_435_; lean_object* v_r_436_; 
v___x_481__boxed_434_ = lean_unbox(v___x_431_);
v_res_435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0(v___x_481__boxed_434_, v_d_432_, v_e_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(lean_object* v_as_437_, lean_object* v_lo_438_, lean_object* v_hi_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_nat_dec_lt(v_lo_438_, v_hi_439_);
if (v___x_440_ == 0)
{
lean_dec(v_lo_438_);
return v_as_437_;
}
else
{
lean_object* v___x_441_; lean_object* v___f_442_; lean_object* v___x_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; uint8_t v___x_446_; 
v___x_441_ = lean_box(v___x_440_);
v___f_442_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_442_, 0, v___x_441_);
lean_inc(v_lo_438_);
v___x_443_ = l_Array_qpartition___redArg(v_as_437_, v___f_442_, v_lo_438_, v_hi_439_);
v_fst_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_fst_444_);
v_snd_445_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_snd_445_);
lean_dec_ref(v___x_443_);
v___x_446_ = lean_nat_dec_le(v_hi_439_, v_fst_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v_snd_445_, v_lo_438_, v_fst_444_);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_nat_add(v_fst_444_, v___x_448_);
lean_dec(v_fst_444_);
v_as_437_ = v___x_447_;
v_lo_438_ = v___x_449_;
goto _start;
}
else
{
lean_dec(v_fst_444_);
lean_dec(v_lo_438_);
return v_snd_445_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___boxed(lean_object* v_as_451_, lean_object* v_lo_452_, lean_object* v_hi_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v_as_451_, v_lo_452_, v_hi_453_);
lean_dec(v_hi_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Command_getSortedAssertExists_spec__1(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
return v_x_455_;
}
else
{
lean_object* v_key_457_; lean_object* v_tail_458_; lean_object* v___x_459_; 
v_key_457_ = lean_ctor_get(v_x_456_, 0);
lean_inc(v_key_457_);
v_tail_458_ = lean_ctor_get(v_x_456_, 2);
lean_inc(v_tail_458_);
lean_dec_ref(v_x_456_);
v___x_459_ = lean_array_push(v_x_455_, v_key_457_);
v_x_455_ = v___x_459_;
v_x_456_ = v_tail_458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2(lean_object* v_as_461_, size_t v_i_462_, size_t v_stop_463_, lean_object* v_b_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = lean_usize_dec_eq(v_i_462_, v_stop_463_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; size_t v___x_468_; size_t v___x_469_; 
v___x_466_ = lean_array_uget_borrowed(v_as_461_, v_i_462_);
lean_inc(v___x_466_);
v___x_467_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Command_getSortedAssertExists_spec__1(v_b_464_, v___x_466_);
v___x_468_ = ((size_t)1ULL);
v___x_469_ = lean_usize_add(v_i_462_, v___x_468_);
v_i_462_ = v___x_469_;
v_b_464_ = v___x_467_;
goto _start;
}
else
{
return v_b_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2___boxed(lean_object* v_as_471_, lean_object* v_i_472_, lean_object* v_stop_473_, lean_object* v_b_474_){
_start:
{
size_t v_i_boxed_475_; size_t v_stop_boxed_476_; lean_object* v_res_477_; 
v_i_boxed_475_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_stop_boxed_476_ = lean_unbox_usize(v_stop_473_);
lean_dec(v_stop_473_);
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2(v_as_471_, v_i_boxed_475_, v_stop_boxed_476_, v_b_474_);
lean_dec_ref(v_as_471_);
return v_res_477_;
}
}
static lean_object* _init_l_Lean_Elab_Command_getSortedAssertExists___closed__0(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((lean_object*)(l_Lean_Elab_Command_instHashableAssertExists___closed__0));
v___x_479_ = ((lean_object*)(l_Lean_Elab_Command_instBEqAssertExists___closed__0));
v___x_480_ = l_Std_HashSet_instInhabited(lean_box(0), v___x_479_, v___x_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getSortedAssertExists(lean_object* v_env_481_){
_start:
{
lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_491_; lean_object* v___x_498_; lean_object* v_toEnvExtension_499_; lean_object* v_asyncMode_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_size_504_; lean_object* v_buckets_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_498_ = l_Lean_Elab_Command_assertExistsExt;
v_toEnvExtension_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc_ref(v_toEnvExtension_499_);
v_asyncMode_500_ = lean_ctor_get(v_toEnvExtension_499_, 2);
lean_inc(v_asyncMode_500_);
lean_dec_ref(v_toEnvExtension_499_);
v___x_501_ = lean_obj_once(&l_Lean_Elab_Command_getSortedAssertExists___closed__0, &l_Lean_Elab_Command_getSortedAssertExists___closed__0_once, _init_l_Lean_Elab_Command_getSortedAssertExists___closed__0);
v___x_502_ = lean_box(0);
v___x_503_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_501_, v___x_498_, v_env_481_, v_asyncMode_500_, v___x_502_);
lean_dec(v_asyncMode_500_);
v_size_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_size_504_);
v_buckets_505_ = lean_ctor_get(v___x_503_, 1);
lean_inc_ref(v_buckets_505_);
lean_dec(v___x_503_);
v___x_506_ = lean_mk_empty_array_with_capacity(v_size_504_);
lean_dec(v_size_504_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_array_get_size(v_buckets_505_);
v___x_509_ = lean_nat_dec_lt(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_dec_ref(v_buckets_505_);
v___y_491_ = v___x_506_;
goto v___jp_490_;
}
else
{
uint8_t v___x_510_; 
v___x_510_ = lean_nat_dec_le(v___x_508_, v___x_508_);
if (v___x_510_ == 0)
{
if (v___x_509_ == 0)
{
lean_dec_ref(v_buckets_505_);
v___y_491_ = v___x_506_;
goto v___jp_490_;
}
else
{
size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = ((size_t)0ULL);
v___x_512_ = lean_usize_of_nat(v___x_508_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2(v_buckets_505_, v___x_511_, v___x_512_, v___x_506_);
lean_dec_ref(v_buckets_505_);
v___y_491_ = v___x_513_;
goto v___jp_490_;
}
}
else
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_514_ = ((size_t)0ULL);
v___x_515_ = lean_usize_of_nat(v___x_508_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2(v_buckets_505_, v___x_514_, v___x_515_, v___x_506_);
lean_dec_ref(v_buckets_505_);
v___y_491_ = v___x_516_;
goto v___jp_490_;
}
}
v___jp_482_:
{
uint8_t v___x_487_; 
lean_dec(v___y_483_);
v___x_487_ = lean_nat_dec_le(v___y_486_, v___y_484_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec(v___y_484_);
lean_inc(v___y_486_);
v___x_488_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v___y_485_, v___y_486_, v___y_486_);
lean_dec(v___y_486_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v___y_485_, v___y_486_, v___y_484_);
lean_dec(v___y_484_);
return v___x_489_;
}
}
v___jp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_492_ = lean_array_get_size(v___y_491_);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_nat_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_sub(v___x_492_, v___x_495_);
v___x_497_ = lean_nat_dec_le(v___x_493_, v___x_496_);
if (v___x_497_ == 0)
{
lean_inc(v___x_496_);
v___y_483_ = v___x_492_;
v___y_484_ = v___x_496_;
v___y_485_ = v___y_491_;
v___y_486_ = v___x_496_;
goto v___jp_482_;
}
else
{
v___y_483_ = v___x_492_;
v___y_484_ = v___x_496_;
v___y_485_ = v___y_491_;
v___y_486_ = v___x_493_;
goto v___jp_482_;
}
}
else
{
return v___y_491_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0(lean_object* v_n_517_, lean_object* v_as_518_, lean_object* v_lo_519_, lean_object* v_hi_520_, lean_object* v_w_521_, lean_object* v_hlo_522_, lean_object* v_hhi_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v_as_518_, v_lo_519_, v_hi_520_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___boxed(lean_object* v_n_525_, lean_object* v_as_526_, lean_object* v_lo_527_, lean_object* v_hi_528_, lean_object* v_w_529_, lean_object* v_hlo_530_, lean_object* v_hhi_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0(v_n_525_, v_as_526_, v_lo_527_, v_hi_528_, v_w_529_, v_hlo_530_, v_hhi_531_);
lean_dec(v_hi_528_);
lean_dec(v_n_525_);
return v_res_532_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__0));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__2));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0(lean_object* v_as_539_, size_t v_i_540_, size_t v_stop_541_, lean_object* v_b_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lean_usize_dec_eq(v_i_540_, v_stop_541_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; size_t v___x_551_; size_t v___x_552_; 
v___x_544_ = lean_array_uget_borrowed(v_as_539_, v_i_540_);
v___x_545_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1);
lean_inc(v___x_544_);
v___x_546_ = l_Lean_MessageData_ofName(v___x_544_);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v_b_542_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_add(v_i_540_, v___x_551_);
v_i_540_ = v___x_552_;
v_b_542_ = v___x_550_;
goto _start;
}
else
{
return v_b_542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___boxed(lean_object* v_as_554_, lean_object* v_i_555_, lean_object* v_stop_556_, lean_object* v_b_557_){
_start:
{
size_t v_i_boxed_558_; size_t v_stop_boxed_559_; lean_object* v_res_560_; 
v_i_boxed_558_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_stop_boxed_559_ = lean_unbox_usize(v_stop_556_);
lean_dec(v_stop_556_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0(v_as_554_, v_i_boxed_558_, v_stop_boxed_559_, v_b_557_);
lean_dec_ref(v_as_554_);
return v_res_560_;
}
}
static lean_object* _init_l_Lean_Elab_Command_importPathMessage___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lean_Elab_Command_importPathMessage___closed__0));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_importPathMessage(lean_object* v_env_564_, lean_object* v_idx_565_){
_start:
{
lean_object* v___y_567_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_modNames_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_570_ = lean_box(0);
v___x_571_ = l_Lean_Environment_header(v_env_564_);
v_modNames_572_ = l_Lean_EnvironmentHeader_moduleNames(v___x_571_);
v___x_573_ = lean_array_get(v___x_570_, v_modNames_572_, v_idx_565_);
lean_dec_ref(v_modNames_572_);
lean_inc(v___x_573_);
v___x_574_ = l_Lean_MessageData_ofName(v___x_573_);
v___x_575_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3);
v___x_576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = l_Lean_Environment_importPath(v_env_564_, v___x_573_);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_array_get_size(v___x_577_);
v___x_580_ = lean_nat_dec_lt(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec_ref(v___x_577_);
v___y_567_ = v___x_576_;
goto v___jp_566_;
}
else
{
uint8_t v___x_581_; 
v___x_581_ = lean_nat_dec_le(v___x_579_, v___x_579_);
if (v___x_581_ == 0)
{
if (v___x_580_ == 0)
{
lean_dec_ref(v___x_577_);
v___y_567_ = v___x_576_;
goto v___jp_566_;
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_579_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0(v___x_577_, v___x_582_, v___x_583_, v___x_576_);
lean_dec_ref(v___x_577_);
v___y_567_ = v___x_584_;
goto v___jp_566_;
}
}
else
{
size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((size_t)0ULL);
v___x_586_ = lean_usize_of_nat(v___x_579_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0(v___x_577_, v___x_585_, v___x_586_, v___x_576_);
lean_dec_ref(v___x_577_);
v___y_567_ = v___x_587_;
goto v___jp_566_;
}
}
v___jp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_obj_once(&l_Lean_Elab_Command_importPathMessage___closed__1, &l_Lean_Elab_Command_importPathMessage___closed__1_once, _init_l_Lean_Elab_Command_importPathMessage___closed__1);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___y_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_importPathMessage___boxed(lean_object* v_env_588_, lean_object* v_idx_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Elab_Command_importPathMessage(v_env_588_, v_idx_589_);
lean_dec(v_idx_589_);
lean_dec_ref(v_env_588_);
return v_res_590_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0(uint8_t v___y_592_, uint8_t v_suppressElabErrors_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 1)
{
lean_object* v_pre_595_; 
v_pre_595_ = lean_ctor_get(v_x_594_, 0);
if (lean_obj_tag(v_pre_595_) == 0)
{
lean_object* v_str_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_str_596_ = lean_ctor_get(v_x_594_, 1);
v___x_597_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___closed__0));
v___x_598_ = lean_string_dec_eq(v_str_596_, v___x_597_);
if (v___x_598_ == 0)
{
return v___y_592_;
}
else
{
return v_suppressElabErrors_593_;
}
}
else
{
return v___y_592_;
}
}
else
{
return v___y_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___boxed(lean_object* v___y_599_, lean_object* v_suppressElabErrors_600_, lean_object* v_x_601_){
_start:
{
uint8_t v___y_6400__boxed_602_; uint8_t v_suppressElabErrors_boxed_603_; uint8_t v_res_604_; lean_object* v_r_605_; 
v___y_6400__boxed_602_ = lean_unbox(v___y_599_);
v_suppressElabErrors_boxed_603_ = lean_unbox(v_suppressElabErrors_600_);
v_res_604_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0(v___y_6400__boxed_602_, v_suppressElabErrors_boxed_603_, v_x_601_);
lean_dec(v_x_601_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6(lean_object* v_opts_606_, lean_object* v_opt_607_){
_start:
{
lean_object* v_name_608_; lean_object* v_defValue_609_; lean_object* v_map_610_; lean_object* v___x_611_; 
v_name_608_ = lean_ctor_get(v_opt_607_, 0);
v_defValue_609_ = lean_ctor_get(v_opt_607_, 1);
v_map_610_ = lean_ctor_get(v_opts_606_, 0);
v___x_611_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_610_, v_name_608_);
if (lean_obj_tag(v___x_611_) == 0)
{
uint8_t v___x_612_; 
v___x_612_ = lean_unbox(v_defValue_609_);
return v___x_612_;
}
else
{
lean_object* v_val_613_; 
v_val_613_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_val_613_);
lean_dec_ref(v___x_611_);
if (lean_obj_tag(v_val_613_) == 1)
{
uint8_t v_v_614_; 
v_v_614_ = lean_ctor_get_uint8(v_val_613_, 0);
lean_dec_ref(v_val_613_);
return v_v_614_;
}
else
{
uint8_t v___x_615_; 
lean_dec(v_val_613_);
v___x_615_ = lean_unbox(v_defValue_609_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6___boxed(lean_object* v_opts_616_, lean_object* v_opt_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6(v_opts_616_, v_opt_617_);
lean_dec_ref(v_opt_617_);
lean_dec_ref(v_opts_616_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_620_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
lean_ctor_set(v___x_625_, 2, v___x_624_);
lean_ctor_set(v___x_625_, 3, v___x_623_);
lean_ctor_set(v___x_625_, 4, v___x_623_);
lean_ctor_set(v___x_625_, 5, v___x_623_);
lean_ctor_set(v___x_625_, 6, v___x_623_);
lean_ctor_set(v___x_625_, 7, v___x_623_);
lean_ctor_set(v___x_625_, 8, v___x_623_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(32u);
v___x_627_ = lean_mk_empty_array_with_capacity(v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_629_ = ((size_t)5ULL);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_unsigned_to_nat(32u);
v___x_632_ = lean_mk_empty_array_with_capacity(v___x_631_);
v___x_633_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3);
v___x_634_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
lean_ctor_set(v___x_634_, 2, v___x_630_);
lean_ctor_set(v___x_634_, 3, v___x_630_);
lean_ctor_set_usize(v___x_634_, 4, v___x_629_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_box(1);
v___x_636_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4);
v___x_637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
lean_ctor_set(v___x_638_, 2, v___x_635_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(lean_object* v_msgData_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; lean_object* v_env_643_; lean_object* v___x_644_; lean_object* v_scopes_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_opts_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_642_ = lean_st_ref_get(v___y_640_);
v_env_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc_ref(v_env_643_);
lean_dec(v___x_642_);
v___x_644_ = lean_st_ref_get(v___y_640_);
v_scopes_645_ = lean_ctor_get(v___x_644_, 2);
lean_inc(v_scopes_645_);
lean_dec(v___x_644_);
v___x_646_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_647_ = l_List_head_x21___redArg(v___x_646_, v_scopes_645_);
lean_dec(v_scopes_645_);
v_opts_648_ = lean_ctor_get(v___x_647_, 1);
lean_inc_ref(v_opts_648_);
lean_dec(v___x_647_);
v___x_649_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2);
v___x_650_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5);
v___x_651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_651_, 0, v_env_643_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_650_);
lean_ctor_set(v___x_651_, 3, v_opts_648_);
v___x_652_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_msgData_639_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(v_msgData_654_, v___y_655_);
lean_dec(v___y_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(lean_object* v_ref_659_, lean_object* v_msgData_660_, uint8_t v_severity_661_, uint8_t v_isSilent_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___y_667_; uint8_t v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; uint8_t v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; uint8_t v___y_730_; uint8_t v___y_731_; lean_object* v___y_732_; uint8_t v___y_733_; lean_object* v___y_734_; uint8_t v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; uint8_t v___y_761_; lean_object* v___y_762_; uint8_t v___y_766_; uint8_t v___y_767_; uint8_t v___y_768_; uint8_t v___x_783_; uint8_t v___y_785_; uint8_t v___y_786_; uint8_t v___y_787_; uint8_t v___y_789_; uint8_t v___x_801_; 
v___x_783_ = 2;
v___x_801_ = l_Lean_instBEqMessageSeverity_beq(v_severity_661_, v___x_783_);
if (v___x_801_ == 0)
{
v___y_789_ = v___x_801_;
goto v___jp_788_;
}
else
{
uint8_t v___x_802_; 
lean_inc_ref(v_msgData_660_);
v___x_802_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_660_);
v___y_789_ = v___x_802_;
goto v___jp_788_;
}
v___jp_666_:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Elab_Command_getScope___redArg(v___y_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref(v___x_675_);
v___x_677_ = l_Lean_Elab_Command_getScope___redArg(v___y_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_712_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_712_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_712_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_712_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v_currNamespace_683_; lean_object* v_openDecls_684_; lean_object* v_env_685_; lean_object* v_messages_686_; lean_object* v_scopes_687_; lean_object* v_usedQuotCtxts_688_; lean_object* v_nextMacroScope_689_; lean_object* v_maxRecDepth_690_; lean_object* v_ngen_691_; lean_object* v_auxDeclNGen_692_; lean_object* v_infoState_693_; lean_object* v_traceState_694_; lean_object* v_snapshotTasks_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_711_; 
v___x_682_ = lean_st_ref_take(v___y_674_);
v_currNamespace_683_ = lean_ctor_get(v_a_676_, 2);
lean_inc(v_currNamespace_683_);
lean_dec(v_a_676_);
v_openDecls_684_ = lean_ctor_get(v_a_678_, 3);
lean_inc(v_openDecls_684_);
lean_dec(v_a_678_);
v_env_685_ = lean_ctor_get(v___x_682_, 0);
v_messages_686_ = lean_ctor_get(v___x_682_, 1);
v_scopes_687_ = lean_ctor_get(v___x_682_, 2);
v_usedQuotCtxts_688_ = lean_ctor_get(v___x_682_, 3);
v_nextMacroScope_689_ = lean_ctor_get(v___x_682_, 4);
v_maxRecDepth_690_ = lean_ctor_get(v___x_682_, 5);
v_ngen_691_ = lean_ctor_get(v___x_682_, 6);
v_auxDeclNGen_692_ = lean_ctor_get(v___x_682_, 7);
v_infoState_693_ = lean_ctor_get(v___x_682_, 8);
v_traceState_694_ = lean_ctor_get(v___x_682_, 9);
v_snapshotTasks_695_ = lean_ctor_get(v___x_682_, 10);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_711_ == 0)
{
v___x_697_ = v___x_682_;
v_isShared_698_ = v_isSharedCheck_711_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snapshotTasks_695_);
lean_inc(v_traceState_694_);
lean_inc(v_infoState_693_);
lean_inc(v_auxDeclNGen_692_);
lean_inc(v_ngen_691_);
lean_inc(v_maxRecDepth_690_);
lean_inc(v_nextMacroScope_689_);
lean_inc(v_usedQuotCtxts_688_);
lean_inc(v_scopes_687_);
lean_inc(v_messages_686_);
lean_inc(v_env_685_);
lean_dec(v___x_682_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_711_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v_currNamespace_683_);
lean_ctor_set(v___x_699_, 1, v_openDecls_684_);
v___x_700_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___y_669_);
v___x_701_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_701_, 0, v___y_673_);
lean_ctor_set(v___x_701_, 1, v___y_672_);
lean_ctor_set(v___x_701_, 2, v___y_670_);
lean_ctor_set(v___x_701_, 3, v___y_667_);
lean_ctor_set(v___x_701_, 4, v___x_700_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*5, v___y_671_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*5 + 1, v___y_668_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*5 + 2, v_isSilent_662_);
v___x_702_ = l_Lean_MessageLog_add(v___x_701_, v_messages_686_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_702_);
v___x_704_ = v___x_697_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_env_685_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_scopes_687_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_usedQuotCtxts_688_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_nextMacroScope_689_);
lean_ctor_set(v_reuseFailAlloc_710_, 5, v_maxRecDepth_690_);
lean_ctor_set(v_reuseFailAlloc_710_, 6, v_ngen_691_);
lean_ctor_set(v_reuseFailAlloc_710_, 7, v_auxDeclNGen_692_);
lean_ctor_set(v_reuseFailAlloc_710_, 8, v_infoState_693_);
lean_ctor_set(v_reuseFailAlloc_710_, 9, v_traceState_694_);
lean_ctor_set(v_reuseFailAlloc_710_, 10, v_snapshotTasks_695_);
v___x_704_ = v_reuseFailAlloc_710_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_705_ = lean_st_ref_set(v___y_674_, v___x_704_);
v___x_706_ = lean_box(0);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_706_);
v___x_708_ = v___x_680_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_a_676_);
lean_dec_ref(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v___y_667_);
v_a_713_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_677_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_677_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v___y_667_);
v_a_721_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_675_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_675_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
v___jp_729_:
{
lean_object* v_fileName_735_; lean_object* v_fileMap_736_; uint8_t v_suppressElabErrors_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_756_; 
v_fileName_735_ = lean_ctor_get(v___y_663_, 0);
lean_inc_ref(v_fileName_735_);
v_fileMap_736_ = lean_ctor_get(v___y_663_, 1);
lean_inc_ref(v_fileMap_736_);
v_suppressElabErrors_737_ = lean_ctor_get_uint8(v___y_663_, sizeof(void*)*10);
lean_dec_ref(v___y_663_);
v___x_738_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_660_);
v___x_739_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(v___x_738_, v___y_664_);
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_756_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_756_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_756_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_inc_ref(v_fileMap_736_);
v___x_744_ = l_Lean_FileMap_toPosition(v_fileMap_736_, v___y_732_);
lean_dec(v___y_732_);
v___x_745_ = l_Lean_FileMap_toPosition(v_fileMap_736_, v___y_734_);
lean_dec(v___y_734_);
v___x_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0));
if (v_suppressElabErrors_737_ == 0)
{
lean_del_object(v___x_742_);
v___y_667_ = v___x_747_;
v___y_668_ = v___y_731_;
v___y_669_ = v_a_740_;
v___y_670_ = v___x_746_;
v___y_671_ = v___y_733_;
v___y_672_ = v___x_744_;
v___y_673_ = v_fileName_735_;
v___y_674_ = v___y_664_;
goto v___jp_666_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___f_750_; uint8_t v___x_751_; 
v___x_748_ = lean_box(v___y_730_);
v___x_749_ = lean_box(v_suppressElabErrors_737_);
v___f_750_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_750_, 0, v___x_748_);
lean_closure_set(v___f_750_, 1, v___x_749_);
lean_inc(v_a_740_);
v___x_751_ = l_Lean_MessageData_hasTag(v___f_750_, v_a_740_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec_ref(v___x_746_);
lean_dec_ref(v___x_744_);
lean_dec(v_a_740_);
lean_dec_ref(v_fileName_735_);
v___x_752_ = lean_box(0);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_752_);
v___x_754_ = v___x_742_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_del_object(v___x_742_);
v___y_667_ = v___x_747_;
v___y_668_ = v___y_731_;
v___y_669_ = v_a_740_;
v___y_670_ = v___x_746_;
v___y_671_ = v___y_733_;
v___y_672_ = v___x_744_;
v___y_673_ = v_fileName_735_;
v___y_674_ = v___y_664_;
goto v___jp_666_;
}
}
}
}
v___jp_757_:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Syntax_getTailPos_x3f(v___y_760_, v___y_761_);
lean_dec(v___y_760_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_inc(v___y_762_);
v___y_730_ = v___y_758_;
v___y_731_ = v___y_759_;
v___y_732_ = v___y_762_;
v___y_733_ = v___y_761_;
v___y_734_ = v___y_762_;
goto v___jp_729_;
}
else
{
lean_object* v_val_764_; 
v_val_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_val_764_);
lean_dec_ref(v___x_763_);
v___y_730_ = v___y_758_;
v___y_731_ = v___y_759_;
v___y_732_ = v___y_762_;
v___y_733_ = v___y_761_;
v___y_734_ = v_val_764_;
goto v___jp_729_;
}
}
v___jp_765_:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Elab_Command_getRef___redArg(v___y_663_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v_ref_771_; lean_object* v___x_772_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
v_ref_771_ = l_Lean_replaceRef(v_ref_659_, v_a_770_);
lean_dec(v_a_770_);
v___x_772_ = l_Lean_Syntax_getPos_x3f(v_ref_771_, v___y_767_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_773_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___y_758_ = v___y_766_;
v___y_759_ = v___y_768_;
v___y_760_ = v_ref_771_;
v___y_761_ = v___y_767_;
v___y_762_ = v___x_773_;
goto v___jp_757_;
}
else
{
lean_object* v_val_774_; 
v_val_774_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_val_774_);
lean_dec_ref(v___x_772_);
v___y_758_ = v___y_766_;
v___y_759_ = v___y_768_;
v___y_760_ = v_ref_771_;
v___y_761_ = v___y_767_;
v___y_762_ = v_val_774_;
goto v___jp_757_;
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec_ref(v___y_663_);
lean_dec_ref(v_msgData_660_);
v_a_775_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_769_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_769_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
v___jp_784_:
{
if (v___y_787_ == 0)
{
v___y_766_ = v___y_785_;
v___y_767_ = v___y_786_;
v___y_768_ = v_severity_661_;
goto v___jp_765_;
}
else
{
v___y_766_ = v___y_785_;
v___y_767_ = v___y_786_;
v___y_768_ = v___x_783_;
goto v___jp_765_;
}
}
v___jp_788_:
{
if (v___y_789_ == 0)
{
lean_object* v___x_790_; lean_object* v_scopes_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v_opts_794_; uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_790_ = lean_st_ref_get(v___y_664_);
v_scopes_791_ = lean_ctor_get(v___x_790_, 2);
lean_inc(v_scopes_791_);
lean_dec(v___x_790_);
v___x_792_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_793_ = l_List_head_x21___redArg(v___x_792_, v_scopes_791_);
lean_dec(v_scopes_791_);
v_opts_794_ = lean_ctor_get(v___x_793_, 1);
lean_inc_ref(v_opts_794_);
lean_dec(v___x_793_);
v___x_795_ = 1;
v___x_796_ = l_Lean_instBEqMessageSeverity_beq(v_severity_661_, v___x_795_);
if (v___x_796_ == 0)
{
lean_dec_ref(v_opts_794_);
v___y_785_ = v___y_789_;
v___y_786_ = v___y_789_;
v___y_787_ = v___x_796_;
goto v___jp_784_;
}
else
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = l_Lean_warningAsError;
v___x_798_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6(v_opts_794_, v___x_797_);
lean_dec_ref(v_opts_794_);
v___y_785_ = v___y_789_;
v___y_786_ = v___y_789_;
v___y_787_ = v___x_798_;
goto v___jp_784_;
}
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v___y_663_);
lean_dec_ref(v_msgData_660_);
v___x_799_ = lean_box(0);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___boxed(lean_object* v_ref_803_, lean_object* v_msgData_804_, lean_object* v_severity_805_, lean_object* v_isSilent_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
uint8_t v_severity_boxed_810_; uint8_t v_isSilent_boxed_811_; lean_object* v_res_812_; 
v_severity_boxed_810_ = lean_unbox(v_severity_805_);
v_isSilent_boxed_811_ = lean_unbox(v_isSilent_806_);
v_res_812_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_ref_803_, v_msgData_804_, v_severity_boxed_810_, v_isSilent_boxed_811_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec(v_ref_803_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(lean_object* v_ref_813_, lean_object* v_msgData_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; 
v___x_818_ = 0;
v___x_819_ = 0;
v___x_820_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_ref_813_, v_msgData_814_, v___x_818_, v___x_819_, v___y_815_, v___y_816_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1___boxed(lean_object* v_ref_821_, lean_object* v_msgData_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(v_ref_821_, v_msgData_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec(v_ref_821_);
return v_res_826_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_box(1);
v___x_828_ = l_Lean_MessageData_ofFormat(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__2));
v___x_833_ = l_Lean_MessageData_ofFormat(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_835_) == 0)
{
return v_x_834_;
}
else
{
lean_object* v_head_836_; lean_object* v_tail_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_859_; 
v_head_836_ = lean_ctor_get(v_x_835_, 0);
v_tail_837_ = lean_ctor_get(v_x_835_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_x_835_);
if (v_isSharedCheck_859_ == 0)
{
v___x_839_ = v_x_835_;
v_isShared_840_ = v_isSharedCheck_859_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_tail_837_);
lean_inc(v_head_836_);
lean_dec(v_x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_859_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_before_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_857_; 
v_before_841_ = lean_ctor_get(v_head_836_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_head_836_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; 
v_unused_858_ = lean_ctor_get(v_head_836_, 1);
lean_dec(v_unused_858_);
v___x_843_ = v_head_836_;
v_isShared_844_ = v_isSharedCheck_857_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_before_841_);
lean_dec(v_head_836_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_857_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 7);
lean_ctor_set(v___x_843_, 1, v___x_845_);
lean_ctor_set(v___x_843_, 0, v_x_834_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_x_834_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_845_);
v___x_847_ = v_reuseFailAlloc_856_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3);
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 7);
lean_ctor_set(v___x_839_, 1, v___x_848_);
lean_ctor_set(v___x_839_, 0, v___x_847_);
v___x_850_ = v___x_839_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_855_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = l_Lean_MessageData_ofSyntax(v_before_841_);
v___x_852_ = l_Lean_indentD(v___x_851_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_850_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v_x_834_ = v___x_853_;
v_x_835_ = v_tail_837_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__1));
v___x_864_ = l_Lean_MessageData_ofFormat(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg(lean_object* v_msgData_865_, lean_object* v_macroStack_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v_scopes_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v_opts_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_869_ = lean_st_ref_get(v___y_867_);
v_scopes_870_ = lean_ctor_get(v___x_869_, 2);
lean_inc(v_scopes_870_);
lean_dec(v___x_869_);
v___x_871_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_872_ = l_List_head_x21___redArg(v___x_871_, v_scopes_870_);
lean_dec(v_scopes_870_);
v_opts_873_ = lean_ctor_get(v___x_872_, 1);
lean_inc_ref(v_opts_873_);
lean_dec(v___x_872_);
v___x_874_ = l_Lean_Elab_pp_macroStack;
v___x_875_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6(v_opts_873_, v___x_874_);
lean_dec_ref(v_opts_873_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec(v_macroStack_866_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_msgData_865_);
return v___x_876_;
}
else
{
if (lean_obj_tag(v_macroStack_866_) == 0)
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v_msgData_865_);
return v___x_877_;
}
else
{
lean_object* v_head_878_; lean_object* v_after_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_894_; 
v_head_878_ = lean_ctor_get(v_macroStack_866_, 0);
lean_inc(v_head_878_);
v_after_879_ = lean_ctor_get(v_head_878_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_head_878_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_head_878_, 0);
lean_dec(v_unused_895_);
v___x_881_ = v_head_878_;
v_isShared_882_ = v_isSharedCheck_894_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_after_879_);
lean_dec(v_head_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_894_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0);
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 7);
lean_ctor_set(v___x_881_, 1, v___x_883_);
lean_ctor_set(v___x_881_, 0, v_msgData_865_);
v___x_885_ = v___x_881_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_msgData_865_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_883_);
v___x_885_ = v_reuseFailAlloc_893_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_msgData_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_886_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_MessageData_ofSyntax(v_after_879_);
v___x_889_ = l_Lean_indentD(v___x_888_);
v_msgData_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_890_, 0, v___x_887_);
lean_ctor_set(v_msgData_890_, 1, v___x_889_);
v___x_891_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14(v_msgData_890_, v_macroStack_866_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___boxed(lean_object* v_msgData_896_, lean_object* v_macroStack_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg(v_msgData_896_, v_macroStack_897_, v___y_898_);
lean_dec(v___y_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg(lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Elab_Command_getRef___redArg(v___y_902_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v_macroStack_907_; lean_object* v___x_908_; lean_object* v_a_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_920_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref(v___x_905_);
v_macroStack_907_ = lean_ctor_get(v___y_902_, 4);
lean_inc(v_macroStack_907_);
lean_dec_ref(v___y_902_);
v___x_908_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(v_msg_901_, v___y_903_);
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref(v___x_908_);
lean_inc(v_macroStack_907_);
v___x_910_ = l_Lean_Elab_getBetterRef(v_a_906_, v_macroStack_907_);
lean_dec(v_a_906_);
v___x_911_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg(v_a_909_, v_macroStack_907_, v___y_903_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_920_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_910_);
lean_ctor_set(v___x_916_, 1, v_a_912_);
if (v_isShared_915_ == 0)
{
lean_ctor_set_tag(v___x_914_, 1);
lean_ctor_set(v___x_914_, 0, v___x_916_);
v___x_918_ = v___x_914_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v___y_902_);
lean_dec_ref(v_msg_901_);
v_a_921_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_905_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_905_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_msg_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg(v_msg_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg(lean_object* v_ref_934_, lean_object* v_msg_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Elab_Command_getRef___redArg(v___y_936_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_fileName_941_; lean_object* v_fileMap_942_; lean_object* v_currRecDepth_943_; lean_object* v_cmdPos_944_; lean_object* v_macroStack_945_; lean_object* v_quotContext_x3f_946_; lean_object* v_currMacroScope_947_; lean_object* v_snap_x3f_948_; lean_object* v_cancelTk_x3f_949_; uint8_t v_suppressElabErrors_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_959_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref(v___x_939_);
v_fileName_941_ = lean_ctor_get(v___y_936_, 0);
v_fileMap_942_ = lean_ctor_get(v___y_936_, 1);
v_currRecDepth_943_ = lean_ctor_get(v___y_936_, 2);
v_cmdPos_944_ = lean_ctor_get(v___y_936_, 3);
v_macroStack_945_ = lean_ctor_get(v___y_936_, 4);
v_quotContext_x3f_946_ = lean_ctor_get(v___y_936_, 5);
v_currMacroScope_947_ = lean_ctor_get(v___y_936_, 6);
v_snap_x3f_948_ = lean_ctor_get(v___y_936_, 8);
v_cancelTk_x3f_949_ = lean_ctor_get(v___y_936_, 9);
v_suppressElabErrors_950_ = lean_ctor_get_uint8(v___y_936_, sizeof(void*)*10);
v_isSharedCheck_959_ = !lean_is_exclusive(v___y_936_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v___y_936_, 7);
lean_dec(v_unused_960_);
v___x_952_ = v___y_936_;
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_cancelTk_x3f_949_);
lean_inc(v_snap_x3f_948_);
lean_inc(v_currMacroScope_947_);
lean_inc(v_quotContext_x3f_946_);
lean_inc(v_macroStack_945_);
lean_inc(v_cmdPos_944_);
lean_inc(v_currRecDepth_943_);
lean_inc(v_fileMap_942_);
lean_inc(v_fileName_941_);
lean_dec(v___y_936_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_ref_954_; lean_object* v___x_956_; 
v_ref_954_ = l_Lean_replaceRef(v_ref_934_, v_a_940_);
lean_dec(v_a_940_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 7, v_ref_954_);
v___x_956_ = v___x_952_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_fileName_941_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_fileMap_942_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_currRecDepth_943_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_cmdPos_944_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_macroStack_945_);
lean_ctor_set(v_reuseFailAlloc_958_, 5, v_quotContext_x3f_946_);
lean_ctor_set(v_reuseFailAlloc_958_, 6, v_currMacroScope_947_);
lean_ctor_set(v_reuseFailAlloc_958_, 7, v_ref_954_);
lean_ctor_set(v_reuseFailAlloc_958_, 8, v_snap_x3f_948_);
lean_ctor_set(v_reuseFailAlloc_958_, 9, v_cancelTk_x3f_949_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*10, v_suppressElabErrors_950_);
v___x_956_ = v_reuseFailAlloc_958_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg(v_msg_935_, v___x_956_, v___y_937_);
return v___x_957_;
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v___y_936_);
lean_dec_ref(v_msg_935_);
v_a_961_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_939_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_939_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_ref_969_, lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg(v_ref_969_, v_msg_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec(v_ref_969_);
return v_res_974_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__0));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__2));
v___x_980_ = l_Lean_stringToMessageData(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__4));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_986_ = l_Lean_stringToMessageData(v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_989_ = l_Lean_stringToMessageData(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_996_, lean_object* v_declHint_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; lean_object* v_env_1001_; uint8_t v___x_1002_; 
v___x_1000_ = lean_st_ref_get(v___y_998_);
v_env_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc_ref(v_env_1001_);
lean_dec(v___x_1000_);
v___x_1002_ = l_Lean_Name_isAnonymous(v_declHint_997_);
if (v___x_1002_ == 0)
{
uint8_t v_isExporting_1003_; 
v_isExporting_1003_ = lean_ctor_get_uint8(v_env_1001_, sizeof(void*)*8);
if (v_isExporting_1003_ == 0)
{
lean_object* v___x_1004_; 
lean_dec_ref(v_env_1001_);
lean_dec(v_declHint_997_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_msg_996_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
lean_inc_ref(v_env_1001_);
v___x_1005_ = l_Lean_Environment_setExporting(v_env_1001_, v___x_1002_);
lean_inc(v_declHint_997_);
lean_inc_ref(v___x_1005_);
v___x_1006_ = l_Lean_Environment_contains(v___x_1005_, v_declHint_997_, v_isExporting_1003_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_env_1001_);
lean_dec(v_declHint_997_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_msg_996_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_c_1013_; lean_object* v___x_1014_; 
v___x_1008_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2);
v___x_1009_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5);
v___x_1010_ = l_Lean_Options_empty;
v___x_1011_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1005_);
lean_ctor_set(v___x_1011_, 1, v___x_1008_);
lean_ctor_set(v___x_1011_, 2, v___x_1009_);
lean_ctor_set(v___x_1011_, 3, v___x_1010_);
lean_inc(v_declHint_997_);
v___x_1012_ = l_Lean_MessageData_ofConstName(v_declHint_997_, v___x_1002_);
v_c_1013_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1013_, 0, v___x_1011_);
lean_ctor_set(v_c_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1001_, v_declHint_997_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec_ref(v_env_1001_);
lean_dec(v_declHint_997_);
v___x_1015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_c_1013_);
v___x_1017_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = l_Lean_MessageData_note(v___x_1018_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v_msg_996_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
else
{
lean_object* v_val_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1057_; 
v_val_1022_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1024_ = v___x_1014_;
v_isShared_1025_ = v_isSharedCheck_1057_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_val_1022_);
lean_dec(v___x_1014_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1057_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_mod_1029_; uint8_t v___x_1030_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = l_Lean_Environment_header(v_env_1001_);
lean_dec_ref(v_env_1001_);
v___x_1028_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1027_);
v_mod_1029_ = lean_array_get(v___x_1026_, v___x_1028_, v_val_1022_);
lean_dec(v_val_1022_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = l_Lean_isPrivateName(v_declHint_997_);
lean_dec(v_declHint_997_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1031_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v_c_1013_);
v___x_1033_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = l_Lean_MessageData_ofName(v_mod_1029_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_MessageData_note(v___x_1038_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_msg_996_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1040_);
v___x_1042_ = v___x_1024_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_c_1013_);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_MessageData_ofName(v_mod_1029_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_MessageData_note(v___x_1051_);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_msg_996_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1053_);
v___x_1055_ = v___x_1024_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1058_; 
lean_dec_ref(v_env_1001_);
lean_dec(v_declHint_997_);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_msg_996_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_1059_, lean_object* v_declHint_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg(v_msg_1059_, v_declHint_1060_, v___y_1061_);
lean_dec(v___y_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9(lean_object* v_msg_1064_, lean_object* v_declHint_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1079_; 
v___x_1069_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg(v_msg_1064_, v_declHint_1065_, v___y_1067_);
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1074_ = l_Lean_unknownIdentifierMessageTag;
v___x_1075_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1075_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9___boxed(lean_object* v_msg_1080_, lean_object* v_declHint_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9(v_msg_1080_, v_declHint_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_ref_1086_, lean_object* v_msg_1087_, lean_object* v_declHint_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v_a_1093_; lean_object* v___x_1094_; 
v___x_1092_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9(v_msg_1087_, v_declHint_1088_, v___y_1089_, v___y_1090_);
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg(v_ref_1086_, v_a_1093_, v___y_1089_, v___y_1090_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_ref_1095_, lean_object* v_msg_1096_, lean_object* v_declHint_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_1095_, v_msg_1096_, v_declHint_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec(v_ref_1095_);
return v_res_1101_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__2));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_1108_, lean_object* v_constName_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1113_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1114_ = 0;
lean_inc(v_constName_1109_);
v___x_1115_ = l_Lean_MessageData_ofConstName(v_constName_1109_, v___x_1114_);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1113_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_1108_, v___x_1118_, v_constName_1109_, v___y_1110_, v___y_1111_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_1120_, lean_object* v_constName_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1120_, v_constName_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec(v_ref_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Elab_Command_getRef___redArg(v___y_1127_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg(v_a_1131_, v_constName_1126_, v___y_1127_, v___y_1128_);
lean_dec(v_a_1131_);
return v___x_1132_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v___y_1127_);
lean_dec(v_constName_1126_);
v_a_1133_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1130_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1130_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg(v_constName_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0(lean_object* v_constName_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v_env_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = lean_st_ref_get(v___y_1148_);
v_env_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc_ref(v_env_1151_);
lean_dec(v___x_1150_);
v___x_1152_ = 0;
lean_inc(v_constName_1146_);
v___x_1153_ = l_Lean_Environment_findConstVal_x3f(v_env_1151_, v_constName_1146_, v___x_1152_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg(v_constName_1146_, v___y_1147_, v___y_1148_);
return v___x_1154_;
}
else
{
lean_object* v_val_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v___y_1147_);
lean_dec(v_constName_1146_);
v_val_1155_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1153_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_val_1155_);
lean_dec(v___x_1153_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set_tag(v___x_1157_, 0);
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_val_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0___boxed(lean_object* v_constName_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0(v_constName_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__1(lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
if (lean_obj_tag(v_a_1168_) == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = l_List_reverse___redArg(v_a_1169_);
return v___x_1170_;
}
else
{
lean_object* v_head_1171_; lean_object* v_tail_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1181_; 
v_head_1171_ = lean_ctor_get(v_a_1168_, 0);
v_tail_1172_ = lean_ctor_get(v_a_1168_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_a_1168_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1174_ = v_a_1168_;
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_tail_1172_);
lean_inc(v_head_1171_);
lean_dec(v_a_1168_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = l_Lean_mkLevelParam(v_head_1171_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_a_1169_);
lean_ctor_set(v___x_1174_, 0, v___x_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_a_1169_);
v___x_1178_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
v_a_1168_ = v_tail_1172_;
v_a_1169_ = v___x_1178_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0(lean_object* v_constName_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
lean_inc(v_constName_1182_);
v___x_1186_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0(v_constName_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1198_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1198_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1198_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_levelParams_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v_levelParams_1191_ = lean_ctor_get(v_a_1187_, 1);
lean_inc(v_levelParams_1191_);
lean_dec(v_a_1187_);
v___x_1192_ = lean_box(0);
v___x_1193_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__1(v_levelParams_1191_, v___x_1192_);
v___x_1194_ = l_Lean_mkConst(v_constName_1182_, v___x_1193_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1194_);
v___x_1196_ = v___x_1189_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_constName_1182_);
v_a_1199_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1186_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1186_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0___boxed(lean_object* v_constName_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0(v_constName_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
return v_res_1211_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabImportPath___closed__1(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l_Lean_Elab_Command_elabImportPath___closed__0));
v___x_1214_ = l_Lean_stringToMessageData(v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabImportPath___closed__3(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = ((lean_object*)(l_Lean_Elab_Command_elabImportPath___closed__2));
v___x_1217_ = l_Lean_stringToMessageData(v___x_1216_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabImportPath___closed__5(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Elab_Command_elabImportPath___closed__4));
v___x_1220_ = l_Lean_stringToMessageData(v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabImportPath___closed__7(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Command_elabImportPath___closed__6));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabImportPath___closed__9(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l_Lean_Elab_Command_elabImportPath___closed__8));
v___x_1226_ = l_Lean_stringToMessageData(v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath(lean_object* v_stx_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_n_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1231_ = lean_st_ref_get(v_a_1229_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v_n_1233_ = l_Lean_Syntax_getArg(v_stx_1227_, v___x_1232_);
v___x_1234_ = lean_box(0);
lean_inc(v_n_1233_);
v___x_1235_ = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed), 5, 2);
lean_closure_set(v___x_1235_, 0, v_n_1233_);
lean_closure_set(v___x_1235_, 1, v___x_1234_);
lean_inc_ref(v_a_1228_);
v___x_1236_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1235_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref(v___x_1236_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1237_);
v___x_1238_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0(v_a_1237_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_env_1240_; lean_object* v___x_1241_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
v_env_1240_ = lean_ctor_get(v___x_1231_, 0);
lean_inc_ref(v_env_1240_);
lean_dec(v___x_1231_);
v___x_1241_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1240_, v_a_1237_);
lean_dec(v_a_1237_);
if (lean_obj_tag(v___x_1241_) == 1)
{
lean_object* v_val_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_val_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1242_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = lean_obj_once(&l_Lean_Elab_Command_elabImportPath___closed__1, &l_Lean_Elab_Command_elabImportPath___closed__1_once, _init_l_Lean_Elab_Command_elabImportPath___closed__1);
v___x_1244_ = l_Lean_MessageData_ofExpr(v_a_1239_);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = lean_obj_once(&l_Lean_Elab_Command_elabImportPath___closed__3, &l_Lean_Elab_Command_elabImportPath___closed__3_once, _init_l_Lean_Elab_Command_elabImportPath___closed__3);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = l_Lean_Elab_Command_importPathMessage(v_env_1240_, v_val_1242_);
lean_dec(v_val_1242_);
lean_dec_ref(v_env_1240_);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(v_n_1233_, v___x_1249_, v_a_1228_, v_a_1229_);
lean_dec(v_n_1233_);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v___x_1241_);
lean_dec_ref(v_env_1240_);
v___x_1251_ = lean_obj_once(&l_Lean_Elab_Command_elabImportPath___closed__1, &l_Lean_Elab_Command_elabImportPath___closed__1_once, _init_l_Lean_Elab_Command_elabImportPath___closed__1);
v___x_1252_ = l_Lean_MessageData_ofExpr(v_a_1239_);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = lean_obj_once(&l_Lean_Elab_Command_elabImportPath___closed__5, &l_Lean_Elab_Command_elabImportPath___closed__5_once, _init_l_Lean_Elab_Command_elabImportPath___closed__5);
v___x_1255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(v_n_1233_, v___x_1255_, v_a_1228_, v_a_1229_);
lean_dec(v_n_1233_);
return v___x_1256_;
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1237_);
lean_dec(v_n_1233_);
lean_dec(v___x_1231_);
lean_dec_ref(v_a_1228_);
v_a_1257_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1238_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1238_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v___x_1231_);
v_a_1265_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1267_ = v___x_1236_;
v_isShared_1268_ = v_isSharedCheck_1289_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1236_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1289_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
uint8_t v___x_1269_; 
v___x_1269_ = l_Lean_Exception_isInterrupt(v_a_1265_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_del_object(v___x_1267_);
lean_dec(v_a_1265_);
v___x_1270_ = lean_obj_once(&l_Lean_Elab_Command_elabImportPath___closed__7, &l_Lean_Elab_Command_elabImportPath___closed__7_once, _init_l_Lean_Elab_Command_elabImportPath___closed__7);
v___x_1271_ = l_Lean_Syntax_getId(v_n_1233_);
v___x_1272_ = l_Lean_MessageData_ofName(v___x_1271_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1270_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_obj_once(&l_Lean_Elab_Command_elabImportPath___closed__9, &l_Lean_Elab_Command_elabImportPath___closed__9_once, _init_l_Lean_Elab_Command_elabImportPath___closed__9);
v___x_1275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(v_n_1233_, v___x_1275_, v_a_1228_, v_a_1229_);
lean_dec(v_n_1233_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1284_; 
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v___x_1276_, 0);
lean_dec(v_unused_1285_);
v___x_1278_ = v___x_1276_;
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
else
{
lean_dec(v___x_1276_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = lean_box(0);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1280_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
return v___x_1276_;
}
}
else
{
lean_object* v___x_1287_; 
lean_dec(v_n_1233_);
lean_dec_ref(v_a_1228_);
if (v_isShared_1268_ == 0)
{
v___x_1287_ = v___x_1267_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1265_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___boxed(lean_object* v_stx_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Elab_Command_elabImportPath(v_stx_1290_, v_a_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec(v_stx_1290_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5(lean_object* v_msgData_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(v_msgData_1295_, v___y_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___boxed(lean_object* v_msgData_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5(v_msgData_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1305_, lean_object* v_constName_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg(v_constName_1306_, v___y_1307_, v___y_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1311_, lean_object* v_constName_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1(v_00_u03b1_1311_, v_constName_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1317_, lean_object* v_ref_1318_, lean_object* v_constName_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1318_, v_constName_1319_, v___y_1320_, v___y_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1324_, lean_object* v_ref_1325_, lean_object* v_constName_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1324_, v_ref_1325_, v_constName_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec(v_ref_1325_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b1_1331_, lean_object* v_ref_1332_, lean_object* v_msg_1333_, lean_object* v_declHint_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_1332_, v_msg_1333_, v_declHint_1334_, v___y_1335_, v___y_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_ref_1340_, lean_object* v_msg_1341_, lean_object* v_declHint_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b1_1339_, v_ref_1340_, v_msg_1341_, v_declHint_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec(v_ref_1340_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10(lean_object* v_msg_1347_, lean_object* v_declHint_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg(v_msg_1347_, v_declHint_1348_, v___y_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_1353_, lean_object* v_declHint_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10(v_msg_1353_, v_declHint_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_1359_, lean_object* v_ref_1360_, lean_object* v_msg_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg(v_ref_1360_, v_msg_1361_, v___y_1362_, v___y_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1366_, lean_object* v_ref_1367_, lean_object* v_msg_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10(v_00_u03b1_1366_, v_ref_1367_, v_msg_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec(v_ref_1367_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12(lean_object* v_00_u03b1_1373_, lean_object* v_msg_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg(v_msg_1374_, v___y_1375_, v___y_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_msg_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_1379_, v_msg_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13(lean_object* v_msgData_1385_, lean_object* v_macroStack_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg(v_msgData_1385_, v_macroStack_1386_, v___y_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___boxed(lean_object* v_msgData_1391_, lean_object* v_macroStack_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13(v_msgData_1391_, v_macroStack_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1(){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1411_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1412_ = ((lean_object*)(l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2));
v___x_1413_ = ((lean_object*)(l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4));
v___x_1414_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabImportPath___boxed), 4, 0);
v___x_1415_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1411_, v___x_1412_, v___x_1413_, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___boxed(lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1();
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3(){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = ((lean_object*)(l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4));
v___x_1421_ = ((lean_object*)(l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___closed__0));
v___x_1422_ = l_Lean_addBuiltinDocString(v___x_1420_, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___boxed(lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3();
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; lean_object* v_env_1428_; lean_object* v___x_1429_; lean_object* v_mainModule_1430_; lean_object* v___x_1431_; 
v___x_1427_ = lean_st_ref_get(v___y_1425_);
v_env_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc_ref(v_env_1428_);
lean_dec(v___x_1427_);
v___x_1429_ = l_Lean_Environment_header(v_env_1428_);
lean_dec_ref(v_env_1428_);
v_mainModule_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_mainModule_1430_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_mainModule_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg___boxed(lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(v___y_1432_);
lean_dec(v___y_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1(lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___boxed(lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1(v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0(lean_object* v_ref_1443_, lean_object* v_msgData_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v___x_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = 2;
v___x_1449_ = 0;
v___x_1450_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_ref_1443_, v_msgData_1444_, v___x_1448_, v___x_1449_, v___y_1445_, v___y_1446_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0___boxed(lean_object* v_ref_1451_, lean_object* v_msgData_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0(v_ref_1451_, v_msgData_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec(v_ref_1451_);
return v_res_1456_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__0));
v___x_1459_ = l_Lean_stringToMessageData(v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__2));
v___x_1462_ = l_Lean_stringToMessageData(v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2(lean_object* v___x_1463_, lean_object* v_as_1464_, size_t v_sz_1465_, size_t v_i_1466_, lean_object* v_b_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_a_1472_; uint8_t v___x_1476_; 
v___x_1476_ = lean_usize_dec_lt(v_i_1466_, v_sz_1465_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec_ref(v___y_1468_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_b_1467_);
return v___x_1477_;
}
else
{
lean_object* v___x_1478_; lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1478_ = lean_box(0);
v_a_1479_ = lean_array_uget_borrowed(v_as_1464_, v_i_1466_);
v___x_1480_ = lean_box(0);
lean_inc(v_a_1479_);
v___x_1481_ = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed), 5, 2);
lean_closure_set(v___x_1481_, 0, v_a_1479_);
lean_closure_set(v___x_1481_, 1, v___x_1480_);
lean_inc_ref(v___y_1468_);
v___x_1482_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1481_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1484_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v___x_1482_);
lean_inc_ref(v___y_1468_);
lean_inc(v_a_1483_);
v___x_1484_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0(v_a_1483_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v_a_1487_; lean_object* v___x_1491_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref(v___x_1484_);
v___x_1491_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1463_, v_a_1483_);
lean_dec(v_a_1483_);
if (lean_obj_tag(v___x_1491_) == 1)
{
lean_object* v_val_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_val_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_val_1492_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = lean_obj_once(&l_Lean_Elab_Command_elabImportPath___closed__1, &l_Lean_Elab_Command_elabImportPath___closed__1_once, _init_l_Lean_Elab_Command_elabImportPath___closed__1);
v___x_1494_ = l_Lean_MessageData_ofExpr(v_a_1485_);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = l_Lean_Elab_Command_importPathMessage(v___x_1463_, v_val_1492_);
lean_dec(v_val_1492_);
v___x_1499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v_a_1487_ = v___x_1499_;
goto v___jp_1486_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec(v___x_1491_);
v___x_1500_ = lean_obj_once(&l_Lean_Elab_Command_elabImportPath___closed__1, &l_Lean_Elab_Command_elabImportPath___closed__1_once, _init_l_Lean_Elab_Command_elabImportPath___closed__1);
v___x_1501_ = l_Lean_MessageData_ofExpr(v_a_1485_);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = lean_obj_once(&l_Lean_Elab_Command_elabImportPath___closed__5, &l_Lean_Elab_Command_elabImportPath___closed__5_once, _init_l_Lean_Elab_Command_elabImportPath___closed__5);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v_a_1487_ = v___x_1504_;
goto v___jp_1486_;
}
v___jp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_a_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
lean_inc_ref(v___y_1468_);
v___x_1490_ = l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0(v_a_1479_, v___x_1489_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_dec_ref(v___x_1490_);
v_a_1472_ = v___x_1478_;
goto v___jp_1471_;
}
else
{
lean_dec_ref(v___y_1468_);
return v___x_1490_;
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_a_1483_);
lean_dec_ref(v___y_1468_);
v_a_1505_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1484_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1484_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1533_; 
v_a_1513_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1515_ = v___x_1482_;
v_isShared_1516_ = v_isSharedCheck_1533_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1482_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1533_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
uint8_t v___x_1517_; 
v___x_1517_ = l_Lean_Exception_isInterrupt(v_a_1513_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; 
lean_del_object(v___x_1515_);
lean_dec(v_a_1513_);
v___x_1518_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(v___y_1469_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v___x_1518_);
v___x_1520_ = l_Lean_Syntax_getId(v_a_1479_);
v___x_1521_ = l_Lean_Elab_Command_addAssertExistsEntry___redArg(v___x_1476_, v___x_1520_, v_a_1519_, v___y_1469_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_dec_ref(v___x_1521_);
v_a_1472_ = v___x_1478_;
goto v___jp_1471_;
}
else
{
lean_dec_ref(v___y_1468_);
return v___x_1521_;
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v___y_1468_);
v_a_1522_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1518_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1518_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v___x_1531_; 
lean_dec_ref(v___y_1468_);
if (v_isShared_1516_ == 0)
{
v___x_1531_ = v___x_1515_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1513_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
v___jp_1471_:
{
size_t v___x_1473_; size_t v___x_1474_; 
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = lean_usize_add(v_i_1466_, v___x_1473_);
v_i_1466_ = v___x_1474_;
v_b_1467_ = v_a_1472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___boxed(lean_object* v___x_1534_, lean_object* v_as_1535_, lean_object* v_sz_1536_, lean_object* v_i_1537_, lean_object* v_b_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
size_t v_sz_boxed_1542_; size_t v_i_boxed_1543_; lean_object* v_res_1544_; 
v_sz_boxed_1542_ = lean_unbox_usize(v_sz_1536_);
lean_dec(v_sz_1536_);
v_i_boxed_1543_ = lean_unbox_usize(v_i_1537_);
lean_dec(v_i_1537_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2(v___x_1534_, v_as_1535_, v_sz_boxed_1542_, v_i_boxed_1543_, v_b_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v_as_1535_);
lean_dec_ref(v___x_1534_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists(lean_object* v_stx_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v_env_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; size_t v_sz_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1549_ = lean_st_ref_get(v_a_1547_);
v_env_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc_ref(v_env_1550_);
lean_dec(v___x_1549_);
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = l_Lean_Syntax_getArg(v_stx_1545_, v___x_1551_);
v___x_1553_ = l_Lean_Syntax_getArgs(v___x_1552_);
lean_dec(v___x_1552_);
v___x_1554_ = lean_box(0);
v_sz_1555_ = lean_array_size(v___x_1553_);
v___x_1556_ = ((size_t)0ULL);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2(v_env_1550_, v___x_1553_, v_sz_1555_, v___x_1556_, v___x_1554_, v_a_1546_, v_a_1547_);
lean_dec_ref(v___x_1553_);
lean_dec_ref(v_env_1550_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v___x_1557_, 0);
lean_dec(v_unused_1565_);
v___x_1559_ = v___x_1557_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v___x_1557_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1554_);
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1554_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___boxed(lean_object* v_stx_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Elab_Command_elabAssertNotExists(v_stx_1566_, v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec(v_stx_1566_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1(){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1584_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1585_ = ((lean_object*)(l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1));
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3));
v___x_1587_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAssertNotExists___boxed), 4, 0);
v___x_1588_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1584_, v___x_1585_, v___x_1586_, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___boxed(lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1();
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3(){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = ((lean_object*)(l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3));
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___closed__0));
v___x_1595_ = l_Lean_addBuiltinDocString(v___x_1593_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___boxed(lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3();
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0(lean_object* v_ref_1598_, lean_object* v_msgData_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_1603_; uint8_t v___x_1604_; lean_object* v___x_1605_; 
v___x_1603_ = 1;
v___x_1604_ = 0;
v___x_1605_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_ref_1598_, v_msgData_1599_, v___x_1603_, v___x_1604_, v___y_1600_, v___y_1601_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0___boxed(lean_object* v_ref_1606_, lean_object* v_msgData_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0(v_ref_1606_, v_msgData_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec(v_ref_1606_);
return v_res_1611_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__0));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__2));
v___x_1617_ = l_Lean_stringToMessageData(v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1(lean_object* v___x_1618_, lean_object* v_as_1619_, size_t v_sz_1620_, size_t v_i_1621_, lean_object* v_b_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_a_1627_; uint8_t v___x_1631_; 
v___x_1631_ = lean_usize_dec_lt(v_i_1621_, v_sz_1620_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref(v___y_1623_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_b_1622_);
return v___x_1632_;
}
else
{
lean_object* v___x_1633_; lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1633_ = lean_box(0);
v_a_1634_ = lean_array_uget_borrowed(v_as_1619_, v_i_1621_);
v___x_1635_ = l_Lean_Syntax_getId(v_a_1634_);
v___x_1636_ = l_Lean_Environment_getModuleIdx_x3f(v___x_1618_, v___x_1635_);
if (lean_obj_tag(v___x_1636_) == 1)
{
lean_object* v_val_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v___x_1635_);
v_val_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_val_1637_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1);
lean_inc(v_a_1634_);
v___x_1639_ = l_Lean_MessageData_ofSyntax(v_a_1634_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = l_Lean_Elab_Command_importPathMessage(v___x_1618_, v_val_1637_);
lean_dec(v_val_1637_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
lean_inc_ref(v___y_1623_);
v___x_1645_ = l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0(v_a_1634_, v___x_1644_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_dec_ref(v___x_1645_);
v_a_1627_ = v___x_1633_;
goto v___jp_1626_;
}
else
{
lean_dec_ref(v___y_1623_);
return v___x_1645_;
}
}
else
{
lean_object* v___x_1646_; 
lean_dec(v___x_1636_);
v___x_1646_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(v___y_1624_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref(v___x_1646_);
v___x_1648_ = 0;
v___x_1649_ = l_Lean_Elab_Command_addAssertExistsEntry___redArg(v___x_1648_, v___x_1635_, v_a_1647_, v___y_1624_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_dec_ref(v___x_1649_);
v_a_1627_ = v___x_1633_;
goto v___jp_1626_;
}
else
{
lean_dec_ref(v___y_1623_);
return v___x_1649_;
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v___x_1635_);
lean_dec_ref(v___y_1623_);
v_a_1650_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1646_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1646_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
v___jp_1626_:
{
size_t v___x_1628_; size_t v___x_1629_; 
v___x_1628_ = ((size_t)1ULL);
v___x_1629_ = lean_usize_add(v_i_1621_, v___x_1628_);
v_i_1621_ = v___x_1629_;
v_b_1622_ = v_a_1627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___boxed(lean_object* v___x_1658_, lean_object* v_as_1659_, lean_object* v_sz_1660_, lean_object* v_i_1661_, lean_object* v_b_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
size_t v_sz_boxed_1666_; size_t v_i_boxed_1667_; lean_object* v_res_1668_; 
v_sz_boxed_1666_ = lean_unbox_usize(v_sz_1660_);
lean_dec(v_sz_1660_);
v_i_boxed_1667_ = lean_unbox_usize(v_i_1661_);
lean_dec(v_i_1661_);
v_res_1668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1(v___x_1658_, v_as_1659_, v_sz_boxed_1666_, v_i_boxed_1667_, v_b_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v_as_1659_);
lean_dec_ref(v___x_1658_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported(lean_object* v_stx_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1673_; lean_object* v_env_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; size_t v_sz_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
v___x_1673_ = lean_st_ref_get(v_a_1671_);
v_env_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc_ref(v_env_1674_);
lean_dec(v___x_1673_);
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = l_Lean_Syntax_getArg(v_stx_1669_, v___x_1675_);
v___x_1677_ = l_Lean_Syntax_getArgs(v___x_1676_);
lean_dec(v___x_1676_);
v___x_1678_ = lean_box(0);
v_sz_1679_ = lean_array_size(v___x_1677_);
v___x_1680_ = ((size_t)0ULL);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1(v_env_1674_, v___x_1677_, v_sz_1679_, v___x_1680_, v___x_1678_, v_a_1670_, v_a_1671_);
lean_dec_ref(v___x_1677_);
lean_dec_ref(v_env_1674_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v___x_1681_, 0);
lean_dec(v_unused_1689_);
v___x_1683_ = v___x_1681_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_dec(v___x_1681_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1678_);
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1678_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___boxed(lean_object* v_stx_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Elab_Command_elabAssertNotImported(v_stx_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1692_);
lean_dec(v_stx_1690_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1(){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1708_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1));
v___x_1710_ = ((lean_object*)(l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3));
v___x_1711_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAssertNotImported___boxed), 4, 0);
v___x_1712_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1708_, v___x_1709_, v___x_1710_, v___x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___boxed(lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1();
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3(){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = ((lean_object*)(l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3));
v___x_1718_ = ((lean_object*)(l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___closed__0));
v___x_1719_ = l_Lean_addBuiltinDocString(v___x_1717_, v___x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___boxed(lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3();
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3(lean_object* v_msgData_1722_, uint8_t v_severity_1723_, uint8_t v_isSilent_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Elab_Command_getRef___redArg(v___y_1725_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_a_1729_, v_msgData_1722_, v_severity_1723_, v_isSilent_1724_, v___y_1725_, v___y_1726_);
lean_dec(v_a_1729_);
return v___x_1730_;
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___y_1725_);
lean_dec_ref(v_msgData_1722_);
v_a_1731_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1728_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1728_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3___boxed(lean_object* v_msgData_1739_, lean_object* v_severity_1740_, lean_object* v_isSilent_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v_severity_boxed_1745_; uint8_t v_isSilent_boxed_1746_; lean_object* v_res_1747_; 
v_severity_boxed_1745_ = lean_unbox(v_severity_1740_);
v_isSilent_boxed_1746_ = lean_unbox(v_isSilent_1741_);
v_res_1747_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3(v_msgData_1739_, v_severity_boxed_1745_, v_isSilent_boxed_1746_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3(lean_object* v_msgData_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = 0;
v___x_1753_ = 0;
v___x_1754_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3(v_msgData_1748_, v___x_1752_, v___x_1753_, v___y_1749_, v___y_1750_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3___boxed(lean_object* v_msgData_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3(v_msgData_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2(lean_object* v_msgData_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
uint8_t v___x_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = 1;
v___x_1765_ = 0;
v___x_1766_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3(v_msgData_1760_, v___x_1764_, v___x_1765_, v___y_1761_, v___y_1762_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2___boxed(lean_object* v_msgData_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2(v_msgData_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0(lean_object* v_a_1772_, lean_object* v_as_1773_, size_t v_i_1774_, size_t v_stop_1775_){
_start:
{
uint8_t v___x_1776_; 
v___x_1776_ = lean_usize_dec_eq(v_i_1774_, v_stop_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_array_uget_borrowed(v_as_1773_, v_i_1774_);
v___x_1778_ = lean_name_eq(v_a_1772_, v___x_1777_);
if (v___x_1778_ == 0)
{
size_t v___x_1779_; size_t v___x_1780_; 
v___x_1779_ = ((size_t)1ULL);
v___x_1780_ = lean_usize_add(v_i_1774_, v___x_1779_);
v_i_1774_ = v___x_1780_;
goto _start;
}
else
{
return v___x_1778_;
}
}
else
{
uint8_t v___x_1782_; 
v___x_1782_ = 0;
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0___boxed(lean_object* v_a_1783_, lean_object* v_as_1784_, lean_object* v_i_1785_, lean_object* v_stop_1786_){
_start:
{
size_t v_i_boxed_1787_; size_t v_stop_boxed_1788_; uint8_t v_res_1789_; lean_object* v_r_1790_; 
v_i_boxed_1787_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_stop_boxed_1788_ = lean_unbox_usize(v_stop_1786_);
lean_dec(v_stop_1786_);
v_res_1789_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0(v_a_1783_, v_as_1784_, v_i_boxed_1787_, v_stop_boxed_1788_);
lean_dec_ref(v_as_1784_);
lean_dec(v_a_1783_);
v_r_1790_ = lean_box(v_res_1789_);
return v_r_1790_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0(lean_object* v_as_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_array_get_size(v_as_1791_);
v___x_1795_ = lean_nat_dec_lt(v___x_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
return v___x_1795_;
}
else
{
if (v___x_1795_ == 0)
{
return v___x_1795_;
}
else
{
size_t v___x_1796_; size_t v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = ((size_t)0ULL);
v___x_1797_ = lean_usize_of_nat(v___x_1794_);
v___x_1798_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0(v_a_1792_, v_as_1791_, v___x_1796_, v___x_1797_);
return v___x_1798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0___boxed(lean_object* v_as_1799_, lean_object* v_a_1800_){
_start:
{
uint8_t v_res_1801_; lean_object* v_r_1802_; 
v_res_1801_ = l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0(v_as_1799_, v_a_1800_);
lean_dec(v_a_1800_);
lean_dec_ref(v_as_1799_);
v_r_1802_ = lean_box(v_res_1801_);
return v_r_1802_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__0));
v___x_1805_ = l_Lean_stringToMessageData(v___x_1804_);
return v___x_1805_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__2));
v___x_1808_ = l_Lean_stringToMessageData(v___x_1807_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__4));
v___x_1811_ = l_Lean_stringToMessageData(v___x_1810_);
return v___x_1811_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__6));
v___x_1814_ = l_Lean_stringToMessageData(v___x_1813_);
return v___x_1814_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = l_Lean_crossEmoji;
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = l_Lean_checkEmoji;
v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg(lean_object* v_tk_1821_, lean_object* v___x_1822_, lean_object* v___x_1823_, lean_object* v_as_1824_, size_t v_sz_1825_, size_t v_i_1826_, lean_object* v_b_1827_){
_start:
{
lean_object* v_a_1830_; uint8_t v___x_1834_; 
v___x_1834_ = lean_usize_dec_lt(v_i_1826_, v_sz_1825_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_dec_ref(v___x_1823_);
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_b_1827_);
return v___x_1835_;
}
else
{
lean_object* v_snd_1836_; lean_object* v_fst_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1903_; 
v_snd_1836_ = lean_ctor_get(v_b_1827_, 1);
v_fst_1837_ = lean_ctor_get(v_b_1827_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_b_1827_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1839_ = v_b_1827_;
v_isShared_1840_ = v_isSharedCheck_1903_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_snd_1836_);
lean_inc(v_fst_1837_);
lean_dec(v_b_1827_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1903_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_snd_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1901_; 
v_snd_1841_ = lean_ctor_get(v_snd_1836_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_snd_1836_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v_snd_1836_, 0);
lean_dec(v_unused_1902_);
v___x_1843_ = v_snd_1836_;
v_isShared_1844_ = v_isSharedCheck_1901_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_snd_1841_);
lean_dec(v_snd_1836_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1901_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_a_1845_; uint8_t v_isDecl_1846_; lean_object* v_givenName_1847_; lean_object* v_modName_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; lean_object* v___y_1876_; lean_object* v___y_1877_; uint8_t v___y_1878_; uint8_t v___y_1879_; lean_object* v___y_1885_; uint8_t v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1891_; uint8_t v___y_1892_; lean_object* v___y_1896_; 
v_a_1845_ = lean_array_uget_borrowed(v_as_1824_, v_i_1826_);
v_isDecl_1846_ = lean_ctor_get_uint8(v_a_1845_, sizeof(void*)*2);
v_givenName_1847_ = lean_ctor_get(v_a_1845_, 0);
v_modName_1848_ = lean_ctor_get(v_a_1845_, 1);
if (v_isDecl_1846_ == 0)
{
lean_object* v___x_1899_; 
v___x_1899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__10));
v___y_1896_ = v___x_1899_;
goto v___jp_1895_;
}
else
{
lean_object* v___x_1900_; 
v___x_1900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__11));
v___y_1896_ = v___x_1900_;
goto v___jp_1895_;
}
v___jp_1849_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1);
lean_inc_ref(v___y_1850_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___y_1850_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
lean_inc(v_givenName_1847_);
v___x_1855_ = l_Lean_MessageData_ofName(v_givenName_1847_);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l_Lean_stringToMessageData(v___y_1851_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
lean_inc(v_modName_1848_);
v___x_1863_ = l_Lean_MessageData_ofName(v_modName_1848_);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_array_push(v_fst_1837_, v___x_1866_);
v___x_1868_ = lean_box(v___y_1852_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1868_);
lean_ctor_set(v___x_1843_, 0, v___y_1850_);
v___x_1870_ = v___x_1843_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___y_1850_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1872_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___x_1870_);
lean_ctor_set(v___x_1839_, 0, v___x_1867_);
v___x_1872_ = v___x_1839_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
v_a_1830_ = v___x_1872_;
goto v___jp_1829_;
}
}
}
v___jp_1875_:
{
uint8_t v___x_1880_; 
v___x_1880_ = l_Lean_Syntax_isNone(v_tk_1821_);
if (v___x_1880_ == 0)
{
if (v___y_1878_ == 0)
{
v___y_1850_ = v___y_1876_;
v___y_1851_ = v___y_1877_;
v___y_1852_ = v___y_1879_;
goto v___jp_1849_;
}
else
{
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec_ref(v___y_1877_);
lean_del_object(v___x_1843_);
lean_del_object(v___x_1839_);
v___x_1881_ = lean_box(v___y_1879_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___y_1876_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v_fst_1837_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v_a_1830_ = v___x_1883_;
goto v___jp_1829_;
}
else
{
v___y_1850_ = v___y_1876_;
v___y_1851_ = v___y_1877_;
v___y_1852_ = v___y_1879_;
goto v___jp_1849_;
}
}
}
else
{
v___y_1850_ = v___y_1876_;
v___y_1851_ = v___y_1877_;
v___y_1852_ = v___y_1879_;
goto v___jp_1849_;
}
}
v___jp_1884_:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_unbox(v_snd_1841_);
if (v___x_1888_ == 0)
{
uint8_t v___x_1889_; 
v___x_1889_ = lean_unbox(v_snd_1841_);
lean_dec(v_snd_1841_);
v___y_1876_ = v___y_1887_;
v___y_1877_ = v___y_1885_;
v___y_1878_ = v___y_1886_;
v___y_1879_ = v___x_1889_;
goto v___jp_1875_;
}
else
{
lean_dec(v_snd_1841_);
v___y_1876_ = v___y_1887_;
v___y_1877_ = v___y_1885_;
v___y_1878_ = v___y_1886_;
v___y_1879_ = v___y_1886_;
goto v___jp_1875_;
}
}
v___jp_1890_:
{
if (v___y_1892_ == 0)
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8);
v___y_1885_ = v___y_1891_;
v___y_1886_ = v___y_1892_;
v___y_1887_ = v___x_1893_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9);
v___y_1885_ = v___y_1891_;
v___y_1886_ = v___y_1892_;
v___y_1887_ = v___x_1894_;
goto v___jp_1884_;
}
}
v___jp_1895_:
{
if (v_isDecl_1846_ == 0)
{
uint8_t v___x_1897_; 
v___x_1897_ = l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0(v___x_1822_, v_givenName_1847_);
v___y_1891_ = v___y_1896_;
v___y_1892_ = v___x_1897_;
goto v___jp_1890_;
}
else
{
uint8_t v___x_1898_; 
lean_inc(v_givenName_1847_);
lean_inc_ref(v___x_1823_);
v___x_1898_ = l_Lean_Environment_contains(v___x_1823_, v_givenName_1847_, v___x_1834_);
v___y_1891_ = v___y_1896_;
v___y_1892_ = v___x_1898_;
goto v___jp_1890_;
}
}
}
}
}
v___jp_1829_:
{
size_t v___x_1831_; size_t v___x_1832_; 
v___x_1831_ = ((size_t)1ULL);
v___x_1832_ = lean_usize_add(v_i_1826_, v___x_1831_);
v_i_1826_ = v___x_1832_;
v_b_1827_ = v_a_1830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___boxed(lean_object* v_tk_1904_, lean_object* v___x_1905_, lean_object* v___x_1906_, lean_object* v_as_1907_, lean_object* v_sz_1908_, lean_object* v_i_1909_, lean_object* v_b_1910_, lean_object* v___y_1911_){
_start:
{
size_t v_sz_boxed_1912_; size_t v_i_boxed_1913_; lean_object* v_res_1914_; 
v_sz_boxed_1912_ = lean_unbox_usize(v_sz_1908_);
lean_dec(v_sz_1908_);
v_i_boxed_1913_ = lean_unbox_usize(v_i_1909_);
lean_dec(v_i_1909_);
v_res_1914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg(v_tk_1904_, v___x_1905_, v___x_1906_, v_as_1907_, v_sz_boxed_1912_, v_i_boxed_1913_, v_b_1910_);
lean_dec_ref(v_as_1907_);
lean_dec_ref(v___x_1905_);
lean_dec(v_tk_1904_);
return v_res_1914_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__0(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0));
v___x_1916_ = l_Lean_stringToMessageData(v___x_1915_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__1(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1917_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__0, &l_Lean_Elab_Command_elabCheckAssertions___closed__0_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__0);
v___x_1918_ = lean_unsigned_to_nat(1u);
v___x_1919_ = lean_mk_empty_array_with_capacity(v___x_1918_);
v___x_1920_ = lean_array_push(v___x_1919_, v___x_1917_);
return v___x_1920_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__2(void){
_start:
{
uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1921_ = 1;
v___x_1922_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__0, &l_Lean_Elab_Command_elabCheckAssertions___closed__0_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__0);
v___x_1923_ = lean_box(v___x_1921_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__3(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__2, &l_Lean_Elab_Command_elabCheckAssertions___closed__2_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__2);
v___x_1926_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__1, &l_Lean_Elab_Command_elabCheckAssertions___closed__1_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__1);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1925_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__5(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l_Lean_Elab_Command_elabCheckAssertions___closed__4));
v___x_1930_ = l_Lean_stringToMessageData(v___x_1929_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__7(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l_Lean_Elab_Command_elabCheckAssertions___closed__6));
v___x_1933_ = l_Lean_stringToMessageData(v___x_1932_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__8(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__7, &l_Lean_Elab_Command_elabCheckAssertions___closed__7_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__7);
v___x_1935_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v___x_1934_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__10(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l_Lean_Elab_Command_elabCheckAssertions___closed__9));
v___x_1939_ = l_Lean_stringToMessageData(v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__11(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__10, &l_Lean_Elab_Command_elabCheckAssertions___closed__10_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__10);
v___x_1941_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v___x_1940_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__14(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_Lean_Elab_Command_elabCheckAssertions___closed__13));
v___x_1947_ = l_Lean_MessageData_ofFormat(v___x_1946_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckAssertions___closed__17(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lean_Elab_Command_elabCheckAssertions___closed__16));
v___x_1952_ = l_Lean_MessageData_ofFormat(v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions(lean_object* v_stx_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1960_; lean_object* v_env_1961_; lean_object* v___x_1962_; lean_object* v_tk_1963_; lean_object* v___x_1964_; uint8_t v___y_1966_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1960_ = lean_st_ref_get(v_a_1955_);
v_env_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc_ref(v_env_1961_);
lean_dec(v___x_1960_);
v___x_1962_ = lean_unsigned_to_nat(1u);
v_tk_1963_ = l_Lean_Syntax_getArg(v_stx_1953_, v___x_1962_);
lean_inc_ref(v_env_1961_);
v___x_1964_ = l_Lean_Elab_Command_getSortedAssertExists(v_env_1961_);
v___x_1999_ = lean_array_get_size(v___x_1964_);
v___x_2000_ = lean_unsigned_to_nat(0u);
v___x_2001_ = lean_nat_dec_eq(v___x_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
v___y_1966_ = v___x_2001_;
goto v___jp_1965_;
}
else
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Lean_Syntax_isNone(v_tk_1963_);
v___y_1966_ = v___x_2002_;
goto v___jp_1965_;
}
v___jp_1957_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
v___jp_1965_:
{
if (v___y_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; size_t v_sz_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1967_ = l_Lean_Environment_allImportedModuleNames(v_env_1961_);
v___x_1968_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__3, &l_Lean_Elab_Command_elabCheckAssertions___closed__3_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__3);
v_sz_1969_ = lean_array_size(v___x_1964_);
v___x_1970_ = ((size_t)0ULL);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg(v_tk_1963_, v___x_1967_, v_env_1961_, v___x_1964_, v_sz_1969_, v___x_1970_, v___x_1968_);
lean_dec_ref(v___x_1964_);
lean_dec_ref(v___x_1967_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v_snd_1973_; lean_object* v_fst_1974_; lean_object* v_snd_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref(v___x_1971_);
v_snd_1973_ = lean_ctor_get(v_a_1972_, 1);
lean_inc(v_snd_1973_);
v_fst_1974_ = lean_ctor_get(v_a_1972_, 0);
lean_inc(v_fst_1974_);
lean_dec(v_a_1972_);
v_snd_1975_ = lean_ctor_get(v_snd_1973_, 1);
lean_inc(v_snd_1975_);
lean_dec(v_snd_1973_);
v___x_1976_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__5, &l_Lean_Elab_Command_elabCheckAssertions___closed__5_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__5);
v___x_1977_ = lean_array_push(v_fst_1974_, v___x_1976_);
v___x_1978_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__8, &l_Lean_Elab_Command_elabCheckAssertions___closed__8_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__8);
v___x_1979_ = lean_array_push(v___x_1977_, v___x_1978_);
v___x_1980_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__11, &l_Lean_Elab_Command_elabCheckAssertions___closed__11_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__11);
v___x_1981_ = lean_array_push(v___x_1979_, v___x_1980_);
v___x_1982_ = lean_array_to_list(v___x_1981_);
v___x_1983_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__14, &l_Lean_Elab_Command_elabCheckAssertions___closed__14_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__14);
v___x_1984_ = l_Lean_MessageData_joinSep(v___x_1982_, v___x_1983_);
v___x_1985_ = lean_unbox(v_snd_1975_);
lean_dec(v_snd_1975_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; 
lean_dec(v_tk_1963_);
v___x_1986_ = l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2(v___x_1984_, v_a_1954_, v_a_1955_);
return v___x_1986_;
}
else
{
uint8_t v___x_1987_; 
v___x_1987_ = l_Lean_Syntax_isNone(v_tk_1963_);
lean_dec(v_tk_1963_);
if (v___x_1987_ == 0)
{
lean_dec_ref(v___x_1984_);
lean_dec_ref(v_a_1954_);
goto v___jp_1957_;
}
else
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3(v___x_1984_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_dec_ref(v___x_1988_);
goto v___jp_1957_;
}
else
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_tk_1963_);
lean_dec_ref(v_a_1954_);
v_a_1989_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1971_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1971_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_dec_ref(v___x_1964_);
lean_dec(v_tk_1963_);
lean_dec_ref(v_env_1961_);
v___x_1997_ = lean_obj_once(&l_Lean_Elab_Command_elabCheckAssertions___closed__17, &l_Lean_Elab_Command_elabCheckAssertions___closed__17_once, _init_l_Lean_Elab_Command_elabCheckAssertions___closed__17);
v___x_1998_ = l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3(v___x_1997_, v_a_1954_, v_a_1955_);
return v___x_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___boxed(lean_object* v_stx_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Elab_Command_elabCheckAssertions(v_stx_2003_, v_a_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec(v_stx_2003_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1(lean_object* v_tk_2008_, lean_object* v___x_2009_, lean_object* v___x_2010_, lean_object* v_as_2011_, size_t v_sz_2012_, size_t v_i_2013_, lean_object* v_b_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg(v_tk_2008_, v___x_2009_, v___x_2010_, v_as_2011_, v_sz_2012_, v_i_2013_, v_b_2014_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___boxed(lean_object* v_tk_2019_, lean_object* v___x_2020_, lean_object* v___x_2021_, lean_object* v_as_2022_, lean_object* v_sz_2023_, lean_object* v_i_2024_, lean_object* v_b_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
size_t v_sz_boxed_2029_; size_t v_i_boxed_2030_; lean_object* v_res_2031_; 
v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2023_);
lean_dec(v_sz_2023_);
v_i_boxed_2030_ = lean_unbox_usize(v_i_2024_);
lean_dec(v_i_2024_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1(v_tk_2019_, v___x_2020_, v___x_2021_, v_as_2022_, v_sz_boxed_2029_, v_i_boxed_2030_, v_b_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec_ref(v_as_2022_);
lean_dec_ref(v___x_2020_);
lean_dec(v_tk_2019_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1(){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2045_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2046_ = ((lean_object*)(l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1));
v___x_2047_ = ((lean_object*)(l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3));
v___x_2048_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckAssertions___boxed), 4, 0);
v___x_2049_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2045_, v___x_2046_, v___x_2047_, v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___boxed(lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1();
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3(){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = ((lean_object*)(l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3));
v___x_2055_ = ((lean_object*)(l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___closed__0));
v___x_2056_ = l_Lean_addBuiltinDocString(v___x_2054_, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___boxed(lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3();
return v_res_2058_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_AssertExists(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_assertExistsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_assertExistsExt);
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_AssertExists(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_AssertExists(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_AssertExists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_AssertExists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_AssertExists(builtin);
}
#ifdef __cplusplus
}
#endif
