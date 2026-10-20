// Lean compiler output
// Module: Lean.Elab.Do.InferControlInfo
// Imports: public import Lean.Elab.Term public import Lean.Elab.Do.ForwardSyntax meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Parser_Term_getDoElems(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getPatternVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_getLetPatDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getLetIdDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_pure;
static lean_once_cell_t l_Lean_Elab_Do_ControlInfo_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlInfo_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_empty;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", reassigns: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofName, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = ", numRegularExits: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ",\n    noFallthrough: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ",\n    returnsEarly: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "breaks: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", continues: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value)} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "builtin_doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 75, 74, 17, 172, 74, 138, 206)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 182, 102, 169, 76, 87, 55, 254)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value),LEAN_SCALAR_PTR_LITERAL(208, 65, 144, 138, 55, 55, 217, 220)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ControlInfoHandler"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value),LEAN_SCALAR_PTR_LITERAL(18, 126, 127, 228, 104, 205, 61, 148)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "control info inference"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "controlInfoElemAttribute"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 110, 218, 82, 47, 2, 10, 58)}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 238, .m_capacity = 238, .m_length = 235, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `DoElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`."};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(119) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(127) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 165, 255, 22, 123, 199, 70, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "No `ControlInfo` inference handler found for `"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "` in syntax "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "\nRegister a handler with `@[doElem_control_info "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]`."};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doLetRec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value),LEAN_SCALAR_PTR_LITERAL(82, 47, 84, 182, 64, 225, 123, 219)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 158, 71, 138, 110, 159, 158, 208)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Not a let or reassignment declaration: "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doSkip"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalSyntax"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value),LEAN_SCALAR_PTR_LITERAL(117, 4, 119, 3, 13, 160, 149, 47)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_3),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value),LEAN_SCALAR_PTR_LITERAL(125, 157, 182, 149, 109, 63, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doAssertion"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value),LEAN_SCALAR_PTR_LITERAL(144, 179, 243, 245, 156, 230, 227, 142)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doCatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 196, 191, 146, 79, 230, 20, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "doCatchMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 106, 10, 98, 177, 11, 181, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Not a catch or catch match: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doLoopDecreasing"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value),LEAN_SCALAR_PTR_LITERAL(0, 112, 64, 8, 91, 183, 41, 148)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doLoopInvariant"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value),LEAN_SCALAR_PTR_LITERAL(207, 155, 107, 150, 202, 64, 185, 181)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doErasedArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value),LEAN_SCALAR_PTR_LITERAL(176, 216, 203, 158, 108, 103, 134, 112)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doErased"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_value),LEAN_SCALAR_PTR_LITERAL(69, 69, 120, 16, 133, 86, 56, 26)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; 
v___x_1_ = l_Lean_NameSet_empty;
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = 0;
v___x_4_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4_, 0, v___x_2_);
lean_ctor_set(v___x_4_, 1, v___x_1_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 1, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 2, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 3, v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_Elab_Do_instInhabitedControlInfo_default;
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_empty___closed__0(void){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; 
v___x_8_ = l_Lean_NameSet_empty;
v___x_9_ = 1;
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = 0;
v___x_12_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_12_, 0, v___x_10_);
lean_ctor_set(v___x_12_, 1, v___x_8_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2 + 1, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2 + 2, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2 + 3, v___x_9_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_empty(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_empty___closed__0, &l_Lean_Elab_Do_ControlInfo_empty___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_empty___closed__0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
uint8_t v_breaks_16_; uint8_t v_continues_17_; uint8_t v_returnsEarly_18_; uint8_t v_noFallthrough_19_; lean_object* v_reassigns_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_52_; 
v_breaks_16_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2);
v_continues_17_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2 + 1);
v_returnsEarly_18_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2 + 2);
v_noFallthrough_19_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2 + 3);
v_reassigns_20_ = lean_ctor_get(v_a_14_, 1);
v_isSharedCheck_52_ = !lean_is_exclusive(v_a_14_);
if (v_isSharedCheck_52_ == 0)
{
lean_object* v_unused_53_; 
v_unused_53_ = lean_ctor_get(v_a_14_, 0);
lean_dec(v_unused_53_);
v___x_22_ = v_a_14_;
v_isShared_23_ = v_isSharedCheck_52_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_reassigns_20_);
lean_dec(v_a_14_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_52_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
uint8_t v___y_25_; uint8_t v___y_26_; uint8_t v___y_27_; lean_object* v___y_28_; lean_object* v___y_29_; uint8_t v___y_30_; uint8_t v___y_36_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_45_; uint8_t v___y_46_; uint8_t v___y_49_; 
if (v_breaks_16_ == 0)
{
uint8_t v_breaks_51_; 
v_breaks_51_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2);
v___y_49_ = v_breaks_51_;
goto v___jp_48_;
}
else
{
v___y_49_ = v_breaks_16_;
goto v___jp_48_;
}
v___jp_24_:
{
lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_31_ = l_Lean_NameSet_append(v_reassigns_20_, v___y_28_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_31_);
lean_ctor_set(v___x_22_, 0, v___y_29_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___y_29_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2, v___y_27_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 1, v___y_26_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 2, v___y_25_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 3, v___y_30_);
return v___x_33_;
}
}
v___jp_35_:
{
if (v_noFallthrough_19_ == 0)
{
lean_object* v_numRegularExits_39_; uint8_t v_noFallthrough_40_; lean_object* v_reassigns_41_; 
v_numRegularExits_39_ = lean_ctor_get(v_b_15_, 0);
lean_inc(v_numRegularExits_39_);
v_noFallthrough_40_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2 + 3);
v_reassigns_41_ = lean_ctor_get(v_b_15_, 1);
lean_inc(v_reassigns_41_);
lean_dec_ref(v_b_15_);
v___y_25_ = v___y_38_;
v___y_26_ = v___y_36_;
v___y_27_ = v___y_37_;
v___y_28_ = v_reassigns_41_;
v___y_29_ = v_numRegularExits_39_;
v___y_30_ = v_noFallthrough_40_;
goto v___jp_24_;
}
else
{
lean_object* v_numRegularExits_42_; lean_object* v_reassigns_43_; 
v_numRegularExits_42_ = lean_ctor_get(v_b_15_, 0);
lean_inc(v_numRegularExits_42_);
v_reassigns_43_ = lean_ctor_get(v_b_15_, 1);
lean_inc(v_reassigns_43_);
lean_dec_ref(v_b_15_);
v___y_25_ = v___y_38_;
v___y_26_ = v___y_36_;
v___y_27_ = v___y_37_;
v___y_28_ = v_reassigns_43_;
v___y_29_ = v_numRegularExits_42_;
v___y_30_ = v_noFallthrough_19_;
goto v___jp_24_;
}
}
v___jp_44_:
{
if (v_returnsEarly_18_ == 0)
{
uint8_t v_returnsEarly_47_; 
v_returnsEarly_47_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2 + 2);
v___y_36_ = v___y_46_;
v___y_37_ = v___y_45_;
v___y_38_ = v_returnsEarly_47_;
goto v___jp_35_;
}
else
{
v___y_36_ = v___y_46_;
v___y_37_ = v___y_45_;
v___y_38_ = v_returnsEarly_18_;
goto v___jp_35_;
}
}
v___jp_48_:
{
if (v_continues_17_ == 0)
{
uint8_t v_continues_50_; 
v_continues_50_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2 + 1);
v___y_45_ = v___y_49_;
v___y_46_ = v_continues_50_;
goto v___jp_44_;
}
else
{
v___y_45_ = v___y_49_;
v___y_46_ = v_continues_17_;
goto v___jp_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object* v_a_54_, lean_object* v_b_55_){
_start:
{
uint8_t v___y_57_; lean_object* v___y_58_; uint8_t v___y_59_; lean_object* v___y_60_; lean_object* v___y_61_; uint8_t v___y_62_; uint8_t v___y_63_; uint8_t v_breaks_66_; uint8_t v_continues_67_; uint8_t v_returnsEarly_68_; lean_object* v_numRegularExits_69_; uint8_t v_noFallthrough_70_; lean_object* v_reassigns_71_; uint8_t v___y_73_; uint8_t v___y_74_; uint8_t v___y_75_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_85_; 
v_breaks_66_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2);
v_continues_67_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2 + 1);
v_returnsEarly_68_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2 + 2);
v_numRegularExits_69_ = lean_ctor_get(v_a_54_, 0);
lean_inc(v_numRegularExits_69_);
v_noFallthrough_70_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2 + 3);
v_reassigns_71_ = lean_ctor_get(v_a_54_, 1);
lean_inc(v_reassigns_71_);
lean_dec_ref(v_a_54_);
if (v_breaks_66_ == 0)
{
uint8_t v_breaks_87_; 
v_breaks_87_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2);
v___y_85_ = v_breaks_87_;
goto v___jp_84_;
}
else
{
v___y_85_ = v_breaks_66_;
goto v___jp_84_;
}
v___jp_56_:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = l_Lean_NameSet_append(v___y_58_, v___y_61_);
v___x_65_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_65_, 0, v___y_60_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___y_59_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 1, v___y_57_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 2, v___y_62_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 3, v___y_63_);
return v___x_65_;
}
v___jp_72_:
{
lean_object* v_numRegularExits_76_; uint8_t v_noFallthrough_77_; lean_object* v_reassigns_78_; lean_object* v___x_79_; 
v_numRegularExits_76_ = lean_ctor_get(v_b_55_, 0);
lean_inc(v_numRegularExits_76_);
v_noFallthrough_77_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2 + 3);
v_reassigns_78_ = lean_ctor_get(v_b_55_, 1);
lean_inc(v_reassigns_78_);
lean_dec_ref(v_b_55_);
v___x_79_ = lean_nat_add(v_numRegularExits_69_, v_numRegularExits_76_);
lean_dec(v_numRegularExits_76_);
lean_dec(v_numRegularExits_69_);
if (v_noFallthrough_70_ == 0)
{
v___y_57_ = v___y_73_;
v___y_58_ = v_reassigns_71_;
v___y_59_ = v___y_74_;
v___y_60_ = v___x_79_;
v___y_61_ = v_reassigns_78_;
v___y_62_ = v___y_75_;
v___y_63_ = v_noFallthrough_70_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___y_73_;
v___y_58_ = v_reassigns_71_;
v___y_59_ = v___y_74_;
v___y_60_ = v___x_79_;
v___y_61_ = v_reassigns_78_;
v___y_62_ = v___y_75_;
v___y_63_ = v_noFallthrough_77_;
goto v___jp_56_;
}
}
v___jp_80_:
{
if (v_returnsEarly_68_ == 0)
{
uint8_t v_returnsEarly_83_; 
v_returnsEarly_83_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2 + 2);
v___y_73_ = v___y_82_;
v___y_74_ = v___y_81_;
v___y_75_ = v_returnsEarly_83_;
goto v___jp_72_;
}
else
{
v___y_73_ = v___y_82_;
v___y_74_ = v___y_81_;
v___y_75_ = v_returnsEarly_68_;
goto v___jp_72_;
}
}
v___jp_84_:
{
if (v_continues_67_ == 0)
{
uint8_t v_continues_86_; 
v_continues_86_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2 + 1);
v___y_81_ = v___y_85_;
v___y_82_ = v_continues_86_;
goto v___jp_80_;
}
else
{
v___y_81_ = v___y_85_;
v___y_82_ = v_continues_67_;
goto v___jp_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object* v_x1_88_, lean_object* v_x2_89_, lean_object* v_x3_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v_x1_88_);
lean_ctor_set(v___x_91_, 1, v_x3_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0));
v___x_94_ = l_Lean_stringToMessageData(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13));
v___x_117_ = l_Lean_stringToMessageData(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15));
v___x_120_ = l_Lean_stringToMessageData(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19));
v___x_125_ = l_Lean_stringToMessageData(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21));
v___x_128_ = l_Lean_stringToMessageData(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23));
v___x_131_ = l_Lean_stringToMessageData(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object* v___f_132_, lean_object* v_info_133_){
_start:
{
lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; uint8_t v_breaks_150_; uint8_t v_continues_151_; uint8_t v_returnsEarly_152_; lean_object* v_numRegularExits_153_; uint8_t v_noFallthrough_154_; lean_object* v_reassigns_155_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___x_182_; lean_object* v___y_184_; 
v_breaks_150_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2);
v_continues_151_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2 + 1);
v_returnsEarly_152_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2 + 2);
v_numRegularExits_153_ = lean_ctor_get(v_info_133_, 0);
lean_inc(v_numRegularExits_153_);
v_noFallthrough_154_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2 + 3);
v_reassigns_155_ = lean_ctor_get(v_info_133_, 1);
lean_inc(v_reassigns_155_);
lean_dec_ref(v_info_133_);
v___x_182_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22);
if (v_breaks_150_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_184_ = v___x_192_;
goto v___jp_183_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_184_ = v___x_193_;
goto v___jp_183_;
}
v___jp_134_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
lean_inc_ref(v___y_137_);
v___x_138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_138_, 0, v___y_137_);
v___x_139_ = l_Lean_MessageData_ofFormat(v___x_138_);
v___x_140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_136_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_box(0);
v___x_144_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11));
v___x_145_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_144_, v___f_132_, v___x_143_, v___y_135_);
v___x_146_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12));
v___x_147_ = l_List_mapTR_loop___redArg(v___x_146_, v___x_145_, v___x_143_);
v___x_148_ = l_Lean_MessageData_ofList(v___x_147_);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_142_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
v___jp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_inc_ref(v___y_158_);
v___x_159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_159_, 0, v___y_158_);
v___x_160_ = l_Lean_MessageData_ofFormat(v___x_159_);
v___x_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_161_, 0, v___y_157_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14);
v___x_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Nat_reprFast(v_numRegularExits_153_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = l_Lean_MessageData_ofFormat(v___x_165_);
v___x_167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_163_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16);
v___x_169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
if (v_noFallthrough_154_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_135_ = v_reassigns_155_;
v___y_136_ = v___x_169_;
v___y_137_ = v___x_170_;
goto v___jp_134_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_135_ = v_reassigns_155_;
v___y_136_ = v___x_169_;
v___y_137_ = v___x_171_;
goto v___jp_134_;
}
}
v___jp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc_ref(v___y_174_);
v___x_175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_175_, 0, v___y_174_);
v___x_176_ = l_Lean_MessageData_ofFormat(v___x_175_);
v___x_177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_177_, 0, v___y_173_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20);
v___x_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
if (v_returnsEarly_152_ == 0)
{
lean_object* v___x_180_; 
v___x_180_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_157_ = v___x_179_;
v___y_158_ = v___x_180_;
goto v___jp_156_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_157_ = v___x_179_;
v___y_158_ = v___x_181_;
goto v___jp_156_;
}
}
v___jp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc_ref(v___y_184_);
v___x_185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_185_, 0, v___y_184_);
v___x_186_ = l_Lean_MessageData_ofFormat(v___x_185_);
v___x_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_182_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24);
v___x_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
if (v_continues_151_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_173_ = v___x_189_;
v___y_174_ = v___x_190_;
goto v___jp_172_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_173_ = v___x_189_;
v___y_174_ = v___x_191_;
goto v___jp_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object* v_ref_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1));
v___x_225_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3));
v___x_226_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8));
v___x_227_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12));
v___x_228_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13));
v___x_229_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_224_, v___x_225_, v___x_226_, v___x_227_, v___x_228_, v_ref_222_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object* v_ref_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v_ref_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_241_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2____boxed(lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1(){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0));
v___x_248_ = l_Lean_addBuiltinDocString(v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3(){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_278_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6));
v___x_279_ = l_Lean_addBuiltinDeclarationRanges(v___x_277_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object* v_msgData_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_env_289_; uint8_t v___x_290_; lean_object* v_env_291_; lean_object* v___x_292_; lean_object* v_toCold_293_; lean_object* v_mctx_294_; lean_object* v_lctx_295_; lean_object* v_options_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = 0;
v_env_291_ = l_Lean_Environment_setRecordingDeps(v_env_289_, v___x_290_);
v___x_292_ = lean_st_ref_get(v___y_284_);
v_toCold_293_ = lean_ctor_get(v___y_285_, 0);
v_mctx_294_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_mctx_294_);
lean_dec(v___x_292_);
v_lctx_295_ = lean_ctor_get(v___y_283_, 2);
v_options_296_ = lean_ctor_get(v_toCold_293_, 2);
lean_inc_ref(v_options_296_);
lean_inc_ref(v_lctx_295_);
v___x_297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_297_, 0, v_env_291_);
lean_ctor_set(v___x_297_, 1, v_mctx_294_);
lean_ctor_set(v___x_297_, 2, v_lctx_295_);
lean_ctor_set(v___x_297_, 3, v_options_296_);
v___x_298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_msgData_282_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_box(1);
v___x_308_ = l_Lean_MessageData_ofFormat(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_313_ = l_Lean_MessageData_ofFormat(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
return v_x_314_;
}
else
{
lean_object* v_head_316_; lean_object* v_tail_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_339_; 
v_head_316_ = lean_ctor_get(v_x_315_, 0);
v_tail_317_ = lean_ctor_get(v_x_315_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_339_ == 0)
{
v___x_319_ = v_x_315_;
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_tail_317_);
lean_inc(v_head_316_);
lean_dec(v_x_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_before_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_337_; 
v_before_321_ = lean_ctor_get(v_head_316_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_head_316_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_head_316_, 1);
lean_dec(v_unused_338_);
v___x_323_ = v_head_316_;
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_before_321_);
lean_dec(v_head_316_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 7);
lean_ctor_set(v___x_323_, 1, v___x_325_);
lean_ctor_set(v___x_323_, 0, v_x_314_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_x_314_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_336_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 7);
lean_ctor_set(v___x_319_, 1, v___x_328_);
lean_ctor_set(v___x_319_, 0, v___x_327_);
v___x_330_ = v___x_319_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_335_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = l_Lean_MessageData_ofSyntax(v_before_321_);
v___x_332_ = l_Lean_indentD(v___x_331_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_330_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v_x_314_ = v___x_333_;
v_x_315_ = v_tail_317_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_340_, lean_object* v_opt_341_){
_start:
{
lean_object* v_name_342_; lean_object* v_defValue_343_; lean_object* v_map_344_; lean_object* v___x_345_; 
v_name_342_ = lean_ctor_get(v_opt_341_, 0);
v_defValue_343_ = lean_ctor_get(v_opt_341_, 1);
v_map_344_ = lean_ctor_get(v_opts_340_, 0);
v___x_345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_344_, v_name_342_);
if (lean_obj_tag(v___x_345_) == 0)
{
uint8_t v___x_346_; 
v___x_346_ = lean_unbox(v_defValue_343_);
return v___x_346_;
}
else
{
lean_object* v_val_347_; 
v_val_347_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v___x_345_, 1);
if (lean_obj_tag(v_val_347_) == 1)
{
uint8_t v_v_348_; 
v_v_348_ = lean_ctor_get_uint8(v_val_347_, 0);
lean_dec_ref_known(v_val_347_, 0);
return v_v_348_;
}
else
{
uint8_t v___x_349_; 
lean_dec(v_val_347_);
v___x_349_ = lean_unbox(v_defValue_343_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_350_, lean_object* v_opt_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_350_, v_opt_351_);
lean_dec_ref(v_opt_351_);
lean_dec_ref(v_opts_350_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_358_ = l_Lean_MessageData_ofFormat(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_359_, lean_object* v_macroStack_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_363_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_361_);
v___x_364_ = l_Lean_Elab_pp_macroStack;
v___x_365_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v___x_363_, v___x_364_);
lean_dec_ref(v___x_363_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v_macroStack_360_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_msgData_359_);
return v___x_366_;
}
else
{
if (lean_obj_tag(v_macroStack_360_) == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_msgData_359_);
return v___x_367_;
}
else
{
lean_object* v_head_368_; lean_object* v_after_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_384_; 
v_head_368_ = lean_ctor_get(v_macroStack_360_, 0);
lean_inc(v_head_368_);
v_after_369_ = lean_ctor_get(v_head_368_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_head_368_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_head_368_, 0);
lean_dec(v_unused_385_);
v___x_371_ = v_head_368_;
v_isShared_372_ = v_isSharedCheck_384_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_after_369_);
lean_dec(v_head_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_384_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 7);
lean_ctor_set(v___x_371_, 1, v___x_373_);
lean_ctor_set(v___x_371_, 0, v_msgData_359_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_msgData_359_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_383_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_msgData_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_376_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = l_Lean_MessageData_ofSyntax(v_after_369_);
v___x_379_ = l_Lean_indentD(v___x_378_);
v_msgData_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_380_, 0, v___x_377_);
lean_ctor_set(v_msgData_380_, 1, v___x_379_);
v___x_381_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_380_, v_macroStack_360_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_386_, lean_object* v_macroStack_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_386_, v_macroStack_387_, v___y_388_);
lean_dec_ref(v___y_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_ref_399_; lean_object* v_macroStack_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_ref_399_ = lean_ctor_get(v___y_396_, 2);
v_macroStack_400_ = lean_ctor_get(v___y_392_, 1);
v___x_401_ = l_Lean_Elab_getBetterRef(v_ref_399_, v_macroStack_400_);
v___x_402_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_391_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
lean_inc(v_macroStack_400_);
v___x_404_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_403_, v_macroStack_400_, v___y_396_);
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_401_);
lean_ctor_set(v___x_409_, 1, v_a_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 1);
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_423_, size_t v_i_424_, size_t v_stop_425_, lean_object* v_b_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = lean_usize_dec_eq(v_i_424_, v_stop_425_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; size_t v___x_430_; size_t v___x_431_; 
v___x_428_ = lean_array_uget_borrowed(v_as_423_, v_i_424_);
lean_inc(v___x_428_);
v___x_429_ = l_Lean_NameSet_insert(v_b_426_, v___x_428_);
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_424_, v___x_430_);
v_i_424_ = v___x_431_;
v_b_426_ = v___x_429_;
goto _start;
}
else
{
return v_b_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_433_, lean_object* v_i_434_, lean_object* v_stop_435_, lean_object* v_b_436_){
_start:
{
size_t v_i_boxed_437_; size_t v_stop_boxed_438_; lean_object* v_res_439_; 
v_i_boxed_437_ = lean_unbox_usize(v_i_434_);
lean_dec(v_i_434_);
v_stop_boxed_438_ = lean_unbox_usize(v_stop_435_);
lean_dec(v_stop_435_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_433_, v_i_boxed_437_, v_stop_boxed_438_, v_b_436_);
lean_dec_ref(v_as_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_440_, size_t v_i_441_, lean_object* v_bs_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_443_ == 0)
{
return v_bs_442_;
}
else
{
lean_object* v_v_444_; lean_object* v___x_445_; lean_object* v_bs_x27_446_; lean_object* v___x_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v_v_444_ = lean_array_uget(v_bs_442_, v_i_441_);
v___x_445_ = lean_unsigned_to_nat(0u);
v_bs_x27_446_ = lean_array_uset(v_bs_442_, v_i_441_, v___x_445_);
v___x_447_ = l_Lean_TSyntax_getId(v_v_444_);
lean_dec(v_v_444_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_441_, v___x_448_);
v___x_450_ = lean_array_uset(v_bs_x27_446_, v_i_441_, v___x_447_);
v_i_441_ = v___x_449_;
v_bs_442_ = v___x_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_bs_454_){
_start:
{
size_t v_sz_boxed_455_; size_t v_i_boxed_456_; lean_object* v_res_457_; 
v_sz_boxed_455_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_456_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_455_, v_i_boxed_456_, v_bs_454_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg(){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t v_sz_466_, size_t v_i_467_, lean_object* v_bs_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_lt(v_i_467_, v_sz_466_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v_bs_468_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v_bs_x27_472_; lean_object* v___x_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v_bs_x27_472_ = lean_array_uset(v_bs_468_, v_i_467_, v___x_471_);
v___x_473_ = lean_box(0);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_467_, v___x_474_);
v___x_476_ = lean_array_uset(v_bs_x27_472_, v_i_467_, v___x_473_);
v_i_467_ = v___x_475_;
v_bs_468_ = v___x_476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_sz_478_, lean_object* v_i_479_, lean_object* v_bs_480_){
_start:
{
size_t v_sz_boxed_481_; size_t v_i_boxed_482_; lean_object* v_res_483_; 
v_sz_boxed_481_ = lean_unbox_usize(v_sz_478_);
lean_dec(v_sz_478_);
v_i_boxed_482_ = lean_unbox_usize(v_i_479_);
lean_dec(v_i_479_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_boxed_481_, v_i_boxed_482_, v_bs_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_484_, uint8_t v___x_485_, lean_object* v_as_486_, size_t v_i_487_, size_t v_stop_488_, lean_object* v_b_489_){
_start:
{
lean_object* v___y_491_; uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_eq(v_i_487_, v_stop_488_);
if (v___x_495_ == 0)
{
lean_object* v_fst_496_; uint8_t v___x_497_; 
v_fst_496_ = lean_ctor_get(v_b_489_, 0);
v___x_497_ = lean_unbox(v_fst_496_);
if (v___x_497_ == 0)
{
lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v_snd_498_ = lean_ctor_get(v_b_489_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_b_489_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_b_489_, 0);
lean_dec(v_unused_507_);
v___x_500_ = v_b_489_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_dec(v_b_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_box(v___x_484_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_snd_498_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
v___y_491_ = v___x_504_;
goto v___jp_490_;
}
}
}
else
{
lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_snd_508_ = lean_ctor_get(v_b_489_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_b_489_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_b_489_, 0);
lean_dec(v_unused_519_);
v___x_510_ = v_b_489_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_dec(v_b_489_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_512_ = lean_array_uget_borrowed(v_as_486_, v_i_487_);
lean_inc(v___x_512_);
v___x_513_ = lean_array_push(v_snd_508_, v___x_512_);
v___x_514_ = lean_box(v___x_485_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_513_);
lean_ctor_set(v___x_510_, 0, v___x_514_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_513_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v___y_491_ = v___x_516_;
goto v___jp_490_;
}
}
}
}
else
{
return v_b_489_;
}
v___jp_490_:
{
size_t v___x_492_; size_t v___x_493_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_487_, v___x_492_);
v_i_487_ = v___x_493_;
v_b_489_ = v___y_491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v_as_522_, lean_object* v_i_523_, lean_object* v_stop_524_, lean_object* v_b_525_){
_start:
{
uint8_t v___x_173150__boxed_526_; uint8_t v___x_173151__boxed_527_; size_t v_i_boxed_528_; size_t v_stop_boxed_529_; lean_object* v_res_530_; 
v___x_173150__boxed_526_ = lean_unbox(v___x_520_);
v___x_173151__boxed_527_ = lean_unbox(v___x_521_);
v_i_boxed_528_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_stop_boxed_529_ = lean_unbox_usize(v_stop_524_);
lean_dec(v_stop_524_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_173150__boxed_526_, v___x_173151__boxed_527_, v_as_522_, v_i_boxed_528_, v_stop_boxed_529_, v_b_525_);
lean_dec_ref(v_as_522_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_531_, lean_object* v___y_532_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_a_533_);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v_a_533_);
lean_ctor_set(v___x_534_, 1, v___y_532_);
return v___x_534_;
}
else
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_a_535_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_535_);
lean_ctor_set(v___x_536_, 1, v___y_532_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_537_, v___y_538_);
lean_dec_ref(v_x_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_540_, lean_object* v_stx_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_540_, v_stx_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
if (lean_obj_tag(v_a_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_554_; 
v_a_546_ = lean_ctor_get(v___x_544_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_544_, 0);
lean_dec(v_unused_555_);
v___x_548_ = v___x_544_;
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_box(0);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_a_546_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_584_; 
v_val_556_ = lean_ctor_get(v_a_545_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_584_ == 0)
{
v___x_558_ = v_a_545_;
v_isShared_559_ = v_isSharedCheck_584_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_dec(v_a_545_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_584_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_snd_560_; 
v_snd_560_ = lean_ctor_get(v_val_556_, 1);
lean_inc(v_snd_560_);
lean_dec(v_val_556_);
if (lean_obj_tag(v_snd_560_) == 0)
{
lean_object* v_a_561_; lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_558_);
v_a_561_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_544_, 2);
v_a_562_ = lean_ctor_get(v_snd_560_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_snd_560_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v_snd_560_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v_snd_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_567_, v_a_561_);
lean_dec_ref(v___x_567_);
return v___x_568_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_583_; 
v_a_571_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_544_, 2);
v_a_572_ = lean_ctor_get(v_snd_560_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_560_);
if (v_isSharedCheck_583_ == 0)
{
v___x_574_ = v_snd_560_;
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v_snd_560_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_a_572_);
v___x_577_ = v___x_558_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_582_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_577_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_579_, v_a_571_);
lean_dec_ref(v___x_579_);
return v___x_580_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_585_ = lean_ctor_get(v___x_544_, 0);
v_a_586_ = lean_ctor_get(v___x_544_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_544_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_inc(v_a_585_);
lean_dec(v___x_544_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_585_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_594_, lean_object* v_stx_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_594_, v_stx_595_, v___y_596_, v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_598_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l_Lean_maxRecDepthErrorMessage;
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_607_ = l_Lean_MessageData_ofFormat(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_609_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_610_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_611_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_ref_611_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_619_, lean_object* v_declName_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_623_; lean_object* v_env_624_; lean_object* v___x_625_; uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_623_ = 0;
v_env_624_ = l_Lean_Environment_setExporting(v_env_619_, v___x_623_);
lean_inc(v_declName_620_);
v___x_625_ = l_Lean_mkPrivateName(v_env_624_, v_declName_620_);
v___x_626_ = 1;
lean_inc_ref(v_env_624_);
v___x_627_ = l_Lean_Environment_contains(v_env_624_, v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = l_Lean_privateToUserName(v_declName_620_);
v___x_629_ = l_Lean_Environment_contains(v_env_624_, v___x_628_, v___x_626_);
v___x_630_ = lean_box(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___y_622_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v_env_624_);
lean_dec(v_declName_620_);
v___x_632_ = lean_box(v___x_627_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___y_622_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_634_, lean_object* v_declName_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_634_, v_declName_635_, v___y_636_, v___y_637_);
lean_dec_ref(v___y_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_639_, lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_toCold_648_; lean_object* v_currRecDepth_649_; lean_object* v_ref_650_; uint16_t v_optionFlags_651_; uint8_t v_suppressElabErrors_652_; uint8_t v_isRecordingDeps_653_; lean_object* v_ref_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_toCold_648_ = lean_ctor_get(v___y_645_, 0);
v_currRecDepth_649_ = lean_ctor_get(v___y_645_, 1);
v_ref_650_ = lean_ctor_get(v___y_645_, 2);
v_optionFlags_651_ = lean_ctor_get_uint16(v___y_645_, sizeof(void*)*3);
v_suppressElabErrors_652_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3 + 2);
v_isRecordingDeps_653_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3 + 3);
v_ref_654_ = l_Lean_replaceRef(v_ref_639_, v_ref_650_);
lean_inc(v_currRecDepth_649_);
lean_inc_ref(v_toCold_648_);
v___x_655_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_655_, 0, v_toCold_648_);
lean_ctor_set(v___x_655_, 1, v_currRecDepth_649_);
lean_ctor_set(v___x_655_, 2, v_ref_654_);
lean_ctor_set_uint16(v___x_655_, sizeof(void*)*3, v_optionFlags_651_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3 + 2, v_suppressElabErrors_652_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3 + 3, v_isRecordingDeps_653_);
v___x_656_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___x_655_, v___y_646_);
lean_dec_ref_known(v___x_655_, 3);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_657_, v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v_ref_657_);
return v_res_666_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_667_; double v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_float_of_nat(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_ref_679_; lean_object* v___x_680_; lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_726_; 
v_ref_679_ = lean_ctor_get(v___y_676_, 2);
v___x_680_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_726_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_726_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_726_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v_traceState_686_; lean_object* v_env_687_; lean_object* v_nextMacroScope_688_; lean_object* v_ngen_689_; lean_object* v_auxDeclNGen_690_; lean_object* v_cache_691_; lean_object* v_recordedDeps_692_; lean_object* v_messages_693_; lean_object* v_infoState_694_; lean_object* v_snapshotTasks_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_725_; 
v___x_685_ = lean_st_ref_take(v___y_677_);
v_traceState_686_ = lean_ctor_get(v___x_685_, 4);
v_env_687_ = lean_ctor_get(v___x_685_, 0);
v_nextMacroScope_688_ = lean_ctor_get(v___x_685_, 1);
v_ngen_689_ = lean_ctor_get(v___x_685_, 2);
v_auxDeclNGen_690_ = lean_ctor_get(v___x_685_, 3);
v_cache_691_ = lean_ctor_get(v___x_685_, 5);
v_recordedDeps_692_ = lean_ctor_get(v___x_685_, 6);
v_messages_693_ = lean_ctor_get(v___x_685_, 7);
v_infoState_694_ = lean_ctor_get(v___x_685_, 8);
v_snapshotTasks_695_ = lean_ctor_get(v___x_685_, 9);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_725_ == 0)
{
v___x_697_ = v___x_685_;
v_isShared_698_ = v_isSharedCheck_725_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snapshotTasks_695_);
lean_inc(v_infoState_694_);
lean_inc(v_messages_693_);
lean_inc(v_recordedDeps_692_);
lean_inc(v_cache_691_);
lean_inc(v_traceState_686_);
lean_inc(v_auxDeclNGen_690_);
lean_inc(v_ngen_689_);
lean_inc(v_nextMacroScope_688_);
lean_inc(v_env_687_);
lean_dec(v___x_685_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_725_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
uint64_t v_tid_699_; lean_object* v_traces_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_724_; 
v_tid_699_ = lean_ctor_get_uint64(v_traceState_686_, sizeof(void*)*1);
v_traces_700_ = lean_ctor_get(v_traceState_686_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_traceState_686_);
if (v_isSharedCheck_724_ == 0)
{
v___x_702_ = v_traceState_686_;
v_isShared_703_ = v_isSharedCheck_724_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_traces_700_);
lean_dec(v_traceState_686_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_724_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; double v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_box(0);
v___x_706_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_707_ = 0;
v___x_708_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_709_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_709_, 0, v_cls_672_);
lean_ctor_set(v___x_709_, 1, v___x_705_);
lean_ctor_set(v___x_709_, 2, v___x_708_);
lean_ctor_set_float(v___x_709_, sizeof(void*)*3, v___x_706_);
lean_ctor_set_float(v___x_709_, sizeof(void*)*3 + 8, v___x_706_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*3 + 16, v___x_707_);
v___x_710_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_711_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v_a_681_);
lean_ctor_set(v___x_711_, 2, v___x_710_);
lean_inc(v_ref_679_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_ref_679_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_PersistentArray_push___redArg(v_traces_700_, v___x_712_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_713_);
v___x_715_ = v___x_702_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_713_);
lean_ctor_set_uint64(v_reuseFailAlloc_723_, sizeof(void*)*1, v_tid_699_);
v___x_715_ = v_reuseFailAlloc_723_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 4, v___x_715_);
v___x_717_ = v___x_697_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_env_687_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_nextMacroScope_688_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_ngen_689_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_auxDeclNGen_690_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_722_, 5, v_cache_691_);
lean_ctor_set(v_reuseFailAlloc_722_, 6, v_recordedDeps_692_);
lean_ctor_set(v_reuseFailAlloc_722_, 7, v_messages_693_);
lean_ctor_set(v_reuseFailAlloc_722_, 8, v_infoState_694_);
lean_ctor_set(v_reuseFailAlloc_722_, 9, v_snapshotTasks_695_);
v___x_717_ = v_reuseFailAlloc_722_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_st_ref_put(v___y_677_, v___x_717_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_704_);
v___x_720_ = v___x_683_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_704_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_727_, lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_727_, v_msg_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
if (lean_obj_tag(v_as_738_) == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
else
{
lean_object* v_toCold_748_; lean_object* v_options_749_; uint8_t v_hasTrace_750_; 
v_toCold_748_ = lean_ctor_get(v___y_743_, 0);
v_options_749_ = lean_ctor_get(v_toCold_748_, 2);
v_hasTrace_750_ = lean_ctor_get_uint8(v_options_749_, sizeof(void*)*1);
if (v_hasTrace_750_ == 0)
{
lean_object* v_tail_751_; 
v_tail_751_ = lean_ctor_get(v_as_738_, 1);
lean_inc(v_tail_751_);
lean_dec_ref_known(v_as_738_, 2);
v_as_738_ = v_tail_751_;
goto _start;
}
else
{
lean_object* v_head_753_; lean_object* v_tail_754_; lean_object* v_fst_755_; lean_object* v_snd_756_; lean_object* v_inheritedTraceOptions_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_head_753_ = lean_ctor_get(v_as_738_, 0);
lean_inc(v_head_753_);
v_tail_754_ = lean_ctor_get(v_as_738_, 1);
lean_inc(v_tail_754_);
lean_dec_ref_known(v_as_738_, 2);
v_fst_755_ = lean_ctor_get(v_head_753_, 0);
lean_inc_n(v_fst_755_, 2);
v_snd_756_ = lean_ctor_get(v_head_753_, 1);
lean_inc(v_snd_756_);
lean_dec(v_head_753_);
v_inheritedTraceOptions_757_ = lean_ctor_get(v_toCold_748_, 11);
v___x_758_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_759_ = l_Lean_Name_append(v___x_758_, v_fst_755_);
v___x_760_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_757_, v_options_749_, v___x_759_);
lean_dec(v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v_snd_756_);
lean_dec(v_fst_755_);
v_as_738_ = v_tail_754_;
goto _start;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_762_, 0, v_snd_756_);
v___x_763_ = l_Lean_MessageData_ofFormat(v___x_762_);
v___x_764_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_755_, v___x_763_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_dec_ref_known(v___x_764_, 1);
v_as_738_ = v_tail_754_;
goto _start;
}
else
{
lean_dec(v_tail_754_);
return v___x_764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_box(0);
return v___x_777_;
}
else
{
lean_object* v_key_778_; lean_object* v_value_779_; lean_object* v_tail_780_; uint8_t v___x_781_; 
v_key_778_ = lean_ctor_get(v_x_776_, 0);
v_value_779_ = lean_ctor_get(v_x_776_, 1);
v_tail_780_ = lean_ctor_get(v_x_776_, 2);
v___x_781_ = lean_name_eq(v_key_778_, v_a_775_);
if (v___x_781_ == 0)
{
v_x_776_ = v_tail_780_;
goto _start;
}
else
{
lean_object* v___x_783_; 
lean_inc(v_value_779_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v_value_779_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_784_, lean_object* v_x_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_784_, v_x_785_);
lean_dec(v_x_785_);
lean_dec(v_a_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_buckets_789_; lean_object* v___x_790_; uint64_t v___y_792_; 
v_buckets_789_ = lean_ctor_get(v_m_787_, 1);
v___x_790_ = lean_array_get_size(v_buckets_789_);
if (lean_obj_tag(v_a_788_) == 0)
{
uint64_t v___x_806_; 
v___x_806_ = 1723ULL;
v___y_792_ = v___x_806_;
goto v___jp_791_;
}
else
{
uint64_t v_hash_807_; 
v_hash_807_ = lean_ctor_get_uint64(v_a_788_, sizeof(void*)*2);
v___y_792_ = v_hash_807_;
goto v___jp_791_;
}
v___jp_791_:
{
uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v_fold_795_; uint64_t v___x_796_; uint64_t v___x_797_; uint64_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_793_ = 32ULL;
v___x_794_ = lean_uint64_shift_right(v___y_792_, v___x_793_);
v_fold_795_ = lean_uint64_xor(v___y_792_, v___x_794_);
v___x_796_ = 16ULL;
v___x_797_ = lean_uint64_shift_right(v_fold_795_, v___x_796_);
v___x_798_ = lean_uint64_xor(v_fold_795_, v___x_797_);
v___x_799_ = lean_uint64_to_usize(v___x_798_);
v___x_800_ = lean_usize_of_nat(v___x_790_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_sub(v___x_800_, v___x_801_);
v___x_803_ = lean_usize_land(v___x_799_, v___x_802_);
v___x_804_ = lean_array_uget_borrowed(v_buckets_789_, v___x_803_);
v___x_805_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_788_, v___x_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_m_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0(lean_object* v___x_811_, lean_object* v_entry_812_, lean_object* v_s_813_){
_start:
{
lean_object* v_addEntryFn_814_; lean_object* v_importedEntries_815_; lean_object* v_state_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_addEntryFn_814_ = lean_ctor_get(v___x_811_, 3);
lean_inc(v_addEntryFn_814_);
lean_dec_ref(v___x_811_);
v_importedEntries_815_ = lean_ctor_get(v_s_813_, 0);
v_state_816_ = lean_ctor_get(v_s_813_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_s_813_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v_s_813_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_state_816_);
lean_inc(v_importedEntries_815_);
lean_dec(v_s_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_state_820_; lean_object* v___x_822_; 
v_state_820_ = lean_apply_2(v_addEntryFn_814_, v_state_816_, v_entry_812_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v_state_820_);
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_importedEntries_815_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_state_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_825_, lean_object* v_i_826_, lean_object* v_k_827_){
_start:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = lean_array_get_size(v_keys_825_);
v___x_829_ = lean_nat_dec_lt(v_i_826_, v___x_828_);
if (v___x_829_ == 0)
{
lean_dec(v_i_826_);
return v___x_829_;
}
else
{
lean_object* v_k_x27_830_; uint8_t v___x_831_; 
v_k_x27_830_ = lean_array_fget_borrowed(v_keys_825_, v_i_826_);
v___x_831_ = l_Lean_instBEqExtraModUse_beq(v_k_827_, v_k_x27_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = lean_nat_add(v_i_826_, v___x_832_);
lean_dec(v_i_826_);
v_i_826_ = v___x_833_;
goto _start;
}
else
{
lean_dec(v_i_826_);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_835_, lean_object* v_i_836_, lean_object* v_k_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_835_, v_i_836_, v_k_837_);
lean_dec_ref(v_k_837_);
lean_dec_ref(v_keys_835_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_840_, size_t v_x_841_, lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v_es_843_; lean_object* v___x_844_; size_t v___x_845_; size_t v___x_846_; lean_object* v_j_847_; lean_object* v___x_848_; 
v_es_843_ = lean_ctor_get(v_x_840_, 0);
v___x_844_ = lean_box(2);
v___x_845_ = ((size_t)31ULL);
v___x_846_ = lean_usize_land(v_x_841_, v___x_845_);
v_j_847_ = lean_usize_to_nat(v___x_846_);
v___x_848_ = lean_array_get_borrowed(v___x_844_, v_es_843_, v_j_847_);
lean_dec(v_j_847_);
switch(lean_obj_tag(v___x_848_))
{
case 0:
{
lean_object* v_key_849_; uint8_t v___x_850_; 
v_key_849_ = lean_ctor_get(v___x_848_, 0);
v___x_850_ = l_Lean_instBEqExtraModUse_beq(v_x_842_, v_key_849_);
return v___x_850_;
}
case 1:
{
lean_object* v_node_851_; size_t v___x_852_; size_t v___x_853_; 
v_node_851_ = lean_ctor_get(v___x_848_, 0);
v___x_852_ = ((size_t)5ULL);
v___x_853_ = lean_usize_shift_right(v_x_841_, v___x_852_);
v_x_840_ = v_node_851_;
v_x_841_ = v___x_853_;
goto _start;
}
default: 
{
uint8_t v___x_855_; 
v___x_855_ = 0;
return v___x_855_;
}
}
}
else
{
lean_object* v_ks_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_ks_856_ = lean_ctor_get(v_x_840_, 0);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_856_, v___x_857_, v_x_842_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
size_t v_x_173678__boxed_862_; uint8_t v_res_863_; lean_object* v_r_864_; 
v_x_173678__boxed_862_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_res_863_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_859_, v_x_173678__boxed_862_, v_x_861_);
lean_dec_ref(v_x_861_);
lean_dec_ref(v_x_859_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
uint64_t v___x_867_; size_t v___x_868_; uint8_t v___x_869_; 
v___x_867_ = l_Lean_instHashableExtraModUse_hash(v_x_866_);
v___x_868_ = lean_uint64_to_usize(v___x_867_);
v___x_869_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_865_, v___x_868_, v_x_866_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_870_, v_x_871_);
lean_dec_ref(v_x_871_);
lean_dec_ref(v_x_870_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0(void){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_880_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
lean_ctor_set(v___x_880_, 2, v___x_879_);
lean_ctor_set(v___x_880_, 3, v___x_879_);
lean_ctor_set(v___x_880_, 4, v___x_879_);
lean_ctor_set(v___x_880_, 5, v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v_cls_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_cls_893_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_894_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_895_ = l_Lean_Name_append(v___x_894_, v_cls_893_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13));
v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_906_, uint8_t v_isMeta_907_, lean_object* v_hint_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_env_950_; uint8_t v_isExporting_951_; lean_object* v_entry_952_; lean_object* v___x_953_; lean_object* v_env_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_948_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_949_ = lean_st_ref_get(v___y_914_);
v_env_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_env_950_);
lean_dec(v___x_949_);
v_isExporting_951_ = lean_ctor_get_uint8(v_env_950_, sizeof(void*)*13);
lean_dec_ref(v_env_950_);
lean_inc(v_mod_906_);
v_entry_952_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_952_, 0, v_mod_906_);
lean_ctor_set_uint8(v_entry_952_, sizeof(void*)*1, v_isExporting_951_);
lean_ctor_set_uint8(v_entry_952_, sizeof(void*)*1 + 1, v_isMeta_907_);
v___x_953_ = lean_st_ref_get(v___y_914_);
v_env_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc_ref(v_env_954_);
lean_dec(v___x_953_);
v___x_955_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_956_ = lean_box(1);
v___x_957_ = lean_box(0);
v___x_958_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_948_, v___x_955_, v_env_954_, v___x_956_, v___x_957_);
v___x_959_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_958_, v_entry_952_);
lean_dec(v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v_toCold_960_; lean_object* v_options_961_; lean_object* v_inheritedTraceOptions_962_; uint8_t v_hasTrace_963_; lean_object* v___f_964_; uint8_t v___x_965_; lean_object* v___y_967_; lean_object* v___y_968_; 
v_toCold_960_ = lean_ctor_get(v___y_913_, 0);
v_options_961_ = lean_ctor_get(v_toCold_960_, 2);
v_inheritedTraceOptions_962_ = lean_ctor_get(v_toCold_960_, 11);
v_hasTrace_963_ = lean_ctor_get_uint8(v_options_961_, sizeof(void*)*1);
v___f_964_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0), 3, 2);
lean_closure_set(v___f_964_, 0, v___x_955_);
lean_closure_set(v___f_964_, 1, v_entry_952_);
v___x_965_ = 1;
if (v_hasTrace_963_ == 0)
{
lean_dec(v_hint_908_);
lean_dec(v_mod_906_);
v___y_967_ = v___y_912_;
v___y_968_ = v___y_914_;
goto v___jp_966_;
}
else
{
lean_object* v_cls_995_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_cls_995_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_1015_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_1016_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_962_, v_options_961_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_dec(v_hint_908_);
lean_dec(v_mod_906_);
v___y_967_ = v___y_912_;
v___y_968_ = v___y_914_;
goto v___jp_966_;
}
else
{
lean_object* v___x_1017_; lean_object* v___y_1019_; 
v___x_1017_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
if (v_isExporting_951_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_1019_ = v___x_1026_;
goto v___jp_1018_;
}
else
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_1019_ = v___x_1027_;
goto v___jp_1018_;
}
v___jp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_inc_ref(v___y_1019_);
v___x_1020_ = l_Lean_stringToMessageData(v___y_1019_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1017_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
if (v_isMeta_907_ == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___y_1002_ = v___x_1023_;
v___y_1003_ = v___x_1024_;
goto v___jp_1001_;
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18));
v___y_1002_ = v___x_1023_;
v___y_1003_ = v___x_1025_;
goto v___jp_1001_;
}
}
}
v___jp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___y_997_);
lean_ctor_set(v___x_999_, 1, v___y_998_);
v___x_1000_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_995_, v___x_999_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_dec_ref_known(v___x_1000_, 1);
v___y_967_ = v___y_912_;
v___y_968_ = v___y_914_;
goto v___jp_966_;
}
else
{
lean_dec_ref(v___f_964_);
return v___x_1000_;
}
}
v___jp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
lean_inc_ref(v___y_1003_);
v___x_1004_ = l_Lean_stringToMessageData(v___y_1003_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___y_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_MessageData_ofName(v_mod_906_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_Name_isAnonymous(v_hint_908_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_1012_ = l_Lean_MessageData_ofName(v_hint_908_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___y_997_ = v___x_1009_;
v___y_998_ = v___x_1013_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1014_; 
lean_dec(v_hint_908_);
v___x_1014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11);
v___y_997_ = v___x_1009_;
v___y_998_ = v___x_1014_;
goto v___jp_996_;
}
}
}
v___jp_966_:
{
lean_object* v___x_969_; lean_object* v_toEnvExtension_970_; uint8_t v_logWrites_971_; 
v___x_969_ = lean_st_ref_take(v___y_968_);
v_toEnvExtension_970_ = lean_ctor_get(v___x_955_, 0);
v_logWrites_971_ = lean_ctor_get_uint8(v_toEnvExtension_970_, sizeof(void*)*6);
if (v_logWrites_971_ == 0)
{
lean_object* v_env_972_; lean_object* v_nextMacroScope_973_; lean_object* v_ngen_974_; lean_object* v_auxDeclNGen_975_; lean_object* v_traceState_976_; lean_object* v_recordedDeps_977_; lean_object* v_messages_978_; lean_object* v_infoState_979_; lean_object* v_snapshotTasks_980_; lean_object* v_asyncMode_981_; lean_object* v___x_982_; 
v_env_972_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_972_);
v_nextMacroScope_973_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_nextMacroScope_973_);
v_ngen_974_ = lean_ctor_get(v___x_969_, 2);
lean_inc_ref(v_ngen_974_);
v_auxDeclNGen_975_ = lean_ctor_get(v___x_969_, 3);
lean_inc_ref(v_auxDeclNGen_975_);
v_traceState_976_ = lean_ctor_get(v___x_969_, 4);
lean_inc_ref(v_traceState_976_);
v_recordedDeps_977_ = lean_ctor_get(v___x_969_, 6);
lean_inc_ref(v_recordedDeps_977_);
v_messages_978_ = lean_ctor_get(v___x_969_, 7);
lean_inc_ref(v_messages_978_);
v_infoState_979_ = lean_ctor_get(v___x_969_, 8);
lean_inc_ref(v_infoState_979_);
v_snapshotTasks_980_ = lean_ctor_get(v___x_969_, 9);
lean_inc_ref(v_snapshotTasks_980_);
lean_dec(v___x_969_);
v_asyncMode_981_ = lean_ctor_get(v_toEnvExtension_970_, 2);
lean_inc_ref(v_toEnvExtension_970_);
v___x_982_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_970_, v_env_972_, v___f_964_, v_asyncMode_981_, v___x_957_, v___x_965_);
v___y_917_ = v___y_968_;
v___y_918_ = v_auxDeclNGen_975_;
v___y_919_ = v_messages_978_;
v___y_920_ = v_nextMacroScope_973_;
v___y_921_ = v_recordedDeps_977_;
v___y_922_ = v___y_967_;
v___y_923_ = v_infoState_979_;
v___y_924_ = v_traceState_976_;
v___y_925_ = v_ngen_974_;
v___y_926_ = v_snapshotTasks_980_;
v___y_927_ = v___x_982_;
goto v___jp_916_;
}
else
{
lean_object* v_env_983_; lean_object* v_nextMacroScope_984_; lean_object* v_ngen_985_; lean_object* v_auxDeclNGen_986_; lean_object* v_traceState_987_; lean_object* v_recordedDeps_988_; lean_object* v_messages_989_; lean_object* v_infoState_990_; lean_object* v_snapshotTasks_991_; lean_object* v_asyncMode_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_env_983_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_983_);
v_nextMacroScope_984_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_nextMacroScope_984_);
v_ngen_985_ = lean_ctor_get(v___x_969_, 2);
lean_inc_ref(v_ngen_985_);
v_auxDeclNGen_986_ = lean_ctor_get(v___x_969_, 3);
lean_inc_ref(v_auxDeclNGen_986_);
v_traceState_987_ = lean_ctor_get(v___x_969_, 4);
lean_inc_ref(v_traceState_987_);
v_recordedDeps_988_ = lean_ctor_get(v___x_969_, 6);
lean_inc_ref(v_recordedDeps_988_);
v_messages_989_ = lean_ctor_get(v___x_969_, 7);
lean_inc_ref(v_messages_989_);
v_infoState_990_ = lean_ctor_get(v___x_969_, 8);
lean_inc_ref(v_infoState_990_);
v_snapshotTasks_991_ = lean_ctor_get(v___x_969_, 9);
lean_inc_ref(v_snapshotTasks_991_);
lean_dec(v___x_969_);
v_asyncMode_992_ = lean_ctor_get(v_toEnvExtension_970_, 2);
lean_inc_ref_n(v_toEnvExtension_970_, 2);
v___x_993_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_970_, v_env_983_);
lean_dec_ref(v_env_983_);
v___x_994_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_970_, v___x_993_, v___f_964_, v_asyncMode_992_, v___x_957_, v___x_965_);
v___y_917_ = v___y_968_;
v___y_918_ = v_auxDeclNGen_986_;
v___y_919_ = v_messages_989_;
v___y_920_ = v_nextMacroScope_984_;
v___y_921_ = v_recordedDeps_988_;
v___y_922_ = v___y_967_;
v___y_923_ = v_infoState_990_;
v___y_924_ = v_traceState_987_;
v___y_925_ = v_ngen_985_;
v___y_926_ = v_snapshotTasks_991_;
v___y_927_ = v___x_994_;
goto v___jp_916_;
}
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref_known(v_entry_952_, 1);
lean_dec(v_hint_908_);
lean_dec(v_mod_906_);
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
v___jp_916_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_mctx_932_; lean_object* v_zetaDeltaFVarIds_933_; lean_object* v_postponed_934_; lean_object* v_diag_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_946_; 
v___x_928_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
v___x_929_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_929_, 0, v___y_927_);
lean_ctor_set(v___x_929_, 1, v___y_920_);
lean_ctor_set(v___x_929_, 2, v___y_925_);
lean_ctor_set(v___x_929_, 3, v___y_918_);
lean_ctor_set(v___x_929_, 4, v___y_924_);
lean_ctor_set(v___x_929_, 5, v___x_928_);
lean_ctor_set(v___x_929_, 6, v___y_921_);
lean_ctor_set(v___x_929_, 7, v___y_919_);
lean_ctor_set(v___x_929_, 8, v___y_923_);
lean_ctor_set(v___x_929_, 9, v___y_926_);
v___x_930_ = lean_st_ref_put(v___y_917_, v___x_929_);
v___x_931_ = lean_st_ref_take(v___y_922_);
v_mctx_932_ = lean_ctor_get(v___x_931_, 0);
v_zetaDeltaFVarIds_933_ = lean_ctor_get(v___x_931_, 2);
v_postponed_934_ = lean_ctor_get(v___x_931_, 3);
v_diag_935_ = lean_ctor_get(v___x_931_, 4);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___x_931_, 1);
lean_dec(v_unused_947_);
v___x_937_ = v___x_931_;
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_diag_935_);
lean_inc(v_postponed_934_);
lean_inc(v_zetaDeltaFVarIds_933_);
lean_inc(v_mctx_932_);
lean_dec(v___x_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_939_ = lean_box(0);
v___x_940_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_mctx_932_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_zetaDeltaFVarIds_933_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_postponed_934_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_diag_935_);
v___x_942_ = v_reuseFailAlloc_945_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_st_ref_put(v___y_922_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_939_);
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_1030_, lean_object* v_isMeta_1031_, lean_object* v_hint_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_isMeta_boxed_1040_; lean_object* v_res_1041_; 
v_isMeta_boxed_1040_ = lean_unbox(v_isMeta_1031_);
v_res_1041_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_1030_, v_isMeta_boxed_1040_, v_hint_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1042_, lean_object* v_declName_1043_, lean_object* v_as_1044_, size_t v_sz_1045_, size_t v_i_1046_, lean_object* v_b_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_usize_dec_lt(v_i_1046_, v_sz_1045_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
lean_dec(v_declName_1043_);
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_b_1047_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v_modules_1058_; lean_object* v___x_1059_; lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v_toImport_1062_; lean_object* v_module_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; 
v___x_1057_ = l_Lean_Environment_header(v___x_1042_);
v_modules_1058_ = lean_ctor_get(v___x_1057_, 3);
lean_inc_ref(v_modules_1058_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1060_ = lean_array_uget_borrowed(v_as_1044_, v_i_1046_);
v___x_1061_ = lean_array_get(v___x_1059_, v_modules_1058_, v_a_1060_);
lean_dec_ref(v_modules_1058_);
v_toImport_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc_ref(v_toImport_1062_);
lean_dec(v___x_1061_);
v_module_1063_ = lean_ctor_get(v_toImport_1062_, 0);
lean_inc(v_module_1063_);
lean_dec_ref(v_toImport_1062_);
v___x_1064_ = lean_box(0);
v___x_1065_ = 0;
lean_inc(v_declName_1043_);
v___x_1066_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1063_, v___x_1065_, v_declName_1043_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1066_) == 0)
{
size_t v___x_1067_; size_t v___x_1068_; 
lean_dec_ref_known(v___x_1066_, 1);
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_add(v_i_1046_, v___x_1067_);
v_i_1046_ = v___x_1068_;
v_b_1047_ = v___x_1064_;
goto _start;
}
else
{
lean_dec(v_declName_1043_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1070_, lean_object* v_declName_1071_, lean_object* v_as_1072_, lean_object* v_sz_1073_, lean_object* v_i_1074_, lean_object* v_b_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
size_t v_sz_boxed_1083_; size_t v_i_boxed_1084_; lean_object* v_res_1085_; 
v_sz_boxed_1083_ = lean_unbox_usize(v_sz_1073_);
lean_dec(v_sz_1073_);
v_i_boxed_1084_ = lean_unbox_usize(v_i_1074_);
lean_dec(v_i_1074_);
v_res_1085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1070_, v_declName_1071_, v_as_1072_, v_sz_boxed_1083_, v_i_boxed_1084_, v_b_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec_ref(v_as_1072_);
lean_dec_ref(v___x_1070_);
return v_res_1085_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1089_, uint8_t v_isMeta_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_env_1103_; lean_object* v___y_1105_; lean_object* v___x_1118_; 
v___x_1098_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0);
v___x_1099_ = lean_st_ref_get(v___y_1096_);
v_env_1103_ = lean_ctor_get(v___x_1099_, 0);
lean_inc_ref(v_env_1103_);
lean_dec(v___x_1099_);
v___x_1118_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1103_, v_declName_1089_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1089_);
goto v___jp_1100_;
}
else
{
lean_object* v_val_1119_; lean_object* v___x_1120_; lean_object* v_modules_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_val_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_val_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = l_Lean_Environment_header(v_env_1103_);
v_modules_1121_ = lean_ctor_get(v___x_1120_, 3);
lean_inc_ref(v_modules_1121_);
lean_dec_ref(v___x_1120_);
v___x_1122_ = lean_array_get_size(v_modules_1121_);
v___x_1123_ = lean_nat_dec_lt(v_val_1119_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_dec_ref(v_modules_1121_);
lean_dec(v_val_1119_);
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1089_);
goto v___jp_1100_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___y_1127_; 
v___x_1124_ = lean_array_fget(v_modules_1121_, v_val_1119_);
lean_dec(v_val_1119_);
lean_dec_ref(v_modules_1121_);
v___x_1125_ = lean_st_ref_get(v___y_1096_);
if (v_isMeta_1090_ == 0)
{
lean_dec(v___x_1125_);
v___y_1127_ = v_isMeta_1090_;
goto v___jp_1126_;
}
else
{
lean_object* v_env_1138_; uint8_t v___x_1139_; 
v_env_1138_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_env_1138_);
lean_dec(v___x_1125_);
lean_inc(v_declName_1089_);
v___x_1139_ = l_Lean_isMarkedMeta(v_env_1138_, v_declName_1089_);
if (v___x_1139_ == 0)
{
v___y_1127_ = v_isMeta_1090_;
goto v___jp_1126_;
}
else
{
uint8_t v___x_1140_; 
v___x_1140_ = 0;
v___y_1127_ = v___x_1140_;
goto v___jp_1126_;
}
}
v___jp_1126_:
{
lean_object* v_toImport_1128_; lean_object* v_module_1129_; lean_object* v___x_1130_; 
v_toImport_1128_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_ref(v_toImport_1128_);
lean_dec(v___x_1124_);
v_module_1129_ = lean_ctor_get(v_toImport_1128_, 0);
lean_inc(v_module_1129_);
lean_dec_ref(v_toImport_1128_);
lean_inc(v_declName_1089_);
v___x_1130_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1129_, v___y_1127_, v_declName_1089_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref_known(v___x_1130_, 1);
v___x_1131_ = l_Lean_indirectModUseExt;
v___x_1132_ = lean_box(1);
v___x_1133_ = lean_box(0);
lean_inc_ref(v_env_1103_);
v___x_1134_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1098_, v___x_1131_, v_env_1103_, v___x_1132_, v___x_1133_);
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1134_, v_declName_1089_);
lean_dec(v___x_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___y_1105_ = v___x_1136_;
goto v___jp_1104_;
}
else
{
lean_object* v_val_1137_; 
v_val_1137_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1137_);
lean_dec_ref_known(v___x_1135_, 1);
v___y_1105_ = v_val_1137_;
goto v___jp_1104_;
}
}
else
{
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1089_);
return v___x_1130_;
}
}
}
}
v___jp_1100_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
v___jp_1104_:
{
lean_object* v___x_1106_; size_t v_sz_1107_; size_t v___x_1108_; lean_object* v___x_1109_; 
v___x_1106_ = lean_box(0);
v_sz_1107_ = lean_array_size(v___y_1105_);
v___x_1108_ = ((size_t)0ULL);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1103_, v_declName_1089_, v___y_1105_, v_sz_1107_, v___x_1108_, v___x_1106_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_env_1103_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v___x_1109_, 0);
lean_dec(v_unused_1117_);
v___x_1111_ = v___x_1109_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v___x_1109_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1106_);
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1106_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1141_, lean_object* v_isMeta_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v_isMeta_boxed_1150_; lean_object* v_res_1151_; 
v_isMeta_boxed_1150_ = lean_unbox(v_isMeta_1142_);
v_res_1151_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1141_, v_isMeta_boxed_1150_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
if (lean_obj_tag(v_as_x27_1152_) == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_b_1153_);
return v___x_1161_;
}
else
{
lean_object* v_head_1162_; lean_object* v_tail_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; 
v_head_1162_ = lean_ctor_get(v_as_x27_1152_, 0);
v_tail_1163_ = lean_ctor_get(v_as_x27_1152_, 1);
v___x_1164_ = lean_box(0);
v___x_1165_ = 1;
lean_inc(v_head_1162_);
v___x_1166_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1162_, v___x_1165_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_dec_ref_known(v___x_1166_, 1);
v_as_x27_1152_ = v_tail_1163_;
v_b_1153_ = v___x_1164_;
goto _start;
}
else
{
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1168_, v_b_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v_as_x27_1168_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_currNamespace_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_currNamespace_1178_);
lean_ctor_set(v___x_1181_, 1, v___y_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_currNamespace_1182_, v___y_1183_, v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_env_1186_, lean_object* v___x_1187_, lean_object* v_currNamespace_1188_, lean_object* v_openDecls_1189_, lean_object* v_n_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = l_Lean_ResolveName_resolveGlobalName(v_env_1186_, v___x_1187_, v_currNamespace_1188_, v_openDecls_1189_, v_n_1190_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v___y_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_env_1195_, lean_object* v___x_1196_, lean_object* v_currNamespace_1197_, lean_object* v_openDecls_1198_, lean_object* v_n_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_env_1195_, v___x_1196_, v_currNamespace_1197_, v_openDecls_1198_, v_n_1199_, v___y_1200_, v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v___x_1196_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1203_, lean_object* v_currNamespace_1204_, lean_object* v_openDecls_1205_, lean_object* v_n_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = l_Lean_ResolveName_resolveNamespace(v_env_1203_, v_currNamespace_1204_, v_openDecls_1205_, v_n_1206_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1211_, lean_object* v_currNamespace_1212_, lean_object* v_openDecls_1213_, lean_object* v_n_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1211_, v_currNamespace_1212_, v_openDecls_1213_, v_n_1214_, v___y_1215_, v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; lean_object* v_toCold_1228_; lean_object* v_env_1229_; lean_object* v_currRecDepth_1230_; lean_object* v_ref_1231_; lean_object* v_maxRecDepth_1232_; lean_object* v_currNamespace_1233_; lean_object* v_openDecls_1234_; lean_object* v_quotContext_1235_; lean_object* v_currMacroScope_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v_methods_1243_; lean_object* v___x_1244_; lean_object* v_nextMacroScope_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1227_ = lean_st_ref_get(v___y_1225_);
v_toCold_1228_ = lean_ctor_get(v___y_1224_, 0);
v_env_1229_ = lean_ctor_get(v___x_1227_, 0);
lean_inc_ref_n(v_env_1229_, 4);
lean_dec(v___x_1227_);
v_currRecDepth_1230_ = lean_ctor_get(v___y_1224_, 1);
v_ref_1231_ = lean_ctor_get(v___y_1224_, 2);
v_maxRecDepth_1232_ = lean_ctor_get(v_toCold_1228_, 3);
v_currNamespace_1233_ = lean_ctor_get(v_toCold_1228_, 4);
v_openDecls_1234_ = lean_ctor_get(v_toCold_1228_, 5);
v_quotContext_1235_ = lean_ctor_get(v_toCold_1228_, 8);
v_currMacroScope_1236_ = lean_ctor_get(v_toCold_1228_, 9);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1237_, 0, v_env_1229_);
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1238_, 0, v_env_1229_);
v___x_1239_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1224_);
lean_inc_n(v_currNamespace_1233_, 3);
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1240_, 0, v_currNamespace_1233_);
lean_inc_n(v_openDecls_1234_, 2);
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1241_, 0, v_env_1229_);
lean_closure_set(v___f_1241_, 1, v___x_1239_);
lean_closure_set(v___f_1241_, 2, v_currNamespace_1233_);
lean_closure_set(v___f_1241_, 3, v_openDecls_1234_);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1242_, 0, v_env_1229_);
lean_closure_set(v___f_1242_, 1, v_currNamespace_1233_);
lean_closure_set(v___f_1242_, 2, v_openDecls_1234_);
v_methods_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1243_, 0, v___f_1238_);
lean_ctor_set(v_methods_1243_, 1, v___f_1240_);
lean_ctor_set(v_methods_1243_, 2, v___f_1237_);
lean_ctor_set(v_methods_1243_, 3, v___f_1242_);
lean_ctor_set(v_methods_1243_, 4, v___f_1241_);
v___x_1244_ = lean_st_ref_get(v___y_1225_);
v_nextMacroScope_1245_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_nextMacroScope_1245_);
lean_dec(v___x_1244_);
lean_inc(v_ref_1231_);
lean_inc(v_maxRecDepth_1232_);
lean_inc(v_currRecDepth_1230_);
lean_inc(v_currMacroScope_1236_);
lean_inc(v_quotContext_1235_);
v___x_1246_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1246_, 0, v_methods_1243_);
lean_ctor_set(v___x_1246_, 1, v_quotContext_1235_);
lean_ctor_set(v___x_1246_, 2, v_currMacroScope_1236_);
lean_ctor_set(v___x_1246_, 3, v_currRecDepth_1230_);
lean_ctor_set(v___x_1246_, 4, v_maxRecDepth_1232_);
lean_ctor_set(v___x_1246_, 5, v_ref_1231_);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1248_, 0, v_nextMacroScope_1245_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
lean_ctor_set(v___x_1248_, 2, v___x_1247_);
v___x_1249_ = lean_apply_2(v_x_1219_, v___x_1246_, v___x_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v_a_1251_; lean_object* v_macroScope_1252_; lean_object* v_traceMsgs_1253_; lean_object* v_expandedMacroDecls_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 1);
lean_inc(v_a_1250_);
v_a_1251_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1249_, 2);
v_macroScope_1252_ = lean_ctor_get(v_a_1250_, 0);
lean_inc(v_macroScope_1252_);
v_traceMsgs_1253_ = lean_ctor_get(v_a_1250_, 1);
lean_inc(v_traceMsgs_1253_);
v_expandedMacroDecls_1254_ = lean_ctor_get(v_a_1250_, 2);
lean_inc(v_expandedMacroDecls_1254_);
lean_dec(v_a_1250_);
v___x_1255_ = lean_box(0);
v___x_1256_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1254_, v___x_1255_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v_expandedMacroDecls_1254_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___x_1257_; lean_object* v_env_1258_; lean_object* v_ngen_1259_; lean_object* v_auxDeclNGen_1260_; lean_object* v_traceState_1261_; lean_object* v_cache_1262_; lean_object* v_recordedDeps_1263_; lean_object* v_messages_1264_; lean_object* v_infoState_1265_; lean_object* v_snapshotTasks_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref_known(v___x_1256_, 1);
v___x_1257_ = lean_st_ref_take(v___y_1225_);
v_env_1258_ = lean_ctor_get(v___x_1257_, 0);
v_ngen_1259_ = lean_ctor_get(v___x_1257_, 2);
v_auxDeclNGen_1260_ = lean_ctor_get(v___x_1257_, 3);
v_traceState_1261_ = lean_ctor_get(v___x_1257_, 4);
v_cache_1262_ = lean_ctor_get(v___x_1257_, 5);
v_recordedDeps_1263_ = lean_ctor_get(v___x_1257_, 6);
v_messages_1264_ = lean_ctor_get(v___x_1257_, 7);
v_infoState_1265_ = lean_ctor_get(v___x_1257_, 8);
v_snapshotTasks_1266_ = lean_ctor_get(v___x_1257_, 9);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1257_, 1);
lean_dec(v_unused_1293_);
v___x_1268_ = v___x_1257_;
v_isShared_1269_ = v_isSharedCheck_1292_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snapshotTasks_1266_);
lean_inc(v_infoState_1265_);
lean_inc(v_messages_1264_);
lean_inc(v_recordedDeps_1263_);
lean_inc(v_cache_1262_);
lean_inc(v_traceState_1261_);
lean_inc(v_auxDeclNGen_1260_);
lean_inc(v_ngen_1259_);
lean_inc(v_env_1258_);
lean_dec(v___x_1257_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1292_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v_macroScope_1252_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_env_1258_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_macroScope_1252_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_ngen_1259_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_auxDeclNGen_1260_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_traceState_1261_);
lean_ctor_set(v_reuseFailAlloc_1291_, 5, v_cache_1262_);
lean_ctor_set(v_reuseFailAlloc_1291_, 6, v_recordedDeps_1263_);
lean_ctor_set(v_reuseFailAlloc_1291_, 7, v_messages_1264_);
lean_ctor_set(v_reuseFailAlloc_1291_, 8, v_infoState_1265_);
lean_ctor_set(v_reuseFailAlloc_1291_, 9, v_snapshotTasks_1266_);
v___x_1271_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_st_ref_put(v___y_1225_, v___x_1271_);
v___x_1273_ = l_List_reverse___redArg(v_traceMsgs_1253_);
v___x_1274_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1273_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1274_, 0);
lean_dec(v_unused_1282_);
v___x_1276_ = v___x_1274_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_dec(v___x_1274_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v_a_1251_);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1251_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_a_1251_);
v_a_1283_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1274_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1274_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_traceMsgs_1253_);
lean_dec(v_macroScope_1252_);
lean_dec(v_a_1251_);
v_a_1294_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1256_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1256_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
lean_object* v_a_1302_; 
v_a_1302_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1249_, 2);
if (lean_obj_tag(v_a_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v_a_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_a_1303_ = lean_ctor_get(v_a_1302_, 0);
lean_inc(v_a_1303_);
v_a_1304_ = lean_ctor_get(v_a_1302_, 1);
lean_inc_ref(v_a_1304_);
lean_dec_ref_known(v_a_1302_, 2);
v___x_1305_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1306_ = lean_string_dec_eq(v_a_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_a_1304_);
v___x_1308_ = l_Lean_MessageData_ofFormat(v___x_1307_);
v___x_1309_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1303_, v___x_1308_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v_a_1303_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; 
lean_dec_ref(v_a_1304_);
v___x_1310_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1303_);
return v___x_1310_;
}
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1324_, size_t v_i_1325_, lean_object* v_bs_1326_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_usize_dec_lt(v_i_1325_, v_sz_1324_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_bs_1326_);
return v___x_1328_;
}
else
{
lean_object* v_v_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_v_1329_ = lean_array_uget(v_bs_1326_, v_i_1325_);
v___x_1330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1329_);
v___x_1331_ = l_Lean_Syntax_isOfKind(v_v_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_dec(v_v_1329_);
lean_dec_ref(v_bs_1326_);
v___x_1332_ = lean_box(0);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = l_Lean_Syntax_getArg(v_v_1329_, v___x_1333_);
v___x_1335_ = l_Lean_Syntax_isOfKind(v___x_1334_, v___x_1330_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec(v_v_1329_);
lean_dec_ref(v_bs_1326_);
v___x_1336_ = lean_box(0);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; lean_object* v_bs_x27_1338_; lean_object* v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1337_ = lean_unsigned_to_nat(3u);
v_bs_x27_1338_ = lean_array_uset(v_bs_1326_, v_i_1325_, v___x_1333_);
v___x_1339_ = l_Lean_Syntax_getArg(v_v_1329_, v___x_1337_);
lean_dec(v_v_1329_);
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_add(v_i_1325_, v___x_1340_);
v___x_1342_ = lean_array_uset(v_bs_x27_1338_, v_i_1325_, v___x_1339_);
v_i_1325_ = v___x_1341_;
v_bs_1326_ = v___x_1342_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1344_, lean_object* v_i_1345_, lean_object* v_bs_1346_){
_start:
{
size_t v_sz_boxed_1347_; size_t v_i_boxed_1348_; lean_object* v_res_1349_; 
v_sz_boxed_1347_ = lean_unbox_usize(v_sz_1344_);
lean_dec(v_sz_1344_);
v_i_boxed_1348_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1347_, v_i_boxed_1348_, v_bs_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1362_, size_t v_i_1363_, lean_object* v_bs_1364_){
_start:
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_usize_dec_lt(v_i_1363_, v_sz_1362_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_bs_1364_);
return v___x_1366_;
}
else
{
lean_object* v_v_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_v_1367_ = lean_array_uget(v_bs_1364_, v_i_1363_);
v___x_1368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1367_);
v___x_1369_ = l_Lean_Syntax_isOfKind(v_v_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_dec(v_v_1367_);
lean_dec_ref(v_bs_1364_);
v___x_1370_ = lean_box(0);
return v___x_1370_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = l_Lean_Syntax_getArg(v_v_1367_, v___x_1371_);
v___x_1373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1374_ = l_Lean_Syntax_isOfKind(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_dec(v_v_1367_);
lean_dec_ref(v_bs_1364_);
v___x_1375_ = lean_box(0);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_bs_x27_1378_; lean_object* v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1376_ = lean_unsigned_to_nat(3u);
v___x_1377_ = lean_unsigned_to_nat(0u);
v_bs_x27_1378_ = lean_array_uset(v_bs_1364_, v_i_1363_, v___x_1377_);
v___x_1379_ = l_Lean_Syntax_getArg(v_v_1367_, v___x_1376_);
lean_dec(v_v_1367_);
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1363_, v___x_1380_);
v___x_1382_ = lean_array_uset(v_bs_x27_1378_, v_i_1363_, v___x_1379_);
v_i_1363_ = v___x_1381_;
v_bs_1364_ = v___x_1382_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1384_, lean_object* v_i_1385_, lean_object* v_bs_1386_){
_start:
{
size_t v_sz_boxed_1387_; size_t v_i_boxed_1388_; lean_object* v_res_1389_; 
v_sz_boxed_1387_ = lean_unbox_usize(v_sz_1384_);
lean_dec(v_sz_1384_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1385_);
lean_dec(v_i_1385_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1387_, v_i_boxed_1388_, v_bs_1386_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1396_, size_t v_i_1397_, lean_object* v_bs_1398_){
_start:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_usize_dec_lt(v_i_1397_, v_sz_1396_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_bs_1398_);
return v___x_1400_;
}
else
{
lean_object* v_v_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_v_1401_ = lean_array_uget(v_bs_1398_, v_i_1397_);
v___x_1402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1401_);
v___x_1403_ = l_Lean_Syntax_isOfKind(v_v_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_dec(v_v_1401_);
lean_dec_ref(v_bs_1398_);
v___x_1404_ = lean_box(0);
return v___x_1404_;
}
else
{
lean_object* v___x_1405_; lean_object* v_bs_x27_1406_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1405_ = lean_unsigned_to_nat(0u);
v_bs_x27_1406_ = lean_array_uset(v_bs_1398_, v_i_1397_, v___x_1405_);
v___x_1413_ = l_Lean_Syntax_getArg(v_v_1401_, v___x_1405_);
lean_dec(v_v_1401_);
v___x_1414_ = l_Lean_Syntax_isNone(v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = lean_unsigned_to_nat(2u);
v___x_1416_ = l_Lean_Syntax_matchesNull(v___x_1413_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_dec_ref(v_bs_x27_1406_);
v___x_1417_ = lean_box(0);
return v___x_1417_;
}
else
{
goto v___jp_1407_;
}
}
else
{
lean_dec(v___x_1413_);
goto v___jp_1407_;
}
v___jp_1407_:
{
lean_object* v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_box(0);
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_add(v_i_1397_, v___x_1409_);
v___x_1411_ = lean_array_uset(v_bs_x27_1406_, v_i_1397_, v___x_1408_);
v_i_1397_ = v___x_1410_;
v_bs_1398_ = v___x_1411_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1418_, lean_object* v_i_1419_, lean_object* v_bs_1420_){
_start:
{
size_t v_sz_boxed_1421_; size_t v_i_boxed_1422_; lean_object* v_res_1423_; 
v_sz_boxed_1421_ = lean_unbox_usize(v_sz_1418_);
lean_dec(v_sz_1418_);
v_i_boxed_1422_ = lean_unbox_usize(v_i_1419_);
lean_dec(v_i_1419_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1421_, v_i_boxed_1422_, v_bs_1420_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1424_, size_t v_i_1425_, lean_object* v_bs_1426_){
_start:
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_usize_dec_lt(v_i_1425_, v_sz_1424_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_bs_1426_);
return v___x_1428_;
}
else
{
lean_object* v_v_1429_; lean_object* v___x_1430_; lean_object* v_bs_x27_1431_; size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
v_v_1429_ = lean_array_uget(v_bs_1426_, v_i_1425_);
v___x_1430_ = lean_unsigned_to_nat(0u);
v_bs_x27_1431_ = lean_array_uset(v_bs_1426_, v_i_1425_, v___x_1430_);
v___x_1432_ = ((size_t)1ULL);
v___x_1433_ = lean_usize_add(v_i_1425_, v___x_1432_);
v___x_1434_ = lean_array_uset(v_bs_x27_1431_, v_i_1425_, v_v_1429_);
v_i_1425_ = v___x_1433_;
v_bs_1426_ = v___x_1434_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1436_, lean_object* v_i_1437_, lean_object* v_bs_1438_){
_start:
{
size_t v_sz_boxed_1439_; size_t v_i_boxed_1440_; lean_object* v_res_1441_; 
v_sz_boxed_1439_ = lean_unbox_usize(v_sz_1436_);
lean_dec(v_sz_1436_);
v_i_boxed_1440_ = lean_unbox_usize(v_i_1437_);
lean_dec(v_i_1437_);
v_res_1441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1439_, v_i_boxed_1440_, v_bs_1438_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1442_, lean_object* v_x_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1443_, v___y_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1447_, lean_object* v_x_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1447_, v_x_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec_ref(v_x_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1455_, lean_object* v_as_x27_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
if (lean_obj_tag(v_as_x27_1456_) == 0)
{
lean_object* v___x_1465_; 
lean_dec(v_stx_1455_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_b_1457_);
return v___x_1465_;
}
else
{
lean_object* v_head_1466_; lean_object* v_tail_1467_; lean_object* v_value_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec_ref(v_b_1457_);
v_head_1466_ = lean_ctor_get(v_as_x27_1456_, 0);
v_tail_1467_ = lean_ctor_get(v_as_x27_1456_, 1);
v_value_1468_ = lean_ctor_get(v_head_1466_, 1);
v___x_1469_ = lean_box(0);
v___x_1470_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1471_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_value_1468_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v_stx_1455_);
v___x_1472_ = lean_apply_8(v_value_1468_, v_stx_1455_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, lean_box(0));
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_stx_1455_);
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_a_1473_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___x_1469_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1478_);
v___x_1480_ = v___x_1475_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1504_; 
v_a_1483_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1485_ = v___x_1472_;
v_isShared_1486_ = v_isSharedCheck_1504_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1472_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1504_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
uint8_t v___x_1487_; 
v___x_1487_ = l_Lean_Exception_isInterrupt(v_a_1483_);
if (v___x_1487_ == 0)
{
uint8_t v___x_1488_; 
lean_inc(v_a_1483_);
v___x_1488_ = l_Lean_Exception_isRuntime(v_a_1483_);
if (v___x_1488_ == 0)
{
if (lean_obj_tag(v_a_1483_) == 0)
{
lean_object* v___x_1490_; 
lean_dec(v_stx_1455_);
if (v_isShared_1486_ == 0)
{
v___x_1490_ = v___x_1485_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1483_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
else
{
lean_object* v_id_1492_; uint8_t v___x_1493_; 
v_id_1492_ = lean_ctor_get(v_a_1483_, 0);
v___x_1493_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1471_, v_id_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v_stx_1455_);
if (v_isShared_1486_ == 0)
{
v___x_1495_ = v___x_1485_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1483_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
else
{
lean_dec_ref_known(v_a_1483_, 2);
lean_del_object(v___x_1485_);
v_as_x27_1456_ = v_tail_1467_;
v_b_1457_ = v___x_1470_;
goto _start;
}
}
}
else
{
lean_object* v___x_1499_; 
lean_dec(v_stx_1455_);
if (v_isShared_1486_ == 0)
{
v___x_1499_ = v___x_1485_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1483_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_object* v___x_1502_; 
lean_dec(v_stx_1455_);
if (v_isShared_1486_ == 0)
{
v___x_1502_ = v___x_1485_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1483_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1505_, lean_object* v_as_x27_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1505_, v_as_x27_1506_, v_b_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v_as_x27_1506_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1518_, lean_object* v_rhs_x3f_1519_, lean_object* v_otherwise_x3f_1520_, lean_object* v_body_x3f_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
uint8_t v___y_1530_; lean_object* v___y_1531_; uint8_t v___y_1532_; uint8_t v___y_1533_; uint8_t v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v_body_1541_; lean_object* v___y_1559_; lean_object* v_otherwise_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v_rhs_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; 
if (lean_obj_tag(v_rhs_x3f_1519_) == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1572_ = v___x_1583_;
v___y_1573_ = v_a_1522_;
v___y_1574_ = v_a_1523_;
v___y_1575_ = v_a_1524_;
v___y_1576_ = v_a_1525_;
v___y_1577_ = v_a_1526_;
v___y_1578_ = v_a_1527_;
goto v___jp_1571_;
}
else
{
lean_object* v_val_1584_; lean_object* v___x_1585_; 
v_val_1584_ = lean_ctor_get(v_rhs_x3f_1519_, 0);
lean_inc(v_val_1584_);
lean_dec_ref_known(v_rhs_x3f_1519_, 1);
v___x_1585_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1584_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v_rhs_1572_ = v_a_1586_;
v___y_1573_ = v_a_1522_;
v___y_1574_ = v_a_1523_;
v___y_1575_ = v_a_1524_;
v___y_1576_ = v_a_1525_;
v___y_1577_ = v_a_1526_;
v___y_1578_ = v_a_1527_;
goto v___jp_1571_;
}
else
{
lean_dec(v_body_x3f_1521_);
lean_dec(v_otherwise_x3f_1520_);
lean_dec_ref(v_reassigned_1518_);
return v___x_1585_;
}
}
v___jp_1529_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1536_, 0, v___y_1531_);
lean_ctor_set(v___x_1536_, 1, v___y_1535_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*2, v___y_1530_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*2 + 1, v___y_1534_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*2 + 2, v___y_1533_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*2 + 3, v___y_1532_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
v___jp_1538_:
{
lean_object* v___x_1542_; lean_object* v_info_1543_; uint8_t v_breaks_1544_; uint8_t v_continues_1545_; uint8_t v_returnsEarly_1546_; lean_object* v_numRegularExits_1547_; uint8_t v_noFallthrough_1548_; lean_object* v_reassigns_1549_; size_t v_sz_1550_; size_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1542_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1541_, v___y_1540_);
v_info_1543_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1539_, v___x_1542_);
v_breaks_1544_ = lean_ctor_get_uint8(v_info_1543_, sizeof(void*)*2);
v_continues_1545_ = lean_ctor_get_uint8(v_info_1543_, sizeof(void*)*2 + 1);
v_returnsEarly_1546_ = lean_ctor_get_uint8(v_info_1543_, sizeof(void*)*2 + 2);
v_numRegularExits_1547_ = lean_ctor_get(v_info_1543_, 0);
lean_inc(v_numRegularExits_1547_);
v_noFallthrough_1548_ = lean_ctor_get_uint8(v_info_1543_, sizeof(void*)*2 + 3);
v_reassigns_1549_ = lean_ctor_get(v_info_1543_, 1);
lean_inc(v_reassigns_1549_);
lean_dec_ref(v_info_1543_);
v_sz_1550_ = lean_array_size(v_reassigned_1518_);
v___x_1551_ = ((size_t)0ULL);
v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1550_, v___x_1551_, v_reassigned_1518_);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_array_get_size(v___x_1552_);
v___x_1555_ = lean_nat_dec_lt(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_dec_ref(v___x_1552_);
v___y_1530_ = v_breaks_1544_;
v___y_1531_ = v_numRegularExits_1547_;
v___y_1532_ = v_noFallthrough_1548_;
v___y_1533_ = v_returnsEarly_1546_;
v___y_1534_ = v_continues_1545_;
v___y_1535_ = v_reassigns_1549_;
goto v___jp_1529_;
}
else
{
size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_usize_of_nat(v___x_1554_);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1552_, v___x_1551_, v___x_1556_, v_reassigns_1549_);
lean_dec_ref(v___x_1552_);
v___y_1530_ = v_breaks_1544_;
v___y_1531_ = v_numRegularExits_1547_;
v___y_1532_ = v_noFallthrough_1548_;
v___y_1533_ = v_returnsEarly_1546_;
v___y_1534_ = v_continues_1545_;
v___y_1535_ = v___x_1557_;
goto v___jp_1529_;
}
}
v___jp_1558_:
{
if (lean_obj_tag(v_body_x3f_1521_) == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1539_ = v___y_1559_;
v___y_1540_ = v_otherwise_1560_;
v_body_1541_ = v___x_1567_;
goto v___jp_1538_;
}
else
{
lean_object* v_val_1568_; lean_object* v___x_1569_; 
v_val_1568_ = lean_ctor_get(v_body_x3f_1521_, 0);
lean_inc(v_val_1568_);
lean_dec_ref_known(v_body_x3f_1521_, 1);
v___x_1569_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1568_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___y_1539_ = v___y_1559_;
v___y_1540_ = v_otherwise_1560_;
v_body_1541_ = v_a_1570_;
goto v___jp_1538_;
}
else
{
lean_dec_ref(v_otherwise_1560_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v_reassigned_1518_);
return v___x_1569_;
}
}
}
v___jp_1571_:
{
if (lean_obj_tag(v_otherwise_x3f_1520_) == 0)
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1559_ = v_rhs_1572_;
v_otherwise_1560_ = v___x_1579_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v___y_1574_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v___y_1576_;
v___y_1565_ = v___y_1577_;
v___y_1566_ = v___y_1578_;
goto v___jp_1558_;
}
else
{
lean_object* v_val_1580_; lean_object* v___x_1581_; 
v_val_1580_ = lean_ctor_get(v_otherwise_x3f_1520_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v_otherwise_x3f_1520_, 1);
v___x_1581_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1580_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___y_1559_ = v_rhs_1572_;
v_otherwise_1560_ = v_a_1582_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v___y_1574_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v___y_1576_;
v___y_1565_ = v___y_1577_;
v___y_1566_ = v___y_1578_;
goto v___jp_1558_;
}
else
{
lean_dec_ref(v_rhs_1572_);
lean_dec(v_body_x3f_1521_);
lean_dec_ref(v_reassigned_1518_);
return v___x_1581_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1604_ = l_Lean_stringToMessageData(v___x_1603_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1689_, lean_object* v_decl_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v_reassigns_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1690_);
v___x_1727_ = l_Lean_Syntax_isOfKind(v_decl_1690_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1690_);
v___x_1729_ = l_Lean_Syntax_isOfKind(v_decl_1690_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1730_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1731_ = lean_box(0);
v___x_1732_ = l_Lean_Syntax_formatStx(v_decl_1690_, v___x_1731_, v___x_1729_);
v___x_1733_ = l_Std_Format_defWidth;
v___x_1734_ = lean_unsigned_to_nat(0u);
v___x_1735_ = l_Std_Format_pretty(v___x_1732_, v___x_1733_, v___x_1734_, v___x_1734_);
v___x_1736_ = l_Lean_stringToMessageData(v___x_1735_);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1730_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1737_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; lean_object* v_pattern_1740_; lean_object* v___y_1742_; lean_object* v_otherwise_x3f_1743_; lean_object* v_body_x3f_x3f_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v_body_x3f_x3f_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___x_1774_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1739_ = lean_unsigned_to_nat(0u);
v_pattern_1740_ = l_Lean_Syntax_getArg(v_decl_1690_, v___x_1739_);
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1813_ = l_Lean_Syntax_getArg(v_decl_1690_, v___x_1774_);
v___x_1814_ = l_Lean_Syntax_isNone(v___x_1813_);
if (v___x_1814_ == 0)
{
uint8_t v___x_1815_; 
lean_inc(v___x_1813_);
v___x_1815_ = l_Lean_Syntax_matchesNull(v___x_1813_, v___x_1774_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec(v___x_1813_);
lean_dec(v_pattern_1740_);
v___x_1816_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1817_ = lean_box(0);
v___x_1818_ = l_Lean_Syntax_formatStx(v_decl_1690_, v___x_1817_, v___x_1815_);
v___x_1819_ = l_Std_Format_defWidth;
v___x_1820_ = l_Std_Format_pretty(v___x_1818_, v___x_1819_, v___x_1739_, v___x_1739_);
v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1816_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1822_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1824_ = l_Lean_Syntax_getArg(v___x_1813_, v___x_1739_);
lean_dec(v___x_1813_);
v___x_1825_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1826_ = l_Lean_Syntax_isOfKind(v___x_1824_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec(v_pattern_1740_);
v___x_1827_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1828_ = lean_box(0);
v___x_1829_ = l_Lean_Syntax_formatStx(v_decl_1690_, v___x_1828_, v___x_1826_);
v___x_1830_ = l_Std_Format_defWidth;
v___x_1831_ = l_Std_Format_pretty(v___x_1829_, v___x_1830_, v___x_1739_, v___x_1739_);
v___x_1832_ = l_Lean_stringToMessageData(v___x_1831_);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1827_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1833_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1834_;
}
else
{
v___y_1776_ = v_a_1691_;
v___y_1777_ = v_a_1692_;
v___y_1778_ = v_a_1693_;
v___y_1779_ = v_a_1694_;
v___y_1780_ = v_a_1695_;
v___y_1781_ = v_a_1696_;
goto v___jp_1775_;
}
}
}
else
{
lean_dec(v___x_1813_);
v___y_1776_ = v_a_1691_;
v___y_1777_ = v_a_1692_;
v___y_1778_ = v_a_1693_;
v___y_1779_ = v_a_1694_;
v___y_1780_ = v_a_1695_;
v___y_1781_ = v_a_1696_;
goto v___jp_1775_;
}
v___jp_1741_:
{
if (v_reassignment_1689_ == 0)
{
lean_object* v___x_1751_; 
lean_dec(v_pattern_1740_);
v___x_1751_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1711_ = v_body_x3f_x3f_1744_;
v___y_1712_ = v___y_1742_;
v___y_1713_ = v_otherwise_x3f_1743_;
v_reassigns_1714_ = v___x_1751_;
v___y_1715_ = v___y_1745_;
v___y_1716_ = v___y_1746_;
v___y_1717_ = v___y_1747_;
v___y_1718_ = v___y_1748_;
v___y_1719_ = v___y_1749_;
v___y_1720_ = v___y_1750_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1740_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___y_1711_ = v_body_x3f_x3f_1744_;
v___y_1712_ = v___y_1742_;
v___y_1713_ = v_otherwise_x3f_1743_;
v_reassigns_1714_ = v_a_1753_;
v___y_1715_ = v___y_1745_;
v___y_1716_ = v___y_1746_;
v___y_1717_ = v___y_1747_;
v___y_1718_ = v___y_1748_;
v___y_1719_ = v___y_1749_;
v___y_1720_ = v___y_1750_;
goto v___jp_1710_;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_body_x3f_x3f_1744_);
lean_dec(v_otherwise_x3f_1743_);
lean_dec(v___y_1742_);
v_a_1754_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1752_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1752_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
v___jp_1762_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___y_1763_);
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_body_x3f_x3f_1765_);
v___y_1742_ = v___y_1764_;
v_otherwise_x3f_1743_ = v___x_1772_;
v_body_x3f_x3f_1744_ = v___x_1773_;
v___y_1745_ = v___y_1766_;
v___y_1746_ = v___y_1767_;
v___y_1747_ = v___y_1768_;
v___y_1748_ = v___y_1769_;
v___y_1749_ = v___y_1770_;
v___y_1750_ = v___y_1771_;
goto v___jp_1741_;
}
v___jp_1775_:
{
lean_object* v___x_1782_; lean_object* v_rhs_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1782_ = lean_unsigned_to_nat(3u);
v_rhs_1783_ = l_Lean_Syntax_getArg(v_decl_1690_, v___x_1782_);
v___x_1784_ = lean_unsigned_to_nat(4u);
v___x_1785_ = l_Lean_Syntax_getArg(v_decl_1690_, v___x_1784_);
v___x_1786_ = l_Lean_Syntax_isNone(v___x_1785_);
if (v___x_1786_ == 0)
{
uint8_t v___x_1787_; 
lean_inc(v___x_1785_);
v___x_1787_ = l_Lean_Syntax_matchesNull(v___x_1785_, v___x_1782_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec(v___x_1785_);
lean_dec(v_rhs_1783_);
lean_dec(v_pattern_1740_);
v___x_1788_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1789_ = lean_box(0);
v___x_1790_ = l_Lean_Syntax_formatStx(v_decl_1690_, v___x_1789_, v___x_1787_);
v___x_1791_ = l_Std_Format_defWidth;
v___x_1792_ = l_Std_Format_pretty(v___x_1790_, v___x_1791_, v___x_1739_, v___x_1739_);
v___x_1793_ = l_Lean_stringToMessageData(v___x_1792_);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1788_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1794_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; lean_object* v_otherwise_x3f_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1796_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1797_ = l_Lean_Syntax_getArg(v___x_1785_, v___x_1774_);
v___x_1798_ = l_Lean_Syntax_getArg(v___x_1785_, v___x_1796_);
lean_dec(v___x_1785_);
v___x_1799_ = l_Lean_Syntax_isNone(v___x_1798_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; 
lean_inc(v___x_1798_);
v___x_1800_ = l_Lean_Syntax_matchesNull(v___x_1798_, v___x_1774_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v___x_1798_);
lean_dec(v_otherwise_x3f_1797_);
lean_dec(v_rhs_1783_);
lean_dec(v_pattern_1740_);
v___x_1801_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1802_ = lean_box(0);
v___x_1803_ = l_Lean_Syntax_formatStx(v_decl_1690_, v___x_1802_, v___x_1800_);
v___x_1804_ = l_Std_Format_defWidth;
v___x_1805_ = l_Std_Format_pretty(v___x_1803_, v___x_1804_, v___x_1739_, v___x_1739_);
v___x_1806_ = l_Lean_stringToMessageData(v___x_1805_);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1801_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1807_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
return v___x_1808_;
}
else
{
lean_object* v_body_x3f_x3f_1809_; lean_object* v___x_1810_; 
lean_dec(v_decl_1690_);
v_body_x3f_x3f_1809_ = l_Lean_Syntax_getArg(v___x_1798_, v___x_1739_);
lean_dec(v___x_1798_);
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_body_x3f_x3f_1809_);
v___y_1763_ = v_otherwise_x3f_1797_;
v___y_1764_ = v_rhs_1783_;
v_body_x3f_x3f_1765_ = v___x_1810_;
v___y_1766_ = v___y_1776_;
v___y_1767_ = v___y_1777_;
v___y_1768_ = v___y_1778_;
v___y_1769_ = v___y_1779_;
v___y_1770_ = v___y_1780_;
v___y_1771_ = v___y_1781_;
goto v___jp_1762_;
}
}
else
{
lean_object* v___x_1811_; 
lean_dec(v___x_1798_);
lean_dec(v_decl_1690_);
v___x_1811_ = lean_box(0);
v___y_1763_ = v_otherwise_x3f_1797_;
v___y_1764_ = v_rhs_1783_;
v_body_x3f_x3f_1765_ = v___x_1811_;
v___y_1766_ = v___y_1776_;
v___y_1767_ = v___y_1777_;
v___y_1768_ = v___y_1778_;
v___y_1769_ = v___y_1779_;
v___y_1770_ = v___y_1780_;
v___y_1771_ = v___y_1781_;
goto v___jp_1762_;
}
}
}
else
{
lean_object* v___x_1812_; 
lean_dec(v___x_1785_);
lean_dec(v_decl_1690_);
v___x_1812_ = lean_box(0);
v___y_1742_ = v_rhs_1783_;
v_otherwise_x3f_1743_ = v___x_1812_;
v_body_x3f_x3f_1744_ = v___x_1812_;
v___y_1745_ = v___y_1776_;
v___y_1746_ = v___y_1777_;
v___y_1747_ = v___y_1778_;
v___y_1748_ = v___y_1779_;
v___y_1749_ = v___y_1780_;
v___y_1750_ = v___y_1781_;
goto v___jp_1741_;
}
}
}
}
else
{
lean_object* v___x_1835_; lean_object* v_x_1836_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v_x_1836_ = l_Lean_Syntax_getArg(v_decl_1690_, v___x_1835_);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1836_);
v___x_1851_ = l_Lean_Syntax_isOfKind(v_x_1836_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec(v_x_1836_);
v___x_1852_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1853_ = lean_box(0);
v___x_1854_ = l_Lean_Syntax_formatStx(v_decl_1690_, v___x_1853_, v___x_1851_);
v___x_1855_ = l_Std_Format_defWidth;
v___x_1856_ = l_Std_Format_pretty(v___x_1854_, v___x_1855_, v___x_1835_, v___x_1835_);
v___x_1857_ = l_Lean_stringToMessageData(v___x_1856_);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1852_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1858_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = lean_unsigned_to_nat(1u);
v___x_1861_ = l_Lean_Syntax_getArg(v_decl_1690_, v___x_1860_);
v___x_1862_ = l_Lean_Syntax_isNone(v___x_1861_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1863_; 
lean_inc(v___x_1861_);
v___x_1863_ = l_Lean_Syntax_matchesNull(v___x_1861_, v___x_1860_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec(v___x_1861_);
lean_dec(v_x_1836_);
v___x_1864_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1865_ = lean_box(0);
v___x_1866_ = l_Lean_Syntax_formatStx(v_decl_1690_, v___x_1865_, v___x_1863_);
v___x_1867_ = l_Std_Format_defWidth;
v___x_1868_ = l_Std_Format_pretty(v___x_1866_, v___x_1867_, v___x_1835_, v___x_1835_);
v___x_1869_ = l_Lean_stringToMessageData(v___x_1868_);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1864_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1870_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1872_ = l_Lean_Syntax_getArg(v___x_1861_, v___x_1835_);
lean_dec(v___x_1861_);
v___x_1873_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1874_ = l_Lean_Syntax_isOfKind(v___x_1872_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v_x_1836_);
v___x_1875_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1876_ = lean_box(0);
v___x_1877_ = l_Lean_Syntax_formatStx(v_decl_1690_, v___x_1876_, v___x_1874_);
v___x_1878_ = l_Std_Format_defWidth;
v___x_1879_ = l_Std_Format_pretty(v___x_1877_, v___x_1878_, v___x_1835_, v___x_1835_);
v___x_1880_ = l_Lean_stringToMessageData(v___x_1879_);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1875_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1881_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1882_;
}
else
{
v___y_1838_ = v_a_1691_;
v___y_1839_ = v_a_1692_;
v___y_1840_ = v_a_1693_;
v___y_1841_ = v_a_1694_;
v___y_1842_ = v_a_1695_;
v___y_1843_ = v_a_1696_;
goto v___jp_1837_;
}
}
}
else
{
lean_dec(v___x_1861_);
v___y_1838_ = v_a_1691_;
v___y_1839_ = v_a_1692_;
v___y_1840_ = v_a_1693_;
v___y_1841_ = v_a_1694_;
v___y_1842_ = v_a_1695_;
v___y_1843_ = v_a_1696_;
goto v___jp_1837_;
}
}
v___jp_1837_:
{
lean_object* v___x_1844_; lean_object* v_rhs_1845_; 
v___x_1844_ = lean_unsigned_to_nat(3u);
v_rhs_1845_ = l_Lean_Syntax_getArg(v_decl_1690_, v___x_1844_);
lean_dec(v_decl_1690_);
if (v_reassignment_1689_ == 0)
{
lean_object* v___x_1846_; 
lean_dec(v_x_1836_);
v___x_1846_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1699_ = v___y_1840_;
v___y_1700_ = v_rhs_1845_;
v___y_1701_ = v___y_1838_;
v___y_1702_ = v___y_1839_;
v___y_1703_ = v___y_1842_;
v___y_1704_ = v___y_1841_;
v___y_1705_ = v___y_1843_;
v___y_1706_ = v___x_1846_;
goto v___jp_1698_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_unsigned_to_nat(1u);
v___x_1848_ = lean_mk_empty_array_with_capacity(v___x_1847_);
v___x_1849_ = lean_array_push(v___x_1848_, v_x_1836_);
v___y_1699_ = v___y_1840_;
v___y_1700_ = v_rhs_1845_;
v___y_1701_ = v___y_1838_;
v___y_1702_ = v___y_1839_;
v___y_1703_ = v___y_1842_;
v___y_1704_ = v___y_1841_;
v___y_1705_ = v___y_1843_;
v___y_1706_ = v___x_1849_;
goto v___jp_1698_;
}
}
}
v___jp_1698_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___y_1700_);
v___x_1708_ = lean_box(0);
v___x_1709_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1706_, v___x_1707_, v___x_1708_, v___x_1708_, v___y_1701_, v___y_1702_, v___y_1699_, v___y_1704_, v___y_1703_, v___y_1705_);
return v___x_1709_;
}
v___jp_1710_:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___y_1712_);
if (lean_obj_tag(v___y_1711_) == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_box(0);
v___x_1723_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1714_, v___x_1721_, v___y_1713_, v___x_1722_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v___x_1723_;
}
else
{
lean_object* v_val_1724_; lean_object* v___x_1725_; 
v_val_1724_ = lean_ctor_get(v___y_1711_, 0);
lean_inc(v_val_1724_);
lean_dec_ref_known(v___y_1711_, 1);
v___x_1725_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1714_, v___x_1721_, v___y_1713_, v_val_1724_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v___x_1725_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_2008_, size_t v_sz_2009_, size_t v_i_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_usize_dec_lt(v_i_2010_, v_sz_2009_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_b_2011_);
return v___x_2020_;
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2022_; 
v_a_2021_ = lean_array_uget_borrowed(v_as_2008_, v_i_2010_);
lean_inc(v_a_2021_);
v___x_2022_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_2021_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2023_, v_b_2011_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2010_, v___x_2025_);
v_i_2010_ = v___x_2026_;
v_b_2011_ = v___x_2024_;
goto _start;
}
else
{
lean_dec_ref(v_b_2011_);
return v___x_2022_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2042_ = l_Lean_stringToMessageData(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2057_, lean_object* v_as_2058_, size_t v_sz_2059_, size_t v_i_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_a_2070_; uint8_t v___x_2074_; 
v___x_2074_ = lean_usize_dec_lt(v_i_2060_, v_sz_2059_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_b_2061_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; lean_object* v_a_2077_; uint8_t v___x_2078_; 
v___x_2076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2077_ = lean_array_uget_borrowed(v_as_2058_, v_i_2060_);
lean_inc(v_a_2077_);
v___x_2078_ = l_Lean_Syntax_isOfKind(v_a_2077_, v___x_2076_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_dec_ref_known(v___x_2079_, 1);
v_a_2070_ = v_b_2061_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_b_2061_);
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v___x_2088_; lean_object* v___y_2090_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2088_ = lean_unsigned_to_nat(3u);
v___x_2107_ = lean_unsigned_to_nat(1u);
v___x_2108_ = l_Lean_Syntax_getArg(v_a_2077_, v___x_2107_);
v___x_2109_ = l_Lean_Syntax_getArgs(v___x_2108_);
lean_dec(v___x_2108_);
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2112_ = lean_array_get_size(v___x_2109_);
v___x_2113_ = lean_nat_dec_lt(v___x_2110_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_dec_ref(v___x_2109_);
v___y_2090_ = v___x_2111_;
goto v___jp_2089_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; size_t v___x_2116_; size_t v___x_2117_; lean_object* v___x_2118_; lean_object* v_snd_2119_; 
v___x_2114_ = lean_box(v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2111_);
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = lean_usize_of_nat(v___x_2112_);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2078_, v___x_2057_, v___x_2109_, v___x_2116_, v___x_2117_, v___x_2115_);
lean_dec_ref(v___x_2109_);
v_snd_2119_ = lean_ctor_get(v___x_2118_, 1);
lean_inc(v_snd_2119_);
lean_dec_ref(v___x_2118_);
v___y_2090_ = v_snd_2119_;
goto v___jp_2089_;
}
v___jp_2089_:
{
size_t v_sz_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v_sz_2091_ = lean_array_size(v___y_2090_);
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2091_, v___x_2092_, v___y_2090_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec_ref_known(v___x_2094_, 1);
v_a_2070_ = v_b_2061_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_b_2061_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec_ref_known(v___x_2093_, 1);
v___x_2103_ = l_Lean_Syntax_getArg(v_a_2077_, v___x_2088_);
v___x_2104_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2103_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2061_, v_a_2105_);
v_a_2070_ = v___x_2106_;
goto v___jp_2069_;
}
else
{
lean_dec_ref(v_b_2061_);
return v___x_2104_;
}
}
}
}
}
v___jp_2069_:
{
size_t v___x_2071_; size_t v___x_2072_; 
v___x_2071_ = ((size_t)1ULL);
v___x_2072_ = lean_usize_add(v_i_2060_, v___x_2071_);
v_i_2060_ = v___x_2072_;
v_b_2061_ = v_a_2070_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2120_, size_t v_sz_2121_, size_t v_i_2122_, lean_object* v_b_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_a_2132_; uint8_t v___x_2136_; 
v___x_2136_ = lean_usize_dec_lt(v_i_2122_, v_sz_2121_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; 
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v_b_2123_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; lean_object* v_a_2139_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2138_ = lean_unsigned_to_nat(0u);
v_a_2139_ = lean_array_uget_borrowed(v_as_2120_, v_i_2122_);
v___x_2152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2139_);
v___x_2153_ = l_Lean_Syntax_isOfKind(v_a_2139_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2139_);
v___x_2155_ = l_Lean_Syntax_isOfKind(v_a_2139_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2156_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2157_ = lean_box(0);
lean_inc(v_a_2139_);
v___x_2158_ = l_Lean_Syntax_formatStx(v_a_2139_, v___x_2157_, v___x_2155_);
v___x_2159_ = l_Std_Format_defWidth;
v___x_2160_ = l_Std_Format_pretty(v___x_2158_, v___x_2159_, v___x_2138_, v___x_2138_);
v___x_2161_ = l_Lean_stringToMessageData(v___x_2160_);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2156_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2162_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_dec_ref_known(v___x_2163_, 1);
v_a_2132_ = v_b_2123_;
goto v___jp_2131_;
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_b_2123_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2172_ = lean_unsigned_to_nat(1u);
v___x_2173_ = l_Lean_Syntax_getArg(v_a_2139_, v___x_2172_);
v___x_2174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2173_);
v___x_2175_ = l_Lean_Syntax_isOfKind(v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec(v___x_2173_);
v___x_2176_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2177_ = lean_box(0);
lean_inc(v_a_2139_);
v___x_2178_ = l_Lean_Syntax_formatStx(v_a_2139_, v___x_2177_, v___x_2175_);
v___x_2179_ = l_Std_Format_defWidth;
v___x_2180_ = l_Std_Format_pretty(v___x_2178_, v___x_2179_, v___x_2138_, v___x_2138_);
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2176_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2182_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_dec_ref_known(v___x_2183_, 1);
v_a_2132_ = v_b_2123_;
goto v___jp_2131_;
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v_b_2123_);
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; size_t v_sz_2194_; size_t v___x_2195_; lean_object* v___x_2196_; 
v___x_2192_ = l_Lean_Syntax_getArg(v___x_2173_, v___x_2138_);
lean_dec(v___x_2173_);
v___x_2193_ = l_Lean_Syntax_getArgs(v___x_2192_);
lean_dec(v___x_2192_);
v_sz_2194_ = lean_array_size(v___x_2193_);
v___x_2195_ = ((size_t)0ULL);
v___x_2196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2153_, v___x_2193_, v_sz_2194_, v___x_2195_, v_b_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec_ref(v___x_2193_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v_a_2132_ = v_a_2197_;
goto v___jp_2131_;
}
else
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = lean_unsigned_to_nat(2u);
v___x_2199_ = l_Lean_Syntax_getArg(v_a_2139_, v___x_2198_);
v___x_2200_ = l_Lean_Syntax_isNone(v___x_2199_);
if (v___x_2200_ == 0)
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lean_Syntax_matchesNull(v___x_2199_, v___x_2198_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2202_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2203_ = lean_box(0);
lean_inc(v_a_2139_);
v___x_2204_ = l_Lean_Syntax_formatStx(v_a_2139_, v___x_2203_, v___x_2201_);
v___x_2205_ = l_Std_Format_defWidth;
v___x_2206_ = l_Std_Format_pretty(v___x_2204_, v___x_2205_, v___x_2138_, v___x_2138_);
v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2202_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2208_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_dec_ref_known(v___x_2209_, 1);
v_a_2132_ = v_b_2123_;
goto v___jp_2131_;
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_b_2123_);
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
v___y_2141_ = v___y_2124_;
v___y_2142_ = v___y_2125_;
v___y_2143_ = v___y_2126_;
v___y_2144_ = v___y_2127_;
v___y_2145_ = v___y_2128_;
v___y_2146_ = v___y_2129_;
goto v___jp_2140_;
}
}
else
{
lean_dec(v___x_2199_);
v___y_2141_ = v___y_2124_;
v___y_2142_ = v___y_2125_;
v___y_2143_ = v___y_2126_;
v___y_2144_ = v___y_2127_;
v___y_2145_ = v___y_2128_;
v___y_2146_ = v___y_2129_;
goto v___jp_2140_;
}
}
v___jp_2140_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = lean_unsigned_to_nat(4u);
v___x_2148_ = l_Lean_Syntax_getArg(v_a_2139_, v___x_2147_);
v___x_2149_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2148_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2150_, v_b_2123_);
v_a_2132_ = v___x_2151_;
goto v___jp_2131_;
}
else
{
lean_dec_ref(v_b_2123_);
return v___x_2149_;
}
}
}
v___jp_2131_:
{
size_t v___x_2133_; size_t v___x_2134_; 
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_add(v_i_2122_, v___x_2133_);
v_i_2122_ = v___x_2134_;
v_b_2123_ = v_a_2132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2218_) == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
else
{
lean_object* v_val_2228_; lean_object* v___x_2229_; 
v_val_2228_ = lean_ctor_get(v_stx_x3f_2218_, 0);
lean_inc(v_val_2228_);
lean_dec_ref_known(v_stx_x3f_2218_, 1);
v___x_2229_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2228_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2248_, lean_object* v_as_2249_, size_t v_sz_2250_, size_t v_i_2251_, lean_object* v_b_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_a_2261_; uint8_t v___x_2265_; 
v___x_2265_ = lean_usize_dec_lt(v_i_2251_, v_sz_2250_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v_b_2252_);
return v___x_2266_;
}
else
{
lean_object* v___x_2267_; lean_object* v_a_2268_; uint8_t v___x_2269_; 
v___x_2267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2268_ = lean_array_uget_borrowed(v_as_2249_, v_i_2251_);
lean_inc(v_a_2268_);
v___x_2269_ = l_Lean_Syntax_isOfKind(v_a_2268_, v___x_2267_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_dec_ref_known(v___x_2270_, 1);
v_a_2261_ = v_b_2252_;
goto v___jp_2260_;
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v_b_2252_);
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
else
{
lean_object* v___x_2279_; lean_object* v___y_2281_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2279_ = lean_unsigned_to_nat(3u);
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = l_Lean_Syntax_getArg(v_a_2268_, v___x_2298_);
v___x_2300_ = l_Lean_Syntax_getArgs(v___x_2299_);
lean_dec(v___x_2299_);
v___x_2301_ = lean_unsigned_to_nat(0u);
v___x_2302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2303_ = lean_array_get_size(v___x_2300_);
v___x_2304_ = lean_nat_dec_lt(v___x_2301_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_dec_ref(v___x_2300_);
v___y_2281_ = v___x_2302_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; lean_object* v___x_2309_; lean_object* v_snd_2310_; 
v___x_2305_ = lean_box(v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___x_2302_);
v___x_2307_ = ((size_t)0ULL);
v___x_2308_ = lean_usize_of_nat(v___x_2303_);
v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2269_, v___x_2248_, v___x_2300_, v___x_2307_, v___x_2308_, v___x_2306_);
lean_dec_ref(v___x_2300_);
v_snd_2310_ = lean_ctor_get(v___x_2309_, 1);
lean_inc(v_snd_2310_);
lean_dec_ref(v___x_2309_);
v___y_2281_ = v_snd_2310_;
goto v___jp_2280_;
}
v___jp_2280_:
{
size_t v_sz_2282_; size_t v___x_2283_; lean_object* v___x_2284_; 
v_sz_2282_ = lean_array_size(v___y_2281_);
v___x_2283_ = ((size_t)0ULL);
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2282_, v___x_2283_, v___y_2281_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_dec_ref_known(v___x_2285_, 1);
v_a_2261_ = v_b_2252_;
goto v___jp_2260_;
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v_b_2252_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref_known(v___x_2284_, 1);
v___x_2294_ = l_Lean_Syntax_getArg(v_a_2268_, v___x_2279_);
v___x_2295_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2294_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2297_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2252_, v_a_2296_);
v_a_2261_ = v___x_2297_;
goto v___jp_2260_;
}
else
{
lean_dec_ref(v_b_2252_);
return v___x_2295_;
}
}
}
}
}
v___jp_2260_:
{
size_t v___x_2262_; size_t v___x_2263_; 
v___x_2262_ = ((size_t)1ULL);
v___x_2263_ = lean_usize_add(v_i_2251_, v___x_2262_);
v_i_2251_ = v___x_2263_;
v_b_2252_ = v_a_2261_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2359_ = l_Lean_NameSet_empty;
v___x_2360_ = lean_unsigned_to_nat(0u);
v___x_2361_ = 0;
v___x_2362_ = 1;
v___x_2363_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2363_, 0, v___x_2360_);
lean_ctor_set(v___x_2363_, 1, v___x_2359_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*2, v___x_2362_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*2 + 1, v___x_2361_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*2 + 2, v___x_2361_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*2 + 3, v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___y_2373_; lean_object* v_bodyInfo_2374_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2394_; lean_object* v_bodyInfo_2395_; lean_object* v___x_2398_; lean_object* v_env_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2398_ = lean_st_ref_get(v_a_2370_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc_ref(v_env_2399_);
lean_dec(v___x_2398_);
lean_inc(v_stx_2364_);
v___x_2400_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2400_, 0, v_env_2399_);
lean_closure_set(v___x_2400_, 1, v_stx_2364_);
v___x_2401_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2400_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_5107_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_5107_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_5107_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
if (lean_obj_tag(v_a_2402_) == 1)
{
lean_object* v_val_2406_; lean_object* v_snd_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_del_object(v___x_2404_);
lean_dec(v_stx_2364_);
v_val_2406_ = lean_ctor_get(v_a_2402_, 0);
lean_inc(v_val_2406_);
lean_dec_ref_known(v_a_2402_, 1);
v_snd_2407_ = lean_ctor_get(v_val_2406_, 1);
lean_inc(v_snd_2407_);
lean_dec(v_val_2406_);
v___x_2408_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2408_, 0, lean_box(0));
lean_closure_set(v___x_2408_, 1, v_snd_2407_);
v___x_2409_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2408_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v_stx_2364_ = v_a_2410_;
goto _start;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
v_a_2412_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2409_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2409_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___x_2602_; uint8_t v___x_2603_; uint8_t v___x_2604_; 
lean_dec(v_a_2402_);
v___x_2602_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2364_);
v___x_2603_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2602_);
v___x_2604_ = 1;
if (v___x_2603_ == 0)
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2364_);
v___x_2606_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2364_);
v___x_2608_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2364_);
v___x_2610_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2611_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2364_);
v___x_2612_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2613_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2364_);
v___x_2614_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
lean_del_object(v___x_2404_);
v___x_2615_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2364_);
v___x_2616_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2364_);
v___x_2618_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; uint8_t v___x_2620_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; 
v___x_2619_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2364_);
v___x_2620_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2364_);
v___x_2682_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2683_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2364_);
v___x_2684_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2683_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2364_);
v___x_2686_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2364_);
v___x_2688_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2364_);
v___x_2690_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2689_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2364_);
v___x_2692_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2693_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2364_);
v___x_2694_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; uint8_t v___x_2696_; uint8_t v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; uint8_t v___y_2701_; 
v___x_2695_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2364_);
v___x_2696_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2364_);
v___x_2705_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2364_);
v___x_2707_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2708_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2364_);
v___x_2709_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2364_);
v___x_2711_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2712_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2364_);
v___x_2713_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2364_);
v___x_2715_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2716_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2364_);
v___x_2717_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2718_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2364_);
v___x_2719_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2718_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v_stx_2364_);
v___x_2721_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v_stx_2364_);
v___x_2723_ = l_Lean_Syntax_isOfKind(v_stx_2364_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v_env_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_inc_n(v_stx_2364_, 2);
v___x_2724_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_2725_ = lean_st_ref_get(v_a_2370_);
v_env_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc_ref(v_env_2726_);
lean_dec(v___x_2725_);
v___x_2727_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2728_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2727_, v_env_2726_, v___x_2724_);
v___x_2729_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2730_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_2728_, v___x_2729_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_2728_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2761_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2761_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2761_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_fst_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2759_; 
v_fst_2735_ = lean_ctor_get(v_a_2731_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_a_2731_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; 
v_unused_2760_ = lean_ctor_get(v_a_2731_, 1);
lean_dec(v_unused_2760_);
v___x_2737_ = v_a_2731_;
v_isShared_2738_ = v_isSharedCheck_2759_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_fst_2735_);
lean_dec(v_a_2731_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2759_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
if (lean_obj_tag(v_fst_2735_) == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
lean_del_object(v___x_2733_);
v___x_2739_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2740_ = l_Lean_MessageData_ofName(v___x_2724_);
lean_inc_ref(v___x_2740_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set_tag(v___x_2737_, 7);
lean_ctor_set(v___x_2737_, 1, v___x_2740_);
lean_ctor_set(v___x_2737_, 0, v___x_2739_);
v___x_2742_ = v___x_2737_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2743_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_2746_ = l_Lean_indentD(v___x_2745_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2744_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
lean_ctor_set(v___x_2750_, 1, v___x_2740_);
v___x_2751_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2752_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_2753_;
}
}
else
{
lean_object* v_val_2755_; lean_object* v___x_2757_; 
lean_del_object(v___x_2737_);
lean_dec(v___x_2724_);
lean_dec(v_stx_2364_);
v_val_2755_ = lean_ctor_get(v_fst_2735_, 0);
lean_inc(v_val_2755_);
lean_dec_ref_known(v_fst_2735_, 1);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v_val_2755_);
v___x_2757_ = v___x_2733_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_val_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v___x_2724_);
lean_dec(v_stx_2364_);
v_a_2762_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2730_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2730_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___y_2774_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2770_ = lean_unsigned_to_nat(1u);
v___x_2771_ = lean_unsigned_to_nat(5u);
v___x_2772_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2771_);
v___x_2783_ = lean_unsigned_to_nat(6u);
v___x_2784_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2783_);
lean_dec(v_stx_2364_);
v___x_2785_ = l_Lean_Syntax_getOptional_x3f(v___x_2784_);
lean_dec(v___x_2784_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_box(0);
v___y_2774_ = v___x_2786_;
goto v___jp_2773_;
}
else
{
lean_object* v_val_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_val_2787_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2785_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_val_2787_);
lean_dec(v___x_2785_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_val_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
v___y_2774_ = v___x_2792_;
goto v___jp_2773_;
}
}
}
v___jp_2773_:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2772_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_2775_) == 0)
{
if (lean_obj_tag(v___y_2774_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = l_Lean_NameSet_empty;
v___x_2778_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2778_, 0, v___x_2770_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*2, v___x_2721_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*2 + 1, v___x_2721_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*2 + 2, v___x_2721_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*2 + 3, v___x_2721_);
v___y_2373_ = v_a_2776_;
v_bodyInfo_2374_ = v___x_2778_;
goto v___jp_2372_;
}
else
{
lean_object* v_a_2779_; lean_object* v_val_2780_; lean_object* v___x_2781_; 
v_a_2779_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2775_, 1);
v_val_2780_ = lean_ctor_get(v___y_2774_, 0);
lean_inc(v_val_2780_);
lean_dec_ref_known(v___y_2774_, 1);
v___x_2781_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2780_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___y_2373_ = v_a_2779_;
v_bodyInfo_2374_ = v_a_2782_;
goto v___jp_2372_;
}
else
{
lean_dec(v_a_2779_);
return v___x_2781_;
}
}
}
else
{
lean_dec(v___y_2774_);
return v___x_2775_;
}
}
}
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___y_2799_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2795_ = lean_unsigned_to_nat(1u);
v___x_2796_ = lean_unsigned_to_nat(5u);
v___x_2797_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2796_);
v___x_2808_ = lean_unsigned_to_nat(6u);
v___x_2809_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2808_);
lean_dec(v_stx_2364_);
v___x_2810_ = l_Lean_Syntax_getOptional_x3f(v___x_2809_);
lean_dec(v___x_2809_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_box(0);
v___y_2799_ = v___x_2811_;
goto v___jp_2798_;
}
else
{
lean_object* v_val_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
v_val_2812_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2810_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_val_2812_);
lean_dec(v___x_2810_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_val_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
v___y_2799_ = v___x_2817_;
goto v___jp_2798_;
}
}
}
v___jp_2798_:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2797_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_2800_) == 0)
{
if (lean_obj_tag(v___y_2799_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
v___x_2802_ = l_Lean_NameSet_empty;
v___x_2803_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2803_, 0, v___x_2795_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*2, v___x_2719_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*2 + 1, v___x_2719_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*2 + 2, v___x_2719_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*2 + 3, v___x_2719_);
v___y_2394_ = v_a_2801_;
v_bodyInfo_2395_ = v___x_2803_;
goto v___jp_2393_;
}
else
{
lean_object* v_a_2804_; lean_object* v_val_2805_; lean_object* v___x_2806_; 
v_a_2804_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2800_, 1);
v_val_2805_ = lean_ctor_get(v___y_2799_, 0);
lean_inc(v_val_2805_);
lean_dec_ref_known(v___y_2799_, 1);
v___x_2806_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2805_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___y_2394_ = v_a_2804_;
v_bodyInfo_2395_ = v_a_2807_;
goto v___jp_2393_;
}
else
{
lean_dec(v_a_2804_);
return v___x_2806_;
}
}
}
else
{
lean_dec(v___y_2799_);
return v___x_2800_;
}
}
}
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_2820_ = lean_unsigned_to_nat(0u);
v___x_2821_ = lean_unsigned_to_nat(1u);
v___x_3035_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2821_);
v___x_3036_ = l_Lean_Syntax_isNone(v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = lean_unsigned_to_nat(5u);
v___x_3038_ = l_Lean_Syntax_matchesNull(v___x_3035_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v_env_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_inc_n(v_stx_2364_, 2);
v___x_3039_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3040_ = lean_st_ref_get(v_a_2370_);
v_env_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc_ref(v_env_3041_);
lean_dec(v___x_3040_);
v___x_3042_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3043_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3042_, v_env_3041_, v___x_3039_);
v___x_3044_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3045_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3043_, v___x_3044_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3043_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3076_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3076_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3076_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v_fst_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3074_; 
v_fst_3050_ = lean_ctor_get(v_a_3046_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_a_3046_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v_a_3046_, 1);
lean_dec(v_unused_3075_);
v___x_3052_ = v_a_3046_;
v_isShared_3053_ = v_isSharedCheck_3074_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_fst_3050_);
lean_dec(v_a_3046_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3074_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
if (lean_obj_tag(v_fst_3050_) == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
lean_del_object(v___x_3048_);
v___x_3054_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3055_ = l_Lean_MessageData_ofName(v___x_3039_);
lean_inc_ref(v___x_3055_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set_tag(v___x_3052_, 7);
lean_ctor_set(v___x_3052_, 1, v___x_3055_);
lean_ctor_set(v___x_3052_, 0, v___x_3054_);
v___x_3057_ = v___x_3052_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3058_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3061_ = l_Lean_indentD(v___x_3060_);
v___x_3062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3059_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3062_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v___x_3055_);
v___x_3066_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3065_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3067_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3068_;
}
}
else
{
lean_object* v_val_3070_; lean_object* v___x_3072_; 
lean_del_object(v___x_3052_);
lean_dec(v___x_3039_);
lean_dec(v_stx_2364_);
v_val_3070_ = lean_ctor_get(v_fst_3050_, 0);
lean_inc(v_val_3070_);
lean_dec_ref_known(v_fst_3050_, 1);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v_val_3070_);
v___x_3072_ = v___x_3048_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_val_3070_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v___x_3039_);
lean_dec(v_stx_2364_);
v_a_3077_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3045_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3045_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
v___y_2823_ = v_a_2365_;
v___y_2824_ = v_a_2366_;
v___y_2825_ = v_a_2367_;
v___y_2826_ = v_a_2368_;
v___y_2827_ = v_a_2369_;
v___y_2828_ = v_a_2370_;
goto v___jp_2822_;
}
}
else
{
lean_dec(v___x_3035_);
v___y_2823_ = v_a_2365_;
v___y_2824_ = v_a_2366_;
v___y_2825_ = v_a_2367_;
v___y_2826_ = v_a_2368_;
v___y_2827_ = v_a_2369_;
v___y_2828_ = v_a_2370_;
goto v___jp_2822_;
}
v___jp_2822_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2829_ = lean_unsigned_to_nat(4u);
v___x_2830_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2829_);
v___x_2831_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
lean_inc(v___x_2830_);
v___x_2832_ = l_Lean_Syntax_isOfKind(v___x_2830_, v___x_2831_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v_env_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec(v___x_2830_);
lean_inc_n(v_stx_2364_, 2);
v___x_2833_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_2834_ = lean_st_ref_get(v___y_2828_);
v_env_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc_ref(v_env_2835_);
lean_dec(v___x_2834_);
v___x_2836_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2837_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2836_, v_env_2835_, v___x_2833_);
v___x_2838_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2839_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_2837_, v___x_2838_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___x_2837_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2870_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2870_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2870_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v_fst_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2868_; 
v_fst_2844_ = lean_ctor_get(v_a_2840_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_a_2840_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v_a_2840_, 1);
lean_dec(v_unused_2869_);
v___x_2846_ = v_a_2840_;
v_isShared_2847_ = v_isSharedCheck_2868_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_fst_2844_);
lean_dec(v_a_2840_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2868_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
if (lean_obj_tag(v_fst_2844_) == 0)
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
lean_del_object(v___x_2842_);
v___x_2848_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2849_ = l_Lean_MessageData_ofName(v___x_2833_);
lean_inc_ref(v___x_2849_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set_tag(v___x_2846_, 7);
lean_ctor_set(v___x_2846_, 1, v___x_2849_);
lean_ctor_set(v___x_2846_, 0, v___x_2848_);
v___x_2851_ = v___x_2846_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2852_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_2855_ = l_Lean_indentD(v___x_2854_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2853_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v___x_2849_);
v___x_2860_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2859_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2861_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_2862_;
}
}
else
{
lean_object* v_val_2864_; lean_object* v___x_2866_; 
lean_del_object(v___x_2846_);
lean_dec(v___x_2833_);
lean_dec(v_stx_2364_);
v_val_2864_ = lean_ctor_get(v_fst_2844_, 0);
lean_inc(v_val_2864_);
lean_dec_ref_known(v_fst_2844_, 1);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v_val_2864_);
v___x_2866_ = v___x_2842_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_val_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v___x_2833_);
lean_dec(v_stx_2364_);
v_a_2871_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2839_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2839_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; size_t v_sz_2881_; size_t v___x_2882_; lean_object* v___x_2883_; 
v___x_2879_ = l_Lean_Syntax_getArg(v___x_2830_, v___x_2820_);
v___x_2880_ = l_Lean_Syntax_getArgs(v___x_2879_);
lean_dec(v___x_2879_);
v_sz_2881_ = lean_array_size(v___x_2880_);
v___x_2882_ = ((size_t)0ULL);
v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2881_, v___x_2882_, v___x_2880_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v_env_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec(v___x_2830_);
lean_inc_n(v_stx_2364_, 2);
v___x_2884_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_2885_ = lean_st_ref_get(v___y_2828_);
v_env_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc_ref(v_env_2886_);
lean_dec(v___x_2885_);
v___x_2887_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2888_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2887_, v_env_2886_, v___x_2884_);
v___x_2889_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2890_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_2888_, v___x_2889_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___x_2888_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2921_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2921_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2921_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_fst_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2919_; 
v_fst_2895_ = lean_ctor_get(v_a_2891_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_a_2891_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v_a_2891_, 1);
lean_dec(v_unused_2920_);
v___x_2897_ = v_a_2891_;
v_isShared_2898_ = v_isSharedCheck_2919_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_fst_2895_);
lean_dec(v_a_2891_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2919_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
if (lean_obj_tag(v_fst_2895_) == 0)
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
lean_del_object(v___x_2893_);
v___x_2899_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2900_ = l_Lean_MessageData_ofName(v___x_2884_);
lean_inc_ref(v___x_2900_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set_tag(v___x_2897_, 7);
lean_ctor_set(v___x_2897_, 1, v___x_2900_);
lean_ctor_set(v___x_2897_, 0, v___x_2899_);
v___x_2902_ = v___x_2897_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2903_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_2906_ = l_Lean_indentD(v___x_2905_);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2904_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___x_2900_);
v___x_2911_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2912_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_2913_;
}
}
else
{
lean_object* v_val_2915_; lean_object* v___x_2917_; 
lean_del_object(v___x_2897_);
lean_dec(v___x_2884_);
lean_dec(v_stx_2364_);
v_val_2915_ = lean_ctor_get(v_fst_2895_, 0);
lean_inc(v_val_2915_);
lean_dec_ref_known(v_fst_2895_, 1);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v_val_2915_);
v___x_2917_ = v___x_2893_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_val_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v___x_2884_);
lean_dec(v_stx_2364_);
v_a_2922_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2890_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2890_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v_val_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v_val_2930_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_val_2930_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2931_ = l_Lean_Syntax_getArg(v___x_2830_, v___x_2821_);
lean_dec(v___x_2830_);
v___x_2932_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_2931_);
v___x_2933_ = l_Lean_Syntax_isOfKind(v___x_2931_, v___x_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v_env_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
lean_dec(v___x_2931_);
lean_dec(v_val_2930_);
lean_inc_n(v_stx_2364_, 2);
v___x_2934_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_2935_ = lean_st_ref_get(v___y_2828_);
v_env_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc_ref(v_env_2936_);
lean_dec(v___x_2935_);
v___x_2937_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2938_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2937_, v_env_2936_, v___x_2934_);
v___x_2939_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2940_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_2938_, v___x_2939_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___x_2938_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2971_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2971_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2971_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v_fst_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2969_; 
v_fst_2945_ = lean_ctor_get(v_a_2941_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_a_2941_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; 
v_unused_2970_ = lean_ctor_get(v_a_2941_, 1);
lean_dec(v_unused_2970_);
v___x_2947_ = v_a_2941_;
v_isShared_2948_ = v_isSharedCheck_2969_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_fst_2945_);
lean_dec(v_a_2941_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2969_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
if (lean_obj_tag(v_fst_2945_) == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
lean_del_object(v___x_2943_);
v___x_2949_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2950_ = l_Lean_MessageData_ofName(v___x_2934_);
lean_inc_ref(v___x_2950_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 7);
lean_ctor_set(v___x_2947_, 1, v___x_2950_);
lean_ctor_set(v___x_2947_, 0, v___x_2949_);
v___x_2952_ = v___x_2947_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2953_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_2956_ = l_Lean_indentD(v___x_2955_);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2954_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v___x_2950_);
v___x_2961_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2962_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_2963_;
}
}
else
{
lean_object* v_val_2965_; lean_object* v___x_2967_; 
lean_del_object(v___x_2947_);
lean_dec(v___x_2934_);
lean_dec(v_stx_2364_);
v_val_2965_ = lean_ctor_get(v_fst_2945_, 0);
lean_inc(v_val_2965_);
lean_dec_ref_known(v_fst_2945_, 1);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v_val_2965_);
v___x_2967_ = v___x_2943_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_val_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v___x_2934_);
lean_dec(v_stx_2364_);
v_a_2972_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2940_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2940_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; 
v___x_2980_ = l_Lean_Syntax_getArg(v___x_2931_, v___x_2821_);
v___x_2981_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_2982_ = l_Lean_Syntax_isOfKind(v___x_2980_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v_env_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec(v___x_2931_);
lean_dec(v_val_2930_);
lean_inc_n(v_stx_2364_, 2);
v___x_2983_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_2984_ = lean_st_ref_get(v___y_2828_);
v_env_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc_ref(v_env_2985_);
lean_dec(v___x_2984_);
v___x_2986_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2987_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2986_, v_env_2985_, v___x_2983_);
v___x_2988_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2989_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_2987_, v___x_2988_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___x_2987_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3020_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3020_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3020_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_fst_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3018_; 
v_fst_2994_ = lean_ctor_get(v_a_2990_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_a_2990_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v_a_2990_, 1);
lean_dec(v_unused_3019_);
v___x_2996_ = v_a_2990_;
v_isShared_2997_ = v_isSharedCheck_3018_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_fst_2994_);
lean_dec(v_a_2990_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3018_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
if (lean_obj_tag(v_fst_2994_) == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
lean_del_object(v___x_2992_);
v___x_2998_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2999_ = l_Lean_MessageData_ofName(v___x_2983_);
lean_inc_ref(v___x_2999_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set_tag(v___x_2996_, 7);
lean_ctor_set(v___x_2996_, 1, v___x_2999_);
lean_ctor_set(v___x_2996_, 0, v___x_2998_);
v___x_3001_ = v___x_2996_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_2998_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3002_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3005_ = l_Lean_indentD(v___x_3004_);
v___x_3006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3003_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set(v___x_3009_, 1, v___x_2999_);
v___x_3010_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3011_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_3012_;
}
}
else
{
lean_object* v_val_3014_; lean_object* v___x_3016_; 
lean_del_object(v___x_2996_);
lean_dec(v___x_2983_);
lean_dec(v_stx_2364_);
v_val_3014_ = lean_ctor_get(v_fst_2994_, 0);
lean_inc(v_val_3014_);
lean_dec_ref_known(v_fst_2994_, 1);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v_val_3014_);
v___x_3016_ = v___x_2992_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_val_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v___x_2983_);
lean_dec(v_stx_2364_);
v_a_3021_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2989_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2989_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec(v_stx_2364_);
v___x_3029_ = lean_unsigned_to_nat(3u);
v___x_3030_ = l_Lean_Syntax_getArg(v___x_2931_, v___x_3029_);
lean_dec(v___x_2931_);
v___x_3031_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3030_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; size_t v_sz_3033_; lean_object* v___x_3034_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
v_sz_3033_ = lean_array_size(v_val_2930_);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2930_, v_sz_3033_, v___x_2882_, v_a_3032_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v_val_2930_);
return v___x_3034_;
}
else
{
lean_dec(v_val_2930_);
return v___x_3031_;
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
lean_object* v___x_3085_; lean_object* v___x_3086_; 
lean_dec(v_stx_2364_);
v___x_3085_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
return v___x_3086_;
}
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_dec(v_stx_2364_);
v___x_3087_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
lean_dec(v_stx_2364_);
v___x_3089_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_dec(v_stx_2364_);
v___x_3091_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
return v___x_3092_;
}
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec(v_stx_2364_);
v___x_3093_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
return v___x_3094_;
}
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; size_t v_sz_3098_; size_t v___x_3099_; lean_object* v___x_3100_; 
v___x_3095_ = lean_unsigned_to_nat(2u);
v___x_3096_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3095_);
v___x_3097_ = l_Lean_Syntax_getArgs(v___x_3096_);
lean_dec(v___x_3096_);
v_sz_3098_ = lean_array_size(v___x_3097_);
v___x_3099_ = ((size_t)0ULL);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3098_, v___x_3099_, v___x_3097_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v_env_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_inc_n(v_stx_2364_, 2);
v___x_3101_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3102_ = lean_st_ref_get(v_a_2370_);
v_env_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc_ref(v_env_3103_);
lean_dec(v___x_3102_);
v___x_3104_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3105_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3104_, v_env_3103_, v___x_3101_);
v___x_3106_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3107_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3105_, v___x_3106_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3105_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3138_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3138_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3138_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v_fst_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3136_; 
v_fst_3112_ = lean_ctor_get(v_a_3108_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_a_3108_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v_a_3108_, 1);
lean_dec(v_unused_3137_);
v___x_3114_ = v_a_3108_;
v_isShared_3115_ = v_isSharedCheck_3136_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_fst_3112_);
lean_dec(v_a_3108_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3136_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
if (lean_obj_tag(v_fst_3112_) == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
lean_del_object(v___x_3110_);
v___x_3116_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3117_ = l_Lean_MessageData_ofName(v___x_3101_);
lean_inc_ref(v___x_3117_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set_tag(v___x_3114_, 7);
lean_ctor_set(v___x_3114_, 1, v___x_3117_);
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3119_ = v___x_3114_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3120_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3123_ = l_Lean_indentD(v___x_3122_);
v___x_3124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3121_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
v___x_3125_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3124_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
lean_ctor_set(v___x_3127_, 1, v___x_3117_);
v___x_3128_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3129_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3130_;
}
}
else
{
lean_object* v_val_3132_; lean_object* v___x_3134_; 
lean_del_object(v___x_3114_);
lean_dec(v___x_3101_);
lean_dec(v_stx_2364_);
v_val_3132_ = lean_ctor_get(v_fst_3112_, 0);
lean_inc(v_val_3132_);
lean_dec_ref_known(v_fst_3112_, 1);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v_val_3132_);
v___x_3134_ = v___x_3110_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_val_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v___x_3101_);
lean_dec(v_stx_2364_);
v_a_3139_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3107_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3107_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_val_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3281_; 
v_val_3147_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3149_ = v___x_3100_;
v_isShared_3150_ = v_isSharedCheck_3281_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_val_3147_);
lean_dec(v___x_3100_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3281_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_finSeq_x3f_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3151_);
v___x_3176_ = lean_unsigned_to_nat(3u);
v___x_3177_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3176_);
v___x_3178_ = l_Lean_Syntax_isNone(v___x_3177_);
if (v___x_3178_ == 0)
{
uint8_t v___x_3179_; 
lean_inc(v___x_3177_);
v___x_3179_ = l_Lean_Syntax_matchesNull(v___x_3177_, v___x_3151_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v_env_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec(v___x_3177_);
lean_dec(v___x_3152_);
lean_del_object(v___x_3149_);
lean_dec(v_val_3147_);
lean_inc_n(v_stx_2364_, 2);
v___x_3180_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3181_ = lean_st_ref_get(v_a_2370_);
v_env_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc_ref(v_env_3182_);
lean_dec(v___x_3181_);
v___x_3183_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3184_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3183_, v_env_3182_, v___x_3180_);
v___x_3185_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3186_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3184_, v___x_3185_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3184_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3217_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3217_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3217_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v_fst_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3215_; 
v_fst_3191_ = lean_ctor_get(v_a_3187_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_a_3187_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; 
v_unused_3216_ = lean_ctor_get(v_a_3187_, 1);
lean_dec(v_unused_3216_);
v___x_3193_ = v_a_3187_;
v_isShared_3194_ = v_isSharedCheck_3215_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_fst_3191_);
lean_dec(v_a_3187_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3215_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
if (lean_obj_tag(v_fst_3191_) == 0)
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; 
lean_del_object(v___x_3189_);
v___x_3195_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3196_ = l_Lean_MessageData_ofName(v___x_3180_);
lean_inc_ref(v___x_3196_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 7);
lean_ctor_set(v___x_3193_, 1, v___x_3196_);
lean_ctor_set(v___x_3193_, 0, v___x_3195_);
v___x_3198_ = v___x_3193_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3199_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3198_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3202_ = l_Lean_indentD(v___x_3201_);
v___x_3203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3200_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
v___x_3204_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v___x_3196_);
v___x_3207_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3208_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3209_;
}
}
else
{
lean_object* v_val_3211_; lean_object* v___x_3213_; 
lean_del_object(v___x_3193_);
lean_dec(v___x_3180_);
lean_dec(v_stx_2364_);
v_val_3211_ = lean_ctor_get(v_fst_3191_, 0);
lean_inc(v_val_3211_);
lean_dec_ref_known(v_fst_3191_, 1);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v_val_3211_);
v___x_3213_ = v___x_3189_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_val_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec(v___x_3180_);
lean_dec(v_stx_2364_);
v_a_3218_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3186_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3186_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3226_ = lean_unsigned_to_nat(0u);
v___x_3227_ = l_Lean_Syntax_getArg(v___x_3177_, v___x_3226_);
lean_dec(v___x_3177_);
v___x_3228_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
lean_inc(v___x_3227_);
v___x_3229_ = l_Lean_Syntax_isOfKind(v___x_3227_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v_env_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_dec(v___x_3227_);
lean_dec(v___x_3152_);
lean_del_object(v___x_3149_);
lean_dec(v_val_3147_);
lean_inc_n(v_stx_2364_, 2);
v___x_3230_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3231_ = lean_st_ref_get(v_a_2370_);
v_env_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc_ref(v_env_3232_);
lean_dec(v___x_3231_);
v___x_3233_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3234_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3233_, v_env_3232_, v___x_3230_);
v___x_3235_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3236_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3234_, v___x_3235_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3234_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3267_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3267_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3267_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v_fst_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3265_; 
v_fst_3241_ = lean_ctor_get(v_a_3237_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v_a_3237_);
if (v_isSharedCheck_3265_ == 0)
{
lean_object* v_unused_3266_; 
v_unused_3266_ = lean_ctor_get(v_a_3237_, 1);
lean_dec(v_unused_3266_);
v___x_3243_ = v_a_3237_;
v_isShared_3244_ = v_isSharedCheck_3265_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_fst_3241_);
lean_dec(v_a_3237_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3265_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
if (lean_obj_tag(v_fst_3241_) == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
lean_del_object(v___x_3239_);
v___x_3245_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3246_ = l_Lean_MessageData_ofName(v___x_3230_);
lean_inc_ref(v___x_3246_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set_tag(v___x_3243_, 7);
lean_ctor_set(v___x_3243_, 1, v___x_3246_);
lean_ctor_set(v___x_3243_, 0, v___x_3245_);
v___x_3248_ = v___x_3243_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3249_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3252_ = l_Lean_indentD(v___x_3251_);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3250_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
lean_ctor_set(v___x_3256_, 1, v___x_3246_);
v___x_3257_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3258_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3259_;
}
}
else
{
lean_object* v_val_3261_; lean_object* v___x_3263_; 
lean_del_object(v___x_3243_);
lean_dec(v___x_3230_);
lean_dec(v_stx_2364_);
v_val_3261_ = lean_ctor_get(v_fst_3241_, 0);
lean_inc(v_val_3261_);
lean_dec_ref_known(v_fst_3241_, 1);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v_val_3261_);
v___x_3263_ = v___x_3239_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_val_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec(v___x_3230_);
lean_dec(v_stx_2364_);
v_a_3268_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3236_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3236_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
lean_dec(v_stx_2364_);
v___x_3276_ = l_Lean_Syntax_getArg(v___x_3227_, v___x_3151_);
lean_dec(v___x_3227_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v___x_3276_);
v___x_3278_ = v___x_3149_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
v_finSeq_x3f_3154_ = v___x_3278_;
v___y_3155_ = v_a_2365_;
v___y_3156_ = v_a_2366_;
v___y_3157_ = v_a_2367_;
v___y_3158_ = v_a_2368_;
v___y_3159_ = v_a_2369_;
v___y_3160_ = v_a_2370_;
goto v___jp_3153_;
}
}
}
}
else
{
lean_object* v___x_3280_; 
lean_dec(v___x_3177_);
lean_del_object(v___x_3149_);
lean_dec(v_stx_2364_);
v___x_3280_ = lean_box(0);
v_finSeq_x3f_3154_ = v___x_3280_;
v___y_3155_ = v_a_2365_;
v___y_3156_ = v_a_2366_;
v___y_3157_ = v_a_2367_;
v___y_3158_ = v_a_2368_;
v___y_3159_ = v_a_2369_;
v___y_3160_ = v_a_2370_;
goto v___jp_3153_;
}
v___jp_3153_:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3152_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; size_t v_sz_3163_; lean_object* v___x_3164_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v_sz_3163_ = lean_array_size(v_val_3147_);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3147_, v_sz_3163_, v___x_3099_, v_a_3162_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v_val_3147_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v___x_3166_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3175_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3175_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3175_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3171_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3165_, v_a_3167_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3171_);
v___x_3173_ = v___x_3169_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
else
{
lean_dec(v_a_3165_);
return v___x_3166_;
}
}
else
{
lean_dec(v_finSeq_x3f_3154_);
return v___x_3164_;
}
}
else
{
lean_dec(v_finSeq_x3f_3154_);
lean_dec(v_val_3147_);
return v___x_3161_;
}
}
}
}
}
}
else
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3282_ = lean_unsigned_to_nat(0u);
v___x_3283_ = lean_unsigned_to_nat(1u);
v___x_3406_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3283_);
v___x_3407_ = l_Lean_Syntax_isNone(v___x_3406_);
if (v___x_3407_ == 0)
{
uint8_t v___x_3408_; 
lean_inc(v___x_3406_);
v___x_3408_ = l_Lean_Syntax_matchesNull(v___x_3406_, v___x_3283_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v_env_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v___x_3406_);
lean_inc_n(v_stx_2364_, 2);
v___x_3409_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3410_ = lean_st_ref_get(v_a_2370_);
v_env_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc_ref(v_env_3411_);
lean_dec(v___x_3410_);
v___x_3412_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3413_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3412_, v_env_3411_, v___x_3409_);
v___x_3414_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3415_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3413_, v___x_3414_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3413_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3446_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3446_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3446_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_fst_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3444_; 
v_fst_3420_ = lean_ctor_get(v_a_3416_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3444_ == 0)
{
lean_object* v_unused_3445_; 
v_unused_3445_ = lean_ctor_get(v_a_3416_, 1);
lean_dec(v_unused_3445_);
v___x_3422_ = v_a_3416_;
v_isShared_3423_ = v_isSharedCheck_3444_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_fst_3420_);
lean_dec(v_a_3416_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3444_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
if (lean_obj_tag(v_fst_3420_) == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
lean_del_object(v___x_3418_);
v___x_3424_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3425_ = l_Lean_MessageData_ofName(v___x_3409_);
lean_inc_ref(v___x_3425_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set_tag(v___x_3422_, 7);
lean_ctor_set(v___x_3422_, 1, v___x_3425_);
lean_ctor_set(v___x_3422_, 0, v___x_3424_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3428_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3431_ = l_Lean_indentD(v___x_3430_);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3429_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
lean_ctor_set(v___x_3435_, 1, v___x_3425_);
v___x_3436_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3435_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3437_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3438_;
}
}
else
{
lean_object* v_val_3440_; lean_object* v___x_3442_; 
lean_del_object(v___x_3422_);
lean_dec(v___x_3409_);
lean_dec(v_stx_2364_);
v_val_3440_ = lean_ctor_get(v_fst_3420_, 0);
lean_inc(v_val_3440_);
lean_dec_ref_known(v_fst_3420_, 1);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v_val_3440_);
v___x_3442_ = v___x_3418_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_val_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v___x_3409_);
lean_dec(v_stx_2364_);
v_a_3447_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3415_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3415_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3455_ = l_Lean_Syntax_getArg(v___x_3406_, v___x_3282_);
lean_dec(v___x_3406_);
v___x_3456_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3457_ = l_Lean_Syntax_isOfKind(v___x_3455_, v___x_3456_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v_env_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_inc_n(v_stx_2364_, 2);
v___x_3458_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3459_ = lean_st_ref_get(v_a_2370_);
v_env_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc_ref(v_env_3460_);
lean_dec(v___x_3459_);
v___x_3461_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3462_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3461_, v_env_3460_, v___x_3458_);
v___x_3463_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3464_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3462_, v___x_3463_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3462_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3495_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3495_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3495_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_fst_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3493_; 
v_fst_3469_ = lean_ctor_get(v_a_3465_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_a_3465_);
if (v_isSharedCheck_3493_ == 0)
{
lean_object* v_unused_3494_; 
v_unused_3494_ = lean_ctor_get(v_a_3465_, 1);
lean_dec(v_unused_3494_);
v___x_3471_ = v_a_3465_;
v_isShared_3472_ = v_isSharedCheck_3493_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_fst_3469_);
lean_dec(v_a_3465_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3493_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
if (lean_obj_tag(v_fst_3469_) == 0)
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
lean_del_object(v___x_3467_);
v___x_3473_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3474_ = l_Lean_MessageData_ofName(v___x_3458_);
lean_inc_ref(v___x_3474_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set_tag(v___x_3471_, 7);
lean_ctor_set(v___x_3471_, 1, v___x_3474_);
lean_ctor_set(v___x_3471_, 0, v___x_3473_);
v___x_3476_ = v___x_3471_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3477_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3476_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3480_ = l_Lean_indentD(v___x_3479_);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3478_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
lean_ctor_set(v___x_3484_, 1, v___x_3474_);
v___x_3485_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3484_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3486_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3487_;
}
}
else
{
lean_object* v_val_3489_; lean_object* v___x_3491_; 
lean_del_object(v___x_3471_);
lean_dec(v___x_3458_);
lean_dec(v_stx_2364_);
v_val_3489_ = lean_ctor_get(v_fst_3469_, 0);
lean_inc(v_val_3489_);
lean_dec_ref_known(v_fst_3469_, 1);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v_val_3489_);
v___x_3491_ = v___x_3467_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_val_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v___x_3458_);
lean_dec(v_stx_2364_);
v_a_3496_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3464_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3464_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
v___y_3301_ = v_a_2365_;
v___y_3302_ = v_a_2366_;
v___y_3303_ = v_a_2367_;
v___y_3304_ = v_a_2368_;
v___y_3305_ = v_a_2369_;
v___y_3306_ = v_a_2370_;
goto v___jp_3300_;
}
}
}
else
{
lean_dec(v___x_3406_);
v___y_3301_ = v_a_2365_;
v___y_3302_ = v_a_2366_;
v___y_3303_ = v_a_2367_;
v___y_3304_ = v_a_2368_;
v___y_3305_ = v_a_2369_;
v___y_3306_ = v_a_2370_;
goto v___jp_3300_;
}
v___jp_3284_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = lean_unsigned_to_nat(3u);
v___x_3292_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3291_);
lean_dec(v_stx_2364_);
v___x_3293_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3292_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; uint8_t v_breaks_3295_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3293_, 1);
v_breaks_3295_ = lean_ctor_get_uint8(v_a_3294_, sizeof(void*)*2);
if (v_breaks_3295_ == 0)
{
uint8_t v_returnsEarly_3296_; lean_object* v_reassigns_3297_; 
v_returnsEarly_3296_ = lean_ctor_get_uint8(v_a_3294_, sizeof(void*)*2 + 2);
v_reassigns_3297_ = lean_ctor_get(v_a_3294_, 1);
lean_inc(v_reassigns_3297_);
lean_dec(v_a_3294_);
v___y_2698_ = v_returnsEarly_3296_;
v___y_2699_ = v_reassigns_3297_;
v___y_2700_ = v___x_3282_;
v___y_2701_ = v___x_2705_;
goto v___jp_2697_;
}
else
{
uint8_t v_returnsEarly_3298_; lean_object* v_reassigns_3299_; 
v_returnsEarly_3298_ = lean_ctor_get_uint8(v_a_3294_, sizeof(void*)*2 + 2);
v_reassigns_3299_ = lean_ctor_get(v_a_3294_, 1);
lean_inc(v_reassigns_3299_);
lean_dec(v_a_3294_);
v___y_2698_ = v_returnsEarly_3298_;
v___y_2699_ = v_reassigns_3299_;
v___y_2700_ = v___x_3283_;
v___y_2701_ = v___x_2696_;
goto v___jp_2697_;
}
}
else
{
return v___x_3293_;
}
}
v___jp_3300_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3307_ = lean_unsigned_to_nat(2u);
v___x_3308_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3307_);
v___x_3309_ = l_Lean_Syntax_isNone(v___x_3308_);
if (v___x_3309_ == 0)
{
uint8_t v___x_3310_; 
lean_inc(v___x_3308_);
v___x_3310_ = l_Lean_Syntax_matchesNull(v___x_3308_, v___x_3283_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v_env_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
lean_dec(v___x_3308_);
lean_inc_n(v_stx_2364_, 2);
v___x_3311_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3312_ = lean_st_ref_get(v___y_3306_);
v_env_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc_ref(v_env_3313_);
lean_dec(v___x_3312_);
v___x_3314_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3315_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3314_, v_env_3313_, v___x_3311_);
v___x_3316_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3317_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3315_, v___x_3316_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___x_3315_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3348_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3320_ = v___x_3317_;
v_isShared_3321_ = v_isSharedCheck_3348_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3348_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v_fst_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3346_; 
v_fst_3322_ = lean_ctor_get(v_a_3318_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_a_3318_);
if (v_isSharedCheck_3346_ == 0)
{
lean_object* v_unused_3347_; 
v_unused_3347_ = lean_ctor_get(v_a_3318_, 1);
lean_dec(v_unused_3347_);
v___x_3324_ = v_a_3318_;
v_isShared_3325_ = v_isSharedCheck_3346_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_fst_3322_);
lean_dec(v_a_3318_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3346_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
if (lean_obj_tag(v_fst_3322_) == 0)
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3329_; 
lean_del_object(v___x_3320_);
v___x_3326_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3327_ = l_Lean_MessageData_ofName(v___x_3311_);
lean_inc_ref(v___x_3327_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 7);
lean_ctor_set(v___x_3324_, 1, v___x_3327_);
lean_ctor_set(v___x_3324_, 0, v___x_3326_);
v___x_3329_ = v___x_3324_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3330_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3333_ = l_Lean_indentD(v___x_3332_);
v___x_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3331_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v___x_3327_);
v___x_3338_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3339_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
return v___x_3340_;
}
}
else
{
lean_object* v_val_3342_; lean_object* v___x_3344_; 
lean_del_object(v___x_3324_);
lean_dec(v___x_3311_);
lean_dec(v_stx_2364_);
v_val_3342_ = lean_ctor_get(v_fst_3322_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v_fst_3322_, 1);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v_val_3342_);
v___x_3344_ = v___x_3320_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_val_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v___x_3311_);
lean_dec(v_stx_2364_);
v_a_3349_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3317_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3317_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3357_ = l_Lean_Syntax_getArg(v___x_3308_, v___x_3282_);
lean_dec(v___x_3308_);
v___x_3358_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3359_ = l_Lean_Syntax_isOfKind(v___x_3357_, v___x_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v_env_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_inc_n(v_stx_2364_, 2);
v___x_3360_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3361_ = lean_st_ref_get(v___y_3306_);
v_env_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc_ref(v_env_3362_);
lean_dec(v___x_3361_);
v___x_3363_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3364_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3363_, v_env_3362_, v___x_3360_);
v___x_3365_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3366_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3364_, v___x_3365_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___x_3364_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3397_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v_fst_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3395_; 
v_fst_3371_ = lean_ctor_get(v_a_3367_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_a_3367_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; 
v_unused_3396_ = lean_ctor_get(v_a_3367_, 1);
lean_dec(v_unused_3396_);
v___x_3373_ = v_a_3367_;
v_isShared_3374_ = v_isSharedCheck_3395_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_fst_3371_);
lean_dec(v_a_3367_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3395_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
if (lean_obj_tag(v_fst_3371_) == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3378_; 
lean_del_object(v___x_3369_);
v___x_3375_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3376_ = l_Lean_MessageData_ofName(v___x_3360_);
lean_inc_ref(v___x_3376_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set_tag(v___x_3373_, 7);
lean_ctor_set(v___x_3373_, 1, v___x_3376_);
lean_ctor_set(v___x_3373_, 0, v___x_3375_);
v___x_3378_ = v___x_3373_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3379_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3382_ = l_Lean_indentD(v___x_3381_);
v___x_3383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3380_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v___x_3376_);
v___x_3387_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3388_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
return v___x_3389_;
}
}
else
{
lean_object* v_val_3391_; lean_object* v___x_3393_; 
lean_del_object(v___x_3373_);
lean_dec(v___x_3360_);
lean_dec(v_stx_2364_);
v_val_3391_ = lean_ctor_get(v_fst_3371_, 0);
lean_inc(v_val_3391_);
lean_dec_ref_known(v_fst_3371_, 1);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v_val_3391_);
v___x_3393_ = v___x_3369_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_val_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v___x_3360_);
lean_dec(v_stx_2364_);
v_a_3398_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3366_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3366_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
v___y_3285_ = v___y_3301_;
v___y_3286_ = v___y_3302_;
v___y_3287_ = v___y_3303_;
v___y_3288_ = v___y_3304_;
v___y_3289_ = v___y_3305_;
v___y_3290_ = v___y_3306_;
goto v___jp_3284_;
}
}
}
else
{
lean_dec(v___x_3308_);
v___y_3285_ = v___y_3301_;
v___y_3286_ = v___y_3302_;
v___y_3287_ = v___y_3303_;
v___y_3288_ = v___y_3304_;
v___y_3289_ = v___y_3305_;
v___y_3290_ = v___y_3306_;
goto v___jp_3284_;
}
}
}
}
else
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3641_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
v___x_3504_ = lean_unsigned_to_nat(0u);
v___x_3505_ = lean_unsigned_to_nat(1u);
v___x_3790_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3505_);
v___x_3791_ = l_Lean_Syntax_getArgs(v___x_3790_);
lean_dec(v___x_3790_);
v___x_3792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3793_ = lean_array_get_size(v___x_3791_);
v___x_3794_ = lean_nat_dec_lt(v___x_3504_, v___x_3793_);
if (v___x_3794_ == 0)
{
lean_dec_ref(v___x_3791_);
v___y_3641_ = v___x_3792_;
goto v___jp_3640_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; size_t v___x_3797_; size_t v___x_3798_; lean_object* v___x_3799_; lean_object* v_snd_3800_; 
v___x_3795_ = lean_box(v___x_3794_);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v___x_3792_);
v___x_3797_ = ((size_t)0ULL);
v___x_3798_ = lean_usize_of_nat(v___x_3793_);
v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2696_, v___x_2694_, v___x_3791_, v___x_3797_, v___x_3798_, v___x_3796_);
lean_dec_ref(v___x_3791_);
v_snd_3800_ = lean_ctor_get(v___x_3799_, 1);
lean_inc(v_snd_3800_);
lean_dec_ref(v___x_3799_);
v___y_3641_ = v_snd_3800_;
goto v___jp_3640_;
}
v___jp_3506_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = lean_unsigned_to_nat(5u);
v___x_3514_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3513_);
lean_dec(v_stx_2364_);
v___x_3515_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3514_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3533_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3533_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3533_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
uint8_t v_returnsEarly_3520_; lean_object* v_reassigns_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3531_; 
v_returnsEarly_3520_ = lean_ctor_get_uint8(v_a_3516_, sizeof(void*)*2 + 2);
v_reassigns_3521_ = lean_ctor_get(v_a_3516_, 1);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_a_3516_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; 
v_unused_3532_ = lean_ctor_get(v_a_3516_, 0);
lean_dec(v_unused_3532_);
v___x_3523_ = v_a_3516_;
v_isShared_3524_ = v_isSharedCheck_3531_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_reassigns_3521_);
lean_dec(v_a_3516_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3531_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3505_);
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_reassigns_3521_);
lean_ctor_set_uint8(v_reuseFailAlloc_3530_, sizeof(void*)*2 + 2, v_returnsEarly_3520_);
v___x_3526_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*2, v___x_2694_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*2 + 1, v___x_2694_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*2 + 3, v___x_2694_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3526_);
v___x_3528_ = v___x_3518_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
else
{
return v___x_3515_;
}
}
v___jp_3534_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3541_ = lean_unsigned_to_nat(3u);
v___x_3542_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3541_);
v___x_3543_ = l_Lean_Syntax_isNone(v___x_3542_);
if (v___x_3543_ == 0)
{
uint8_t v___x_3544_; 
lean_inc(v___x_3542_);
v___x_3544_ = l_Lean_Syntax_matchesNull(v___x_3542_, v___x_3505_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v_env_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec(v___x_3542_);
lean_inc_n(v_stx_2364_, 2);
v___x_3545_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3546_ = lean_st_ref_get(v___y_3540_);
v_env_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc_ref(v_env_3547_);
lean_dec(v___x_3546_);
v___x_3548_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3549_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3548_, v_env_3547_, v___x_3545_);
v___x_3550_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3551_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3549_, v___x_3550_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___x_3549_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3582_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3582_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3582_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v_fst_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3580_; 
v_fst_3556_ = lean_ctor_get(v_a_3552_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_a_3552_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v_a_3552_, 1);
lean_dec(v_unused_3581_);
v___x_3558_ = v_a_3552_;
v_isShared_3559_ = v_isSharedCheck_3580_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_fst_3556_);
lean_dec(v_a_3552_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3580_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
if (lean_obj_tag(v_fst_3556_) == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
lean_del_object(v___x_3554_);
v___x_3560_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3561_ = l_Lean_MessageData_ofName(v___x_3545_);
lean_inc_ref(v___x_3561_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set_tag(v___x_3558_, 7);
lean_ctor_set(v___x_3558_, 1, v___x_3561_);
lean_ctor_set(v___x_3558_, 0, v___x_3560_);
v___x_3563_ = v___x_3558_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3564_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3563_);
lean_ctor_set(v___x_3565_, 1, v___x_3564_);
v___x_3566_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3567_ = l_Lean_indentD(v___x_3566_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3565_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
lean_ctor_set(v___x_3571_, 1, v___x_3561_);
v___x_3572_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3571_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3573_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
return v___x_3574_;
}
}
else
{
lean_object* v_val_3576_; lean_object* v___x_3578_; 
lean_del_object(v___x_3558_);
lean_dec(v___x_3545_);
lean_dec(v_stx_2364_);
v_val_3576_ = lean_ctor_get(v_fst_3556_, 0);
lean_inc(v_val_3576_);
lean_dec_ref_known(v_fst_3556_, 1);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_val_3576_);
v___x_3578_ = v___x_3554_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_val_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v___x_3545_);
lean_dec(v_stx_2364_);
v_a_3583_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3551_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3551_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v___x_3591_ = l_Lean_Syntax_getArg(v___x_3542_, v___x_3504_);
lean_dec(v___x_3542_);
v___x_3592_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3593_ = l_Lean_Syntax_isOfKind(v___x_3591_, v___x_3592_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v_env_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_inc_n(v_stx_2364_, 2);
v___x_3594_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3595_ = lean_st_ref_get(v___y_3540_);
v_env_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc_ref(v_env_3596_);
lean_dec(v___x_3595_);
v___x_3597_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3598_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3597_, v_env_3596_, v___x_3594_);
v___x_3599_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3600_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3598_, v___x_3599_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___x_3598_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3631_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3631_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3631_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_fst_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3629_; 
v_fst_3605_ = lean_ctor_get(v_a_3601_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_a_3601_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_a_3601_, 1);
lean_dec(v_unused_3630_);
v___x_3607_ = v_a_3601_;
v_isShared_3608_ = v_isSharedCheck_3629_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_fst_3605_);
lean_dec(v_a_3601_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3629_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
if (lean_obj_tag(v_fst_3605_) == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
lean_del_object(v___x_3603_);
v___x_3609_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3610_ = l_Lean_MessageData_ofName(v___x_3594_);
lean_inc_ref(v___x_3610_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 7);
lean_ctor_set(v___x_3607_, 1, v___x_3610_);
lean_ctor_set(v___x_3607_, 0, v___x_3609_);
v___x_3612_ = v___x_3607_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3613_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3616_ = l_Lean_indentD(v___x_3615_);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3614_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___x_3610_);
v___x_3621_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3622_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
return v___x_3623_;
}
}
else
{
lean_object* v_val_3625_; lean_object* v___x_3627_; 
lean_del_object(v___x_3607_);
lean_dec(v___x_3594_);
lean_dec(v_stx_2364_);
v_val_3625_ = lean_ctor_get(v_fst_3605_, 0);
lean_inc(v_val_3625_);
lean_dec_ref_known(v_fst_3605_, 1);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v_val_3625_);
v___x_3627_ = v___x_3603_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_val_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v___x_3594_);
lean_dec(v_stx_2364_);
v_a_3632_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3600_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3600_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
v___y_3507_ = v___y_3535_;
v___y_3508_ = v___y_3536_;
v___y_3509_ = v___y_3537_;
v___y_3510_ = v___y_3538_;
v___y_3511_ = v___y_3539_;
v___y_3512_ = v___y_3540_;
goto v___jp_3506_;
}
}
}
else
{
lean_dec(v___x_3542_);
v___y_3507_ = v___y_3535_;
v___y_3508_ = v___y_3536_;
v___y_3509_ = v___y_3537_;
v___y_3510_ = v___y_3538_;
v___y_3511_ = v___y_3539_;
v___y_3512_ = v___y_3540_;
goto v___jp_3506_;
}
}
v___jp_3640_:
{
size_t v_sz_3642_; size_t v___x_3643_; lean_object* v___x_3644_; 
v_sz_3642_ = lean_array_size(v___y_3641_);
v___x_3643_ = ((size_t)0ULL);
v___x_3644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3642_, v___x_3643_, v___y_3641_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_env_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_inc_n(v_stx_2364_, 2);
v___x_3645_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3646_ = lean_st_ref_get(v_a_2370_);
v_env_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc_ref(v_env_3647_);
lean_dec(v___x_3646_);
v___x_3648_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3649_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3648_, v_env_3647_, v___x_3645_);
v___x_3650_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3651_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3649_, v___x_3650_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3649_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3682_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3654_ = v___x_3651_;
v_isShared_3655_ = v_isSharedCheck_3682_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3682_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v_fst_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3680_; 
v_fst_3656_ = lean_ctor_get(v_a_3652_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_a_3652_);
if (v_isSharedCheck_3680_ == 0)
{
lean_object* v_unused_3681_; 
v_unused_3681_ = lean_ctor_get(v_a_3652_, 1);
lean_dec(v_unused_3681_);
v___x_3658_ = v_a_3652_;
v_isShared_3659_ = v_isSharedCheck_3680_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_fst_3656_);
lean_dec(v_a_3652_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3680_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
if (lean_obj_tag(v_fst_3656_) == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3663_; 
lean_del_object(v___x_3654_);
v___x_3660_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3661_ = l_Lean_MessageData_ofName(v___x_3645_);
lean_inc_ref(v___x_3661_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set_tag(v___x_3658_, 7);
lean_ctor_set(v___x_3658_, 1, v___x_3661_);
lean_ctor_set(v___x_3658_, 0, v___x_3660_);
v___x_3663_ = v___x_3658_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3664_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3663_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3667_ = l_Lean_indentD(v___x_3666_);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3665_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3668_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
lean_ctor_set(v___x_3671_, 1, v___x_3661_);
v___x_3672_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3671_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3673_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3674_;
}
}
else
{
lean_object* v_val_3676_; lean_object* v___x_3678_; 
lean_del_object(v___x_3658_);
lean_dec(v___x_3645_);
lean_dec(v_stx_2364_);
v_val_3676_ = lean_ctor_get(v_fst_3656_, 0);
lean_inc(v_val_3676_);
lean_dec_ref_known(v_fst_3656_, 1);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v_val_3676_);
v___x_3678_ = v___x_3654_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_val_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v___x_3645_);
lean_dec(v_stx_2364_);
v_a_3683_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3651_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3651_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
lean_dec_ref_known(v___x_3644_, 1);
v___x_3691_ = lean_unsigned_to_nat(2u);
v___x_3692_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3691_);
v___x_3693_ = l_Lean_Syntax_isNone(v___x_3692_);
if (v___x_3693_ == 0)
{
uint8_t v___x_3694_; 
lean_inc(v___x_3692_);
v___x_3694_ = l_Lean_Syntax_matchesNull(v___x_3692_, v___x_3505_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v_env_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
lean_dec(v___x_3692_);
lean_inc_n(v_stx_2364_, 2);
v___x_3695_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3696_ = lean_st_ref_get(v_a_2370_);
v_env_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc_ref(v_env_3697_);
lean_dec(v___x_3696_);
v___x_3698_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3699_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3698_, v_env_3697_, v___x_3695_);
v___x_3700_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3701_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3699_, v___x_3700_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3699_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3732_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3732_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3732_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v_fst_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3730_; 
v_fst_3706_ = lean_ctor_get(v_a_3702_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_a_3702_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v_a_3702_, 1);
lean_dec(v_unused_3731_);
v___x_3708_ = v_a_3702_;
v_isShared_3709_ = v_isSharedCheck_3730_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_fst_3706_);
lean_dec(v_a_3702_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3730_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
if (lean_obj_tag(v_fst_3706_) == 0)
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3713_; 
lean_del_object(v___x_3704_);
v___x_3710_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3711_ = l_Lean_MessageData_ofName(v___x_3695_);
lean_inc_ref(v___x_3711_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set_tag(v___x_3708_, 7);
lean_ctor_set(v___x_3708_, 1, v___x_3711_);
lean_ctor_set(v___x_3708_, 0, v___x_3710_);
v___x_3713_ = v___x_3708_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3714_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3717_ = l_Lean_indentD(v___x_3716_);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3715_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
lean_ctor_set(v___x_3721_, 1, v___x_3711_);
v___x_3722_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3723_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3724_;
}
}
else
{
lean_object* v_val_3726_; lean_object* v___x_3728_; 
lean_del_object(v___x_3708_);
lean_dec(v___x_3695_);
lean_dec(v_stx_2364_);
v_val_3726_ = lean_ctor_get(v_fst_3706_, 0);
lean_inc(v_val_3726_);
lean_dec_ref_known(v_fst_3706_, 1);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v_val_3726_);
v___x_3728_ = v___x_3704_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_val_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec(v___x_3695_);
lean_dec(v_stx_2364_);
v_a_3733_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3701_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3701_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v___x_3741_ = l_Lean_Syntax_getArg(v___x_3692_, v___x_3504_);
lean_dec(v___x_3692_);
v___x_3742_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3743_ = l_Lean_Syntax_isOfKind(v___x_3741_, v___x_3742_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v_env_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_inc_n(v_stx_2364_, 2);
v___x_3744_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3745_ = lean_st_ref_get(v_a_2370_);
v_env_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc_ref(v_env_3746_);
lean_dec(v___x_3745_);
v___x_3747_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3748_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3747_, v_env_3746_, v___x_3744_);
v___x_3749_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3750_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3748_, v___x_3749_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3748_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3781_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3753_ = v___x_3750_;
v_isShared_3754_ = v_isSharedCheck_3781_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3781_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v_fst_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3779_; 
v_fst_3755_ = lean_ctor_get(v_a_3751_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3751_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; 
v_unused_3780_ = lean_ctor_get(v_a_3751_, 1);
lean_dec(v_unused_3780_);
v___x_3757_ = v_a_3751_;
v_isShared_3758_ = v_isSharedCheck_3779_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_fst_3755_);
lean_dec(v_a_3751_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3779_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
if (lean_obj_tag(v_fst_3755_) == 0)
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3762_; 
lean_del_object(v___x_3753_);
v___x_3759_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3760_ = l_Lean_MessageData_ofName(v___x_3744_);
lean_inc_ref(v___x_3760_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set_tag(v___x_3757_, 7);
lean_ctor_set(v___x_3757_, 1, v___x_3760_);
lean_ctor_set(v___x_3757_, 0, v___x_3759_);
v___x_3762_ = v___x_3757_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3759_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3763_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3766_ = l_Lean_indentD(v___x_3765_);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3764_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
lean_ctor_set(v___x_3770_, 1, v___x_3760_);
v___x_3771_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3770_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3772_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3773_;
}
}
else
{
lean_object* v_val_3775_; lean_object* v___x_3777_; 
lean_del_object(v___x_3757_);
lean_dec(v___x_3744_);
lean_dec(v_stx_2364_);
v_val_3775_ = lean_ctor_get(v_fst_3755_, 0);
lean_inc(v_val_3775_);
lean_dec_ref_known(v_fst_3755_, 1);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v_val_3775_);
v___x_3777_ = v___x_3753_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_val_3775_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec(v___x_3744_);
lean_dec(v_stx_2364_);
v_a_3782_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3750_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3750_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
else
{
v___y_3535_ = v_a_2365_;
v___y_3536_ = v_a_2366_;
v___y_3537_ = v_a_2367_;
v___y_3538_ = v_a_2368_;
v___y_3539_ = v_a_2369_;
v___y_3540_ = v_a_2370_;
goto v___jp_3534_;
}
}
}
else
{
lean_dec(v___x_3692_);
v___y_3535_ = v_a_2365_;
v___y_3536_ = v_a_2366_;
v___y_3537_ = v_a_2367_;
v___y_3538_ = v_a_2368_;
v___y_3539_ = v_a_2369_;
v___y_3540_ = v_a_2370_;
goto v___jp_3534_;
}
}
}
}
v___jp_2697_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2702_, 0, v___y_2700_);
lean_ctor_set(v___x_2702_, 1, v___y_2699_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*2, v___x_2696_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*2 + 1, v___x_2696_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*2 + 2, v___y_2698_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*2 + 3, v___y_2701_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3801_ = lean_unsigned_to_nat(1u);
v___x_3802_ = lean_unsigned_to_nat(3u);
v___x_3803_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3802_);
lean_dec(v_stx_2364_);
v___x_3804_ = l_Lean_NameSet_empty;
v___x_3805_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3805_, 0, v___x_3801_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
lean_ctor_set_uint8(v___x_3805_, sizeof(void*)*2, v___x_2692_);
lean_ctor_set_uint8(v___x_3805_, sizeof(void*)*2 + 1, v___x_2692_);
lean_ctor_set_uint8(v___x_3805_, sizeof(void*)*2 + 2, v___x_2692_);
lean_ctor_set_uint8(v___x_3805_, sizeof(void*)*2 + 3, v___x_2692_);
v___x_3806_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3803_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3815_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3809_ = v___x_3806_;
v_isShared_3810_ = v_isSharedCheck_3815_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3815_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3805_, v_a_3807_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3811_);
v___x_3813_ = v___x_3809_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
else
{
lean_dec_ref_known(v___x_3805_, 2);
return v___x_3806_;
}
}
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; size_t v_sz_3819_; size_t v___x_3820_; lean_object* v___x_3821_; 
v___x_3816_ = lean_unsigned_to_nat(4u);
v___x_3817_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3816_);
v___x_3818_ = l_Lean_Syntax_getArgs(v___x_3817_);
lean_dec(v___x_3817_);
v_sz_3819_ = lean_array_size(v___x_3818_);
v___x_3820_ = ((size_t)0ULL);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3819_, v___x_3820_, v___x_3818_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v_env_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_inc_n(v_stx_2364_, 2);
v___x_3822_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3823_ = lean_st_ref_get(v_a_2370_);
v_env_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc_ref(v_env_3824_);
lean_dec(v___x_3823_);
v___x_3825_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3826_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3825_, v_env_3824_, v___x_3822_);
v___x_3827_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3828_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3826_, v___x_3827_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3826_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3859_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3859_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3859_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v_fst_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3857_; 
v_fst_3833_ = lean_ctor_get(v_a_3829_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_a_3829_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; 
v_unused_3858_ = lean_ctor_get(v_a_3829_, 1);
lean_dec(v_unused_3858_);
v___x_3835_ = v_a_3829_;
v_isShared_3836_ = v_isSharedCheck_3857_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_fst_3833_);
lean_dec(v_a_3829_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3857_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
if (lean_obj_tag(v_fst_3833_) == 0)
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
lean_del_object(v___x_3831_);
v___x_3837_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3838_ = l_Lean_MessageData_ofName(v___x_3822_);
lean_inc_ref(v___x_3838_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 7);
lean_ctor_set(v___x_3835_, 1, v___x_3838_);
lean_ctor_set(v___x_3835_, 0, v___x_3837_);
v___x_3840_ = v___x_3835_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3841_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3844_ = l_Lean_indentD(v___x_3843_);
v___x_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3842_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
lean_ctor_set(v___x_3848_, 1, v___x_3838_);
v___x_3849_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3850_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3851_;
}
}
else
{
lean_object* v_val_3853_; lean_object* v___x_3855_; 
lean_del_object(v___x_3835_);
lean_dec(v___x_3822_);
lean_dec(v_stx_2364_);
v_val_3853_ = lean_ctor_get(v_fst_3833_, 0);
lean_inc(v_val_3853_);
lean_dec_ref_known(v_fst_3833_, 1);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v_val_3853_);
v___x_3855_ = v___x_3831_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_val_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v___x_3822_);
lean_dec(v_stx_2364_);
v_a_3860_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3828_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3828_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v_val_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3955_; 
v_val_3868_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3870_ = v___x_3821_;
v_isShared_3871_ = v_isSharedCheck_3955_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_val_3868_);
lean_dec(v___x_3821_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3955_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v_elseSeq_x3f_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3872_ = lean_unsigned_to_nat(3u);
v___x_3873_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3872_);
v___x_3898_ = lean_unsigned_to_nat(5u);
v___x_3899_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3898_);
v___x_3900_ = l_Lean_Syntax_isNone(v___x_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; uint8_t v___x_3902_; 
v___x_3901_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3899_);
v___x_3902_ = l_Lean_Syntax_matchesNull(v___x_3899_, v___x_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v_env_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec(v___x_3899_);
lean_dec(v___x_3873_);
lean_del_object(v___x_3870_);
lean_dec(v_val_3868_);
lean_inc_n(v_stx_2364_, 2);
v___x_3903_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3904_ = lean_st_ref_get(v_a_2370_);
v_env_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc_ref(v_env_3905_);
lean_dec(v___x_3904_);
v___x_3906_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3907_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3906_, v_env_3905_, v___x_3903_);
v___x_3908_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3909_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3907_, v___x_3908_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_3907_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3940_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3912_ = v___x_3909_;
v_isShared_3913_ = v_isSharedCheck_3940_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3909_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3940_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v_fst_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3938_; 
v_fst_3914_ = lean_ctor_get(v_a_3910_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_a_3910_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; 
v_unused_3939_ = lean_ctor_get(v_a_3910_, 1);
lean_dec(v_unused_3939_);
v___x_3916_ = v_a_3910_;
v_isShared_3917_ = v_isSharedCheck_3938_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_fst_3914_);
lean_dec(v_a_3910_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3938_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
if (lean_obj_tag(v_fst_3914_) == 0)
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
lean_del_object(v___x_3912_);
v___x_3918_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3919_ = l_Lean_MessageData_ofName(v___x_3903_);
lean_inc_ref(v___x_3919_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set_tag(v___x_3916_, 7);
lean_ctor_set(v___x_3916_, 1, v___x_3919_);
lean_ctor_set(v___x_3916_, 0, v___x_3918_);
v___x_3921_ = v___x_3916_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3922_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3925_ = l_Lean_indentD(v___x_3924_);
v___x_3926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3923_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3926_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
v___x_3929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set(v___x_3929_, 1, v___x_3919_);
v___x_3930_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3929_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3931_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_3932_;
}
}
else
{
lean_object* v_val_3934_; lean_object* v___x_3936_; 
lean_del_object(v___x_3916_);
lean_dec(v___x_3903_);
lean_dec(v_stx_2364_);
v_val_3934_ = lean_ctor_get(v_fst_3914_, 0);
lean_inc(v_val_3934_);
lean_dec_ref_known(v_fst_3914_, 1);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v_val_3934_);
v___x_3936_ = v___x_3912_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_val_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec(v___x_3903_);
lean_dec(v_stx_2364_);
v_a_3941_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3909_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3909_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3952_; 
lean_dec(v_stx_2364_);
v___x_3949_ = lean_unsigned_to_nat(1u);
v___x_3950_ = l_Lean_Syntax_getArg(v___x_3899_, v___x_3949_);
lean_dec(v___x_3899_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3950_);
v___x_3952_ = v___x_3870_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
v_elseSeq_x3f_3875_ = v___x_3952_;
v___y_3876_ = v_a_2365_;
v___y_3877_ = v_a_2366_;
v___y_3878_ = v_a_2367_;
v___y_3879_ = v_a_2368_;
v___y_3880_ = v_a_2369_;
v___y_3881_ = v_a_2370_;
goto v___jp_3874_;
}
}
}
else
{
lean_object* v___x_3954_; 
lean_dec(v___x_3899_);
lean_del_object(v___x_3870_);
lean_dec(v_stx_2364_);
v___x_3954_ = lean_box(0);
v_elseSeq_x3f_3875_ = v___x_3954_;
v___y_3876_ = v_a_2365_;
v___y_3877_ = v_a_2366_;
v___y_3878_ = v_a_2367_;
v___y_3879_ = v_a_2368_;
v___y_3880_ = v_a_2369_;
v___y_3881_ = v_a_2370_;
goto v___jp_3874_;
}
v___jp_3874_:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; size_t v_sz_3885_; lean_object* v___x_3886_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
v___x_3884_ = l_Array_reverse___redArg(v_val_3868_);
v_sz_3885_ = lean_array_size(v___x_3884_);
v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3884_, v_sz_3885_, v___x_3820_, v_a_3883_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
lean_dec_ref(v___x_3884_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3873_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3897_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3891_ = v___x_3888_;
v_isShared_3892_ = v_isSharedCheck_3897_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3888_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3897_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3893_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3889_, v_a_3887_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v___x_3893_);
v___x_3895_ = v___x_3891_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
else
{
lean_dec(v_a_3887_);
return v___x_3888_;
}
}
else
{
lean_dec(v___x_3873_);
return v___x_3886_;
}
}
else
{
lean_dec(v___x_3873_);
lean_dec(v_val_3868_);
return v___x_3882_;
}
}
}
}
}
}
else
{
lean_object* v___x_3956_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___x_4020_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
v___x_3956_ = lean_unsigned_to_nat(0u);
v___x_4020_ = lean_unsigned_to_nat(1u);
v___x_4127_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4020_);
v___x_4128_ = l_Lean_Syntax_isNone(v___x_4127_);
if (v___x_4128_ == 0)
{
uint8_t v___x_4129_; 
lean_inc(v___x_4127_);
v___x_4129_ = l_Lean_Syntax_matchesNull(v___x_4127_, v___x_4020_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v_env_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_dec(v___x_4127_);
lean_inc_n(v_stx_2364_, 2);
v___x_4130_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4131_ = lean_st_ref_get(v_a_2370_);
v_env_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc_ref(v_env_4132_);
lean_dec(v___x_4131_);
v___x_4133_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4134_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4133_, v_env_4132_, v___x_4130_);
v___x_4135_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4136_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4134_, v___x_4135_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4134_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4167_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4139_ = v___x_4136_;
v_isShared_4140_ = v_isSharedCheck_4167_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4167_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v_fst_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4165_; 
v_fst_4141_ = lean_ctor_get(v_a_4137_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_a_4137_);
if (v_isSharedCheck_4165_ == 0)
{
lean_object* v_unused_4166_; 
v_unused_4166_ = lean_ctor_get(v_a_4137_, 1);
lean_dec(v_unused_4166_);
v___x_4143_ = v_a_4137_;
v_isShared_4144_ = v_isSharedCheck_4165_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_fst_4141_);
lean_dec(v_a_4137_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4165_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
if (lean_obj_tag(v_fst_4141_) == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4148_; 
lean_del_object(v___x_4139_);
v___x_4145_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4146_ = l_Lean_MessageData_ofName(v___x_4130_);
lean_inc_ref(v___x_4146_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set_tag(v___x_4143_, 7);
lean_ctor_set(v___x_4143_, 1, v___x_4146_);
lean_ctor_set(v___x_4143_, 0, v___x_4145_);
v___x_4148_ = v___x_4143_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4145_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4149_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4148_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4152_ = l_Lean_indentD(v___x_4151_);
v___x_4153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4150_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4153_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
lean_ctor_set(v___x_4156_, 1, v___x_4146_);
v___x_4157_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4158_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4159_;
}
}
else
{
lean_object* v_val_4161_; lean_object* v___x_4163_; 
lean_del_object(v___x_4143_);
lean_dec(v___x_4130_);
lean_dec(v_stx_2364_);
v_val_4161_ = lean_ctor_get(v_fst_4141_, 0);
lean_inc(v_val_4161_);
lean_dec_ref_known(v_fst_4141_, 1);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v_val_4161_);
v___x_4163_ = v___x_4139_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_val_4161_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v___x_4130_);
lean_dec(v_stx_2364_);
v_a_4168_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4136_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4136_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; 
v___x_4176_ = l_Lean_Syntax_getArg(v___x_4127_, v___x_3956_);
lean_dec(v___x_4127_);
v___x_4177_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4178_ = l_Lean_Syntax_isOfKind(v___x_4176_, v___x_4177_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v_env_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4179_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4180_ = lean_st_ref_get(v_a_2370_);
v_env_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc_ref(v_env_4181_);
lean_dec(v___x_4180_);
v___x_4182_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4183_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4182_, v_env_4181_, v___x_4179_);
v___x_4184_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4185_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4183_, v___x_4184_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4183_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4216_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4188_ = v___x_4185_;
v_isShared_4189_ = v_isSharedCheck_4216_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4216_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v_fst_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4214_; 
v_fst_4190_ = lean_ctor_get(v_a_4186_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_a_4186_);
if (v_isSharedCheck_4214_ == 0)
{
lean_object* v_unused_4215_; 
v_unused_4215_ = lean_ctor_get(v_a_4186_, 1);
lean_dec(v_unused_4215_);
v___x_4192_ = v_a_4186_;
v_isShared_4193_ = v_isSharedCheck_4214_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_fst_4190_);
lean_dec(v_a_4186_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4214_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
if (lean_obj_tag(v_fst_4190_) == 0)
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
lean_del_object(v___x_4188_);
v___x_4194_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4195_ = l_Lean_MessageData_ofName(v___x_4179_);
lean_inc_ref(v___x_4195_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set_tag(v___x_4192_, 7);
lean_ctor_set(v___x_4192_, 1, v___x_4195_);
lean_ctor_set(v___x_4192_, 0, v___x_4194_);
v___x_4197_ = v___x_4192_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4198_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4197_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4201_ = l_Lean_indentD(v___x_4200_);
v___x_4202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4199_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4202_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
lean_ctor_set(v___x_4205_, 1, v___x_4195_);
v___x_4206_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4205_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
v___x_4208_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4207_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4208_;
}
}
else
{
lean_object* v_val_4210_; lean_object* v___x_4212_; 
lean_del_object(v___x_4192_);
lean_dec(v___x_4179_);
lean_dec(v_stx_2364_);
v_val_4210_ = lean_ctor_get(v_fst_4190_, 0);
lean_inc(v_val_4210_);
lean_dec_ref_known(v_fst_4190_, 1);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v_val_4210_);
v___x_4212_ = v___x_4188_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_val_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v___x_4179_);
lean_dec(v_stx_2364_);
v_a_4217_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4185_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4185_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
v___y_4022_ = v_a_2365_;
v___y_4023_ = v_a_2366_;
v___y_4024_ = v_a_2367_;
v___y_4025_ = v_a_2368_;
v___y_4026_ = v_a_2369_;
v___y_4027_ = v_a_2370_;
goto v___jp_4021_;
}
}
}
else
{
lean_dec(v___x_4127_);
v___y_4022_ = v_a_2365_;
v___y_4023_ = v_a_2366_;
v___y_4024_ = v_a_2367_;
v___y_4025_ = v_a_2368_;
v___y_4026_ = v_a_2369_;
v___y_4027_ = v_a_2370_;
goto v___jp_4021_;
}
v___jp_3957_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3964_ = lean_unsigned_to_nat(6u);
v___x_3965_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_3964_);
v___x_3966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3965_);
v___x_3967_ = l_Lean_Syntax_isOfKind(v___x_3965_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v_env_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec(v___x_3965_);
lean_inc_n(v_stx_2364_, 2);
v___x_3968_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_3969_ = lean_st_ref_get(v___y_3963_);
v_env_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc_ref(v_env_3970_);
lean_dec(v___x_3969_);
v___x_3971_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3972_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3971_, v_env_3970_, v___x_3968_);
v___x_3973_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3974_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_3972_, v___x_3973_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
lean_dec(v___x_3972_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4005_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3977_ = v___x_3974_;
v_isShared_3978_ = v_isSharedCheck_4005_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4005_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v_fst_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4003_; 
v_fst_3979_ = lean_ctor_get(v_a_3975_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_a_3975_);
if (v_isSharedCheck_4003_ == 0)
{
lean_object* v_unused_4004_; 
v_unused_4004_ = lean_ctor_get(v_a_3975_, 1);
lean_dec(v_unused_4004_);
v___x_3981_ = v_a_3975_;
v_isShared_3982_ = v_isSharedCheck_4003_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_fst_3979_);
lean_dec(v_a_3975_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4003_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
if (lean_obj_tag(v_fst_3979_) == 0)
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
lean_del_object(v___x_3977_);
v___x_3983_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3984_ = l_Lean_MessageData_ofName(v___x_3968_);
lean_inc_ref(v___x_3984_);
if (v_isShared_3982_ == 0)
{
lean_ctor_set_tag(v___x_3981_, 7);
lean_ctor_set(v___x_3981_, 1, v___x_3984_);
lean_ctor_set(v___x_3981_, 0, v___x_3983_);
v___x_3986_ = v___x_3981_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3983_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3987_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3986_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_3990_ = l_Lean_indentD(v___x_3989_);
v___x_3991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3988_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3991_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
lean_ctor_set(v___x_3994_, 1, v___x_3984_);
v___x_3995_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3996_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
return v___x_3997_;
}
}
else
{
lean_object* v_val_3999_; lean_object* v___x_4001_; 
lean_del_object(v___x_3981_);
lean_dec(v___x_3968_);
lean_dec(v_stx_2364_);
v_val_3999_ = lean_ctor_get(v_fst_3979_, 0);
lean_inc(v_val_3999_);
lean_dec_ref_known(v_fst_3979_, 1);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v_val_3999_);
v___x_4001_ = v___x_3977_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_val_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec(v___x_3968_);
lean_dec(v_stx_2364_);
v_a_4006_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3974_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3974_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; size_t v_sz_4017_; size_t v___x_4018_; lean_object* v___x_4019_; 
lean_dec(v_stx_2364_);
v___x_4014_ = l_Lean_Syntax_getArg(v___x_3965_, v___x_3956_);
lean_dec(v___x_3965_);
v___x_4015_ = l_Lean_Syntax_getArgs(v___x_4014_);
lean_dec(v___x_4014_);
v___x_4016_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_4017_ = lean_array_size(v___x_4015_);
v___x_4018_ = ((size_t)0ULL);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2688_, v___x_4015_, v_sz_4017_, v___x_4018_, v___x_4016_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
lean_dec_ref(v___x_4015_);
return v___x_4019_;
}
}
v___jp_4021_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; 
v___x_4028_ = lean_unsigned_to_nat(2u);
v___x_4029_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4028_);
v___x_4030_ = l_Lean_Syntax_isNone(v___x_4029_);
if (v___x_4030_ == 0)
{
uint8_t v___x_4031_; 
lean_inc(v___x_4029_);
v___x_4031_ = l_Lean_Syntax_matchesNull(v___x_4029_, v___x_4020_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v_env_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
lean_dec(v___x_4029_);
lean_inc_n(v_stx_2364_, 2);
v___x_4032_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4033_ = lean_st_ref_get(v___y_4027_);
v_env_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc_ref(v_env_4034_);
lean_dec(v___x_4033_);
v___x_4035_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4036_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4035_, v_env_4034_, v___x_4032_);
v___x_4037_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4038_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4036_, v___x_4037_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec(v___x_4036_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4069_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4041_ = v___x_4038_;
v_isShared_4042_ = v_isSharedCheck_4069_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4038_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4069_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v_fst_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4067_; 
v_fst_4043_ = lean_ctor_get(v_a_4039_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_a_4039_);
if (v_isSharedCheck_4067_ == 0)
{
lean_object* v_unused_4068_; 
v_unused_4068_ = lean_ctor_get(v_a_4039_, 1);
lean_dec(v_unused_4068_);
v___x_4045_ = v_a_4039_;
v_isShared_4046_ = v_isSharedCheck_4067_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_fst_4043_);
lean_dec(v_a_4039_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4067_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
if (lean_obj_tag(v_fst_4043_) == 0)
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4050_; 
lean_del_object(v___x_4041_);
v___x_4047_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4048_ = l_Lean_MessageData_ofName(v___x_4032_);
lean_inc_ref(v___x_4048_);
if (v_isShared_4046_ == 0)
{
lean_ctor_set_tag(v___x_4045_, 7);
lean_ctor_set(v___x_4045_, 1, v___x_4048_);
lean_ctor_set(v___x_4045_, 0, v___x_4047_);
v___x_4050_ = v___x_4045_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4051_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4054_ = l_Lean_indentD(v___x_4053_);
v___x_4055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4052_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
v___x_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
lean_ctor_set(v___x_4058_, 1, v___x_4048_);
v___x_4059_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4058_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
v___x_4061_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4060_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
return v___x_4061_;
}
}
else
{
lean_object* v_val_4063_; lean_object* v___x_4065_; 
lean_del_object(v___x_4045_);
lean_dec(v___x_4032_);
lean_dec(v_stx_2364_);
v_val_4063_ = lean_ctor_get(v_fst_4043_, 0);
lean_inc(v_val_4063_);
lean_dec_ref_known(v_fst_4043_, 1);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v_val_4063_);
v___x_4065_ = v___x_4041_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_val_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec(v___x_4032_);
lean_dec(v_stx_2364_);
v_a_4070_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4038_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4038_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; 
v___x_4078_ = l_Lean_Syntax_getArg(v___x_4029_, v___x_3956_);
lean_dec(v___x_4029_);
v___x_4079_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
v___x_4080_ = l_Lean_Syntax_isOfKind(v___x_4078_, v___x_4079_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v_env_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4081_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4082_ = lean_st_ref_get(v___y_4027_);
v_env_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc_ref(v_env_4083_);
lean_dec(v___x_4082_);
v___x_4084_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4085_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4084_, v_env_4083_, v___x_4081_);
v___x_4086_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4087_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4085_, v___x_4086_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec(v___x_4085_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4118_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4118_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4118_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v_fst_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4116_; 
v_fst_4092_ = lean_ctor_get(v_a_4088_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_a_4088_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; 
v_unused_4117_ = lean_ctor_get(v_a_4088_, 1);
lean_dec(v_unused_4117_);
v___x_4094_ = v_a_4088_;
v_isShared_4095_ = v_isSharedCheck_4116_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_fst_4092_);
lean_dec(v_a_4088_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4116_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
if (lean_obj_tag(v_fst_4092_) == 0)
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4099_; 
lean_del_object(v___x_4090_);
v___x_4096_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4097_ = l_Lean_MessageData_ofName(v___x_4081_);
lean_inc_ref(v___x_4097_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set_tag(v___x_4094_, 7);
lean_ctor_set(v___x_4094_, 1, v___x_4097_);
lean_ctor_set(v___x_4094_, 0, v___x_4096_);
v___x_4099_ = v___x_4094_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4096_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v___x_4097_);
v___x_4099_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4100_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4099_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4103_ = l_Lean_indentD(v___x_4102_);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4101_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___x_4107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
lean_ctor_set(v___x_4107_, 1, v___x_4097_);
v___x_4108_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4107_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4109_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
return v___x_4110_;
}
}
else
{
lean_object* v_val_4112_; lean_object* v___x_4114_; 
lean_del_object(v___x_4094_);
lean_dec(v___x_4081_);
lean_dec(v_stx_2364_);
v_val_4112_ = lean_ctor_get(v_fst_4092_, 0);
lean_inc(v_val_4112_);
lean_dec_ref_known(v_fst_4092_, 1);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v_val_4112_);
v___x_4114_ = v___x_4090_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_val_4112_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec(v___x_4081_);
lean_dec(v_stx_2364_);
v_a_4119_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4087_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4087_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
else
{
v___y_3958_ = v___y_4022_;
v___y_3959_ = v___y_4023_;
v___y_3960_ = v___y_4024_;
v___y_3961_ = v___y_4025_;
v___y_3962_ = v___y_4026_;
v___y_3963_ = v___y_4027_;
goto v___jp_3957_;
}
}
}
else
{
lean_dec(v___x_4029_);
v___y_3958_ = v___y_4022_;
v___y_3959_ = v___y_4023_;
v___y_3960_ = v___y_4024_;
v___y_3961_ = v___y_4025_;
v___y_3962_ = v___y_4026_;
v___y_3963_ = v___y_4027_;
goto v___jp_3957_;
}
}
}
}
else
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; uint8_t v___x_4228_; 
v___x_4225_ = lean_unsigned_to_nat(0u);
v___x_4226_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4225_);
v___x_4227_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_4226_);
v___x_4228_ = l_Lean_Syntax_isOfKind(v___x_4226_, v___x_4227_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; uint8_t v___x_4230_; 
v___x_4229_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_4226_);
v___x_4230_ = l_Lean_Syntax_isOfKind(v___x_4226_, v___x_4229_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v_env_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
lean_dec(v___x_4226_);
lean_inc_n(v_stx_2364_, 2);
v___x_4231_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4232_ = lean_st_ref_get(v_a_2370_);
v_env_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc_ref(v_env_4233_);
lean_dec(v___x_4232_);
v___x_4234_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4235_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4234_, v_env_4233_, v___x_4231_);
v___x_4236_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4237_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4235_, v___x_4236_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4235_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4268_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4268_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4268_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v_fst_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4266_; 
v_fst_4242_ = lean_ctor_get(v_a_4238_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_a_4238_);
if (v_isSharedCheck_4266_ == 0)
{
lean_object* v_unused_4267_; 
v_unused_4267_ = lean_ctor_get(v_a_4238_, 1);
lean_dec(v_unused_4267_);
v___x_4244_ = v_a_4238_;
v_isShared_4245_ = v_isSharedCheck_4266_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_fst_4242_);
lean_dec(v_a_4238_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4266_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
if (lean_obj_tag(v_fst_4242_) == 0)
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4249_; 
lean_del_object(v___x_4240_);
v___x_4246_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4247_ = l_Lean_MessageData_ofName(v___x_4231_);
lean_inc_ref(v___x_4247_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set_tag(v___x_4244_, 7);
lean_ctor_set(v___x_4244_, 1, v___x_4247_);
lean_ctor_set(v___x_4244_, 0, v___x_4246_);
v___x_4249_ = v___x_4244_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4250_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4249_);
lean_ctor_set(v___x_4251_, 1, v___x_4250_);
v___x_4252_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4253_ = l_Lean_indentD(v___x_4252_);
v___x_4254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4251_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
v___x_4255_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4254_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v___x_4257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
lean_ctor_set(v___x_4257_, 1, v___x_4247_);
v___x_4258_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4257_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
v___x_4260_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4259_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4260_;
}
}
else
{
lean_object* v_val_4262_; lean_object* v___x_4264_; 
lean_del_object(v___x_4244_);
lean_dec(v___x_4231_);
lean_dec(v_stx_2364_);
v_val_4262_ = lean_ctor_get(v_fst_4242_, 0);
lean_inc(v_val_4262_);
lean_dec_ref_known(v_fst_4242_, 1);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v_val_4262_);
v___x_4264_ = v___x_4240_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_val_4262_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec(v___x_4231_);
lean_dec(v_stx_2364_);
v_a_4269_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4237_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4237_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
else
{
lean_object* v___x_4277_; 
lean_dec(v_stx_2364_);
v___x_4277_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2604_, v___x_4226_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4277_;
}
}
else
{
lean_object* v___x_4278_; 
lean_dec(v_stx_2364_);
v___x_4278_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2604_, v___x_4226_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4278_;
}
}
}
else
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; uint8_t v___x_4282_; 
v___x_4279_ = lean_unsigned_to_nat(0u);
v___x_4280_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4279_);
v___x_4281_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84));
lean_inc(v___x_4280_);
v___x_4282_ = l_Lean_Syntax_isOfKind(v___x_4280_, v___x_4281_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4283_; uint8_t v___x_4284_; 
v___x_4283_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86));
lean_inc(v___x_4280_);
v___x_4284_ = l_Lean_Syntax_isOfKind(v___x_4280_, v___x_4283_);
if (v___x_4284_ == 0)
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v_env_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
lean_dec(v___x_4280_);
lean_inc_n(v_stx_2364_, 2);
v___x_4285_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4286_ = lean_st_ref_get(v_a_2370_);
v_env_4287_ = lean_ctor_get(v___x_4286_, 0);
lean_inc_ref(v_env_4287_);
lean_dec(v___x_4286_);
v___x_4288_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4289_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4288_, v_env_4287_, v___x_4285_);
v___x_4290_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4291_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4289_, v___x_4290_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4289_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4322_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4294_ = v___x_4291_;
v_isShared_4295_ = v_isSharedCheck_4322_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4291_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4322_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v_fst_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4320_; 
v_fst_4296_ = lean_ctor_get(v_a_4292_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_a_4292_);
if (v_isSharedCheck_4320_ == 0)
{
lean_object* v_unused_4321_; 
v_unused_4321_ = lean_ctor_get(v_a_4292_, 1);
lean_dec(v_unused_4321_);
v___x_4298_ = v_a_4292_;
v_isShared_4299_ = v_isSharedCheck_4320_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_fst_4296_);
lean_dec(v_a_4292_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4320_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
if (lean_obj_tag(v_fst_4296_) == 0)
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4303_; 
lean_del_object(v___x_4294_);
v___x_4300_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4301_ = l_Lean_MessageData_ofName(v___x_4285_);
lean_inc_ref(v___x_4301_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set_tag(v___x_4298_, 7);
lean_ctor_set(v___x_4298_, 1, v___x_4301_);
lean_ctor_set(v___x_4298_, 0, v___x_4300_);
v___x_4303_ = v___x_4298_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4300_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v___x_4301_);
v___x_4303_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4304_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4307_ = l_Lean_indentD(v___x_4306_);
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4305_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4308_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
v___x_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
lean_ctor_set(v___x_4311_, 1, v___x_4301_);
v___x_4312_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
v___x_4314_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4313_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4314_;
}
}
else
{
lean_object* v_val_4316_; lean_object* v___x_4318_; 
lean_del_object(v___x_4298_);
lean_dec(v___x_4285_);
lean_dec(v_stx_2364_);
v_val_4316_ = lean_ctor_get(v_fst_4296_, 0);
lean_inc(v_val_4316_);
lean_dec_ref_known(v_fst_4296_, 1);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v_val_4316_);
v___x_4318_ = v___x_4294_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_val_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v___x_4285_);
lean_dec(v_stx_2364_);
v_a_4323_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4291_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4291_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_object* v___x_4331_; 
lean_dec(v_stx_2364_);
v___x_4331_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_4280_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4280_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4331_, 1);
v___x_4333_ = lean_box(0);
v___x_4334_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4332_, v___x_4333_, v___x_4333_, v___x_4333_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4334_;
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
v_a_4335_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4331_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4331_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
}
else
{
lean_object* v___x_4343_; 
lean_dec(v_stx_2364_);
v___x_4343_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_4280_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4280_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v_a_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4344_);
lean_dec_ref_known(v___x_4343_, 1);
v___x_4345_ = lean_box(0);
v___x_4346_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4344_, v___x_4345_, v___x_4345_, v___x_4345_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4346_;
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
v_a_4347_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4343_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4343_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
}
else
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4355_ = lean_unsigned_to_nat(0u);
v___x_4356_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4355_);
v___x_4357_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88));
lean_inc(v___x_4356_);
v___x_4358_ = l_Lean_Syntax_isOfKind(v___x_4356_, v___x_4357_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v_env_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
lean_dec(v___x_4356_);
lean_inc_n(v_stx_2364_, 2);
v___x_4359_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4360_ = lean_st_ref_get(v_a_2370_);
v_env_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc_ref(v_env_4361_);
lean_dec(v___x_4360_);
v___x_4362_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4363_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4362_, v_env_4361_, v___x_4359_);
v___x_4364_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4365_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4363_, v___x_4364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4363_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4396_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4396_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4396_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v_fst_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4394_; 
v_fst_4370_ = lean_ctor_get(v_a_4366_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_a_4366_);
if (v_isSharedCheck_4394_ == 0)
{
lean_object* v_unused_4395_; 
v_unused_4395_ = lean_ctor_get(v_a_4366_, 1);
lean_dec(v_unused_4395_);
v___x_4372_ = v_a_4366_;
v_isShared_4373_ = v_isSharedCheck_4394_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_fst_4370_);
lean_dec(v_a_4366_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4394_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
if (lean_obj_tag(v_fst_4370_) == 0)
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4377_; 
lean_del_object(v___x_4368_);
v___x_4374_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4375_ = l_Lean_MessageData_ofName(v___x_4359_);
lean_inc_ref(v___x_4375_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set_tag(v___x_4372_, 7);
lean_ctor_set(v___x_4372_, 1, v___x_4375_);
lean_ctor_set(v___x_4372_, 0, v___x_4374_);
v___x_4377_ = v___x_4372_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4374_);
lean_ctor_set(v_reuseFailAlloc_4389_, 1, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4378_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4377_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4381_ = l_Lean_indentD(v___x_4380_);
v___x_4382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4379_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
v___x_4383_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4382_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
v___x_4385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
lean_ctor_set(v___x_4385_, 1, v___x_4375_);
v___x_4386_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4387_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4388_;
}
}
else
{
lean_object* v_val_4390_; lean_object* v___x_4392_; 
lean_del_object(v___x_4372_);
lean_dec(v___x_4359_);
lean_dec(v_stx_2364_);
v_val_4390_ = lean_ctor_get(v_fst_4370_, 0);
lean_inc(v_val_4390_);
lean_dec_ref_known(v_fst_4370_, 1);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 0, v_val_4390_);
v___x_4392_ = v___x_4368_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_val_4390_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
lean_dec(v___x_4359_);
lean_dec(v_stx_2364_);
v_a_4397_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4365_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4365_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
else
{
lean_object* v___x_4405_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4405_ = lean_unsigned_to_nat(1u);
v___x_4511_ = l_Lean_Syntax_getArg(v___x_4356_, v___x_4405_);
lean_dec(v___x_4356_);
v___x_4512_ = l_Lean_Syntax_isNone(v___x_4511_);
if (v___x_4512_ == 0)
{
uint8_t v___x_4513_; 
v___x_4513_ = l_Lean_Syntax_matchesNull(v___x_4511_, v___x_4405_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v_env_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4514_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4515_ = lean_st_ref_get(v_a_2370_);
v_env_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc_ref(v_env_4516_);
lean_dec(v___x_4515_);
v___x_4517_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4518_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4517_, v_env_4516_, v___x_4514_);
v___x_4519_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4520_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4518_, v___x_4519_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4518_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4551_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4523_ = v___x_4520_;
v_isShared_4524_ = v_isSharedCheck_4551_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4520_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4551_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_fst_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4549_; 
v_fst_4525_ = lean_ctor_get(v_a_4521_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v_a_4521_);
if (v_isSharedCheck_4549_ == 0)
{
lean_object* v_unused_4550_; 
v_unused_4550_ = lean_ctor_get(v_a_4521_, 1);
lean_dec(v_unused_4550_);
v___x_4527_ = v_a_4521_;
v_isShared_4528_ = v_isSharedCheck_4549_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_fst_4525_);
lean_dec(v_a_4521_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4549_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
if (lean_obj_tag(v_fst_4525_) == 0)
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4532_; 
lean_del_object(v___x_4523_);
v___x_4529_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4530_ = l_Lean_MessageData_ofName(v___x_4514_);
lean_inc_ref(v___x_4530_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set_tag(v___x_4527_, 7);
lean_ctor_set(v___x_4527_, 1, v___x_4530_);
lean_ctor_set(v___x_4527_, 0, v___x_4529_);
v___x_4532_ = v___x_4527_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4529_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v___x_4530_);
v___x_4532_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4533_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4532_);
lean_ctor_set(v___x_4534_, 1, v___x_4533_);
v___x_4535_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4536_ = l_Lean_indentD(v___x_4535_);
v___x_4537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4534_);
lean_ctor_set(v___x_4537_, 1, v___x_4536_);
v___x_4538_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4537_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
v___x_4540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
lean_ctor_set(v___x_4540_, 1, v___x_4530_);
v___x_4541_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4540_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
v___x_4543_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4542_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4543_;
}
}
else
{
lean_object* v_val_4545_; lean_object* v___x_4547_; 
lean_del_object(v___x_4527_);
lean_dec(v___x_4514_);
lean_dec(v_stx_2364_);
v_val_4545_ = lean_ctor_get(v_fst_4525_, 0);
lean_inc(v_val_4545_);
lean_dec_ref_known(v_fst_4525_, 1);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v_val_4545_);
v___x_4547_ = v___x_4523_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_val_4545_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v___x_4514_);
lean_dec(v_stx_2364_);
v_a_4552_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4520_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4520_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
else
{
v___y_4407_ = v_a_2365_;
v___y_4408_ = v_a_2366_;
v___y_4409_ = v_a_2367_;
v___y_4410_ = v_a_2368_;
v___y_4411_ = v_a_2369_;
v___y_4412_ = v_a_2370_;
goto v___jp_4406_;
}
}
else
{
lean_dec(v___x_4511_);
v___y_4407_ = v_a_2365_;
v___y_4408_ = v_a_2366_;
v___y_4409_ = v_a_2367_;
v___y_4410_ = v_a_2368_;
v___y_4411_ = v_a_2369_;
v___y_4412_ = v_a_2370_;
goto v___jp_4406_;
}
v___jp_4406_:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; uint8_t v___x_4415_; 
v___x_4413_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4405_);
v___x_4414_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90));
lean_inc(v___x_4413_);
v___x_4415_ = l_Lean_Syntax_isOfKind(v___x_4413_, v___x_4414_);
if (v___x_4415_ == 0)
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v_env_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
lean_dec(v___x_4413_);
lean_inc_n(v_stx_2364_, 2);
v___x_4416_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4417_ = lean_st_ref_get(v___y_4412_);
v_env_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc_ref(v_env_4418_);
lean_dec(v___x_4417_);
v___x_4419_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4420_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4419_, v_env_4418_, v___x_4416_);
v___x_4421_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4422_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4420_, v___x_4421_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___x_4420_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4453_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4453_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4453_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v_fst_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4451_; 
v_fst_4427_ = lean_ctor_get(v_a_4423_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v_a_4423_);
if (v_isSharedCheck_4451_ == 0)
{
lean_object* v_unused_4452_; 
v_unused_4452_ = lean_ctor_get(v_a_4423_, 1);
lean_dec(v_unused_4452_);
v___x_4429_ = v_a_4423_;
v_isShared_4430_ = v_isSharedCheck_4451_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_fst_4427_);
lean_dec(v_a_4423_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4451_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
if (lean_obj_tag(v_fst_4427_) == 0)
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4434_; 
lean_del_object(v___x_4425_);
v___x_4431_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4432_ = l_Lean_MessageData_ofName(v___x_4416_);
lean_inc_ref(v___x_4432_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set_tag(v___x_4429_, 7);
lean_ctor_set(v___x_4429_, 1, v___x_4432_);
lean_ctor_set(v___x_4429_, 0, v___x_4431_);
v___x_4434_ = v___x_4429_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4435_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4434_);
lean_ctor_set(v___x_4436_, 1, v___x_4435_);
v___x_4437_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4438_ = l_Lean_indentD(v___x_4437_);
v___x_4439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4436_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
v___x_4440_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4439_);
lean_ctor_set(v___x_4441_, 1, v___x_4440_);
v___x_4442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
lean_ctor_set(v___x_4442_, 1, v___x_4432_);
v___x_4443_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4442_);
lean_ctor_set(v___x_4444_, 1, v___x_4443_);
v___x_4445_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4444_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
return v___x_4445_;
}
}
else
{
lean_object* v_val_4447_; lean_object* v___x_4449_; 
lean_del_object(v___x_4429_);
lean_dec(v___x_4416_);
lean_dec(v_stx_2364_);
v_val_4447_ = lean_ctor_get(v_fst_4427_, 0);
lean_inc(v_val_4447_);
lean_dec_ref_known(v_fst_4427_, 1);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v_val_4447_);
v___x_4449_ = v___x_4425_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_val_4447_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_dec(v___x_4416_);
lean_dec(v_stx_2364_);
v_a_4454_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4422_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4422_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
else
{
lean_object* v___x_4462_; uint8_t v___x_4463_; 
v___x_4462_ = l_Lean_Syntax_getArg(v___x_4413_, v___x_4405_);
lean_dec(v___x_4413_);
v___x_4463_ = l_Lean_Syntax_isNone(v___x_4462_);
if (v___x_4463_ == 0)
{
uint8_t v___x_4464_; 
v___x_4464_ = l_Lean_Syntax_matchesNull(v___x_4462_, v___x_4405_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v_env_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4465_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4466_ = lean_st_ref_get(v___y_4412_);
v_env_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc_ref(v_env_4467_);
lean_dec(v___x_4466_);
v___x_4468_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4469_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4468_, v_env_4467_, v___x_4465_);
v___x_4470_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4471_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4469_, v___x_4470_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___x_4469_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4502_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4474_ = v___x_4471_;
v_isShared_4475_ = v_isSharedCheck_4502_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4471_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4502_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v_fst_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4500_; 
v_fst_4476_ = lean_ctor_get(v_a_4472_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_a_4472_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; 
v_unused_4501_ = lean_ctor_get(v_a_4472_, 1);
lean_dec(v_unused_4501_);
v___x_4478_ = v_a_4472_;
v_isShared_4479_ = v_isSharedCheck_4500_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_fst_4476_);
lean_dec(v_a_4472_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4500_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
if (lean_obj_tag(v_fst_4476_) == 0)
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4483_; 
lean_del_object(v___x_4474_);
v___x_4480_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4481_ = l_Lean_MessageData_ofName(v___x_4465_);
lean_inc_ref(v___x_4481_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set_tag(v___x_4478_, 7);
lean_ctor_set(v___x_4478_, 1, v___x_4481_);
lean_ctor_set(v___x_4478_, 0, v___x_4480_);
v___x_4483_ = v___x_4478_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4480_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4484_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4483_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
v___x_4486_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4487_ = l_Lean_indentD(v___x_4486_);
v___x_4488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4485_);
lean_ctor_set(v___x_4488_, 1, v___x_4487_);
v___x_4489_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4488_);
lean_ctor_set(v___x_4490_, 1, v___x_4489_);
v___x_4491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
lean_ctor_set(v___x_4491_, 1, v___x_4481_);
v___x_4492_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4491_);
lean_ctor_set(v___x_4493_, 1, v___x_4492_);
v___x_4494_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4493_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
return v___x_4494_;
}
}
else
{
lean_object* v_val_4496_; lean_object* v___x_4498_; 
lean_del_object(v___x_4478_);
lean_dec(v___x_4465_);
lean_dec(v_stx_2364_);
v_val_4496_ = lean_ctor_get(v_fst_4476_, 0);
lean_inc(v_val_4496_);
lean_dec_ref_known(v_fst_4476_, 1);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 0, v_val_4496_);
v___x_4498_ = v___x_4474_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_val_4496_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
}
else
{
lean_object* v_a_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4510_; 
lean_dec(v___x_4465_);
lean_dec(v_stx_2364_);
v_a_4503_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4505_ = v___x_4471_;
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_a_4503_);
lean_dec(v___x_4471_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
if (v_isShared_4506_ == 0)
{
v___x_4508_ = v___x_4505_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
else
{
lean_dec(v_stx_2364_);
goto v___jp_2390_;
}
}
else
{
lean_dec(v___x_4462_);
lean_dec(v_stx_2364_);
goto v___jp_2390_;
}
}
}
}
}
}
else
{
lean_object* v___x_4560_; lean_object* v___x_4561_; uint8_t v___x_4562_; 
v___x_4560_ = lean_unsigned_to_nat(1u);
v___x_4561_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4560_);
v___x_4562_ = l_Lean_Syntax_isNone(v___x_4561_);
if (v___x_4562_ == 0)
{
uint8_t v___x_4563_; 
v___x_4563_ = l_Lean_Syntax_matchesNull(v___x_4561_, v___x_4560_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v_env_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4564_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4565_ = lean_st_ref_get(v_a_2370_);
v_env_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc_ref(v_env_4566_);
lean_dec(v___x_4565_);
v___x_4567_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4568_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4567_, v_env_4566_, v___x_4564_);
v___x_4569_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4570_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4568_, v___x_4569_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4568_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4601_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4573_ = v___x_4570_;
v_isShared_4574_ = v_isSharedCheck_4601_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4570_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4601_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v_fst_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4599_; 
v_fst_4575_ = lean_ctor_get(v_a_4571_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_a_4571_);
if (v_isSharedCheck_4599_ == 0)
{
lean_object* v_unused_4600_; 
v_unused_4600_ = lean_ctor_get(v_a_4571_, 1);
lean_dec(v_unused_4600_);
v___x_4577_ = v_a_4571_;
v_isShared_4578_ = v_isSharedCheck_4599_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_fst_4575_);
lean_dec(v_a_4571_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4599_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
if (lean_obj_tag(v_fst_4575_) == 0)
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4582_; 
lean_del_object(v___x_4573_);
v___x_4579_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4580_ = l_Lean_MessageData_ofName(v___x_4564_);
lean_inc_ref(v___x_4580_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set_tag(v___x_4577_, 7);
lean_ctor_set(v___x_4577_, 1, v___x_4580_);
lean_ctor_set(v___x_4577_, 0, v___x_4579_);
v___x_4582_ = v___x_4577_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v___x_4580_);
v___x_4582_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4583_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4582_);
lean_ctor_set(v___x_4584_, 1, v___x_4583_);
v___x_4585_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4586_ = l_Lean_indentD(v___x_4585_);
v___x_4587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4584_);
lean_ctor_set(v___x_4587_, 1, v___x_4586_);
v___x_4588_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4587_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
lean_ctor_set(v___x_4590_, 1, v___x_4580_);
v___x_4591_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4590_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
v___x_4593_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4592_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4593_;
}
}
else
{
lean_object* v_val_4595_; lean_object* v___x_4597_; 
lean_del_object(v___x_4577_);
lean_dec(v___x_4564_);
lean_dec(v_stx_2364_);
v_val_4595_ = lean_ctor_get(v_fst_4575_, 0);
lean_inc(v_val_4595_);
lean_dec_ref_known(v_fst_4575_, 1);
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 0, v_val_4595_);
v___x_4597_ = v___x_4573_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_val_4595_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
}
else
{
lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4609_; 
lean_dec(v___x_4564_);
lean_dec(v_stx_2364_);
v_a_4602_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4604_ = v___x_4570_;
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v___x_4570_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4607_; 
if (v_isShared_4605_ == 0)
{
v___x_4607_ = v___x_4604_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
else
{
v___y_2622_ = v_a_2365_;
v___y_2623_ = v_a_2366_;
v___y_2624_ = v_a_2367_;
v___y_2625_ = v_a_2368_;
v___y_2626_ = v_a_2369_;
v___y_2627_ = v_a_2370_;
goto v___jp_2621_;
}
}
else
{
lean_dec(v___x_4561_);
v___y_2622_ = v_a_2365_;
v___y_2623_ = v_a_2366_;
v___y_2624_ = v_a_2367_;
v___y_2625_ = v_a_2368_;
v___y_2626_ = v_a_2369_;
v___y_2627_ = v_a_2370_;
goto v___jp_2621_;
}
}
}
else
{
lean_object* v___x_4610_; lean_object* v___x_4611_; uint8_t v___x_4612_; 
v___x_4610_ = lean_unsigned_to_nat(1u);
v___x_4611_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4610_);
v___x_4612_ = l_Lean_Syntax_isNone(v___x_4611_);
if (v___x_4612_ == 0)
{
uint8_t v___x_4613_; 
v___x_4613_ = l_Lean_Syntax_matchesNull(v___x_4611_, v___x_4610_);
if (v___x_4613_ == 0)
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v_env_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4614_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4615_ = lean_st_ref_get(v_a_2370_);
v_env_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc_ref(v_env_4616_);
lean_dec(v___x_4615_);
v___x_4617_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4618_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4617_, v_env_4616_, v___x_4614_);
v___x_4619_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4620_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4618_, v___x_4619_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4618_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4651_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4623_ = v___x_4620_;
v_isShared_4624_ = v_isSharedCheck_4651_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4620_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4651_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v_fst_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4649_; 
v_fst_4625_ = lean_ctor_get(v_a_4621_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v_a_4621_);
if (v_isSharedCheck_4649_ == 0)
{
lean_object* v_unused_4650_; 
v_unused_4650_ = lean_ctor_get(v_a_4621_, 1);
lean_dec(v_unused_4650_);
v___x_4627_ = v_a_4621_;
v_isShared_4628_ = v_isSharedCheck_4649_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_fst_4625_);
lean_dec(v_a_4621_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4649_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
if (lean_obj_tag(v_fst_4625_) == 0)
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4632_; 
lean_del_object(v___x_4623_);
v___x_4629_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4630_ = l_Lean_MessageData_ofName(v___x_4614_);
lean_inc_ref(v___x_4630_);
if (v_isShared_4628_ == 0)
{
lean_ctor_set_tag(v___x_4627_, 7);
lean_ctor_set(v___x_4627_, 1, v___x_4630_);
lean_ctor_set(v___x_4627_, 0, v___x_4629_);
v___x_4632_ = v___x_4627_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v___x_4630_);
v___x_4632_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4633_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4632_);
lean_ctor_set(v___x_4634_, 1, v___x_4633_);
v___x_4635_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4636_ = l_Lean_indentD(v___x_4635_);
v___x_4637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4634_);
lean_ctor_set(v___x_4637_, 1, v___x_4636_);
v___x_4638_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4637_);
lean_ctor_set(v___x_4639_, 1, v___x_4638_);
v___x_4640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
lean_ctor_set(v___x_4640_, 1, v___x_4630_);
v___x_4641_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4640_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
v___x_4643_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4642_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4643_;
}
}
else
{
lean_object* v_val_4645_; lean_object* v___x_4647_; 
lean_del_object(v___x_4627_);
lean_dec(v___x_4614_);
lean_dec(v_stx_2364_);
v_val_4645_ = lean_ctor_get(v_fst_4625_, 0);
lean_inc(v_val_4645_);
lean_dec_ref_known(v_fst_4625_, 1);
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 0, v_val_4645_);
v___x_4647_ = v___x_4623_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_val_4645_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
lean_dec(v___x_4614_);
lean_dec(v_stx_2364_);
v_a_4652_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4620_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4620_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
else
{
v___y_2421_ = v_a_2365_;
v___y_2422_ = v_a_2366_;
v___y_2423_ = v_a_2367_;
v___y_2424_ = v_a_2368_;
v___y_2425_ = v_a_2369_;
v___y_2426_ = v_a_2370_;
goto v___jp_2420_;
}
}
else
{
lean_dec(v___x_4611_);
v___y_2421_ = v_a_2365_;
v___y_2422_ = v_a_2366_;
v___y_2423_ = v_a_2367_;
v___y_2424_ = v_a_2368_;
v___y_2425_ = v_a_2369_;
v___y_2426_ = v_a_2370_;
goto v___jp_2420_;
}
}
v___jp_2621_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___x_2628_ = lean_unsigned_to_nat(2u);
v___x_2629_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2628_);
v___x_2630_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2631_ = l_Lean_Syntax_isOfKind(v___x_2629_, v___x_2630_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v_env_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_inc_n(v_stx_2364_, 2);
v___x_2632_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_2633_ = lean_st_ref_get(v___y_2627_);
v_env_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc_ref(v_env_2634_);
lean_dec(v___x_2633_);
v___x_2635_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2636_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2635_, v_env_2634_, v___x_2632_);
v___x_2637_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2638_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_2636_, v___x_2637_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___x_2636_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2669_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2669_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2669_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_fst_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2667_; 
v_fst_2643_ = lean_ctor_get(v_a_2639_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_a_2639_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v_a_2639_, 1);
lean_dec(v_unused_2668_);
v___x_2645_ = v_a_2639_;
v_isShared_2646_ = v_isSharedCheck_2667_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_fst_2643_);
lean_dec(v_a_2639_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2667_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
if (lean_obj_tag(v_fst_2643_) == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
lean_del_object(v___x_2641_);
v___x_2647_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2648_ = l_Lean_MessageData_ofName(v___x_2632_);
lean_inc_ref(v___x_2648_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 7);
lean_ctor_set(v___x_2645_, 1, v___x_2648_);
lean_ctor_set(v___x_2645_, 0, v___x_2647_);
v___x_2650_ = v___x_2645_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2651_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2650_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_2654_ = l_Lean_indentD(v___x_2653_);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2652_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v___x_2648_);
v___x_2659_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2660_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2661_;
}
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2665_; 
lean_del_object(v___x_2645_);
lean_dec(v___x_2632_);
lean_dec(v_stx_2364_);
v_val_2663_ = lean_ctor_get(v_fst_2643_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v_fst_2643_, 1);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v_val_2663_);
v___x_2665_ = v___x_2641_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_val_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v___x_2632_);
lean_dec(v_stx_2364_);
v_a_2670_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2638_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2638_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = lean_unsigned_to_nat(3u);
v___x_2679_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2678_);
lean_dec(v_stx_2364_);
v___x_2680_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2620_, v___x_2679_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2680_;
}
}
}
else
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; 
v___x_4660_ = lean_unsigned_to_nat(0u);
v___x_4661_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4660_);
v___x_4662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4663_ = l_Lean_Syntax_isOfKind(v___x_4661_, v___x_4662_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v_env_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4664_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4665_ = lean_st_ref_get(v_a_2370_);
v_env_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc_ref(v_env_4666_);
lean_dec(v___x_4665_);
v___x_4667_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4668_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4667_, v_env_4666_, v___x_4664_);
v___x_4669_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4670_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4668_, v___x_4669_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4668_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4701_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4701_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4701_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v_fst_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4699_; 
v_fst_4675_ = lean_ctor_get(v_a_4671_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_a_4671_);
if (v_isSharedCheck_4699_ == 0)
{
lean_object* v_unused_4700_; 
v_unused_4700_ = lean_ctor_get(v_a_4671_, 1);
lean_dec(v_unused_4700_);
v___x_4677_ = v_a_4671_;
v_isShared_4678_ = v_isSharedCheck_4699_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_fst_4675_);
lean_dec(v_a_4671_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4699_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
if (lean_obj_tag(v_fst_4675_) == 0)
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4682_; 
lean_del_object(v___x_4673_);
v___x_4679_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4680_ = l_Lean_MessageData_ofName(v___x_4664_);
lean_inc_ref(v___x_4680_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set_tag(v___x_4677_, 7);
lean_ctor_set(v___x_4677_, 1, v___x_4680_);
lean_ctor_set(v___x_4677_, 0, v___x_4679_);
v___x_4682_ = v___x_4677_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4679_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v___x_4680_);
v___x_4682_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4683_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4682_);
lean_ctor_set(v___x_4684_, 1, v___x_4683_);
v___x_4685_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4686_ = l_Lean_indentD(v___x_4685_);
v___x_4687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4684_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4687_);
lean_ctor_set(v___x_4689_, 1, v___x_4688_);
v___x_4690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
lean_ctor_set(v___x_4690_, 1, v___x_4680_);
v___x_4691_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4690_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
v___x_4693_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4692_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4693_;
}
}
else
{
lean_object* v_val_4695_; lean_object* v___x_4697_; 
lean_del_object(v___x_4677_);
lean_dec(v___x_4664_);
lean_dec(v_stx_2364_);
v_val_4695_ = lean_ctor_get(v_fst_4675_, 0);
lean_inc(v_val_4695_);
lean_dec_ref_known(v_fst_4675_, 1);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v_val_4695_);
v___x_4697_ = v___x_4673_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_val_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_dec(v___x_4664_);
lean_dec(v_stx_2364_);
v_a_4702_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4670_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4670_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4710_ = lean_unsigned_to_nat(1u);
v___x_4711_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4710_);
v___x_4712_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92));
lean_inc(v___x_4711_);
v___x_4713_ = l_Lean_Syntax_isOfKind(v___x_4711_, v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v_env_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
lean_dec(v___x_4711_);
lean_inc_n(v_stx_2364_, 2);
v___x_4714_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4715_ = lean_st_ref_get(v_a_2370_);
v_env_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc_ref(v_env_4716_);
lean_dec(v___x_4715_);
v___x_4717_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4718_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4717_, v_env_4716_, v___x_4714_);
v___x_4719_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4720_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4718_, v___x_4719_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4718_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4751_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4723_ = v___x_4720_;
v_isShared_4724_ = v_isSharedCheck_4751_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4720_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4751_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v_fst_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4749_; 
v_fst_4725_ = lean_ctor_get(v_a_4721_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v_a_4721_);
if (v_isSharedCheck_4749_ == 0)
{
lean_object* v_unused_4750_; 
v_unused_4750_ = lean_ctor_get(v_a_4721_, 1);
lean_dec(v_unused_4750_);
v___x_4727_ = v_a_4721_;
v_isShared_4728_ = v_isSharedCheck_4749_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_fst_4725_);
lean_dec(v_a_4721_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4749_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
if (lean_obj_tag(v_fst_4725_) == 0)
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4732_; 
lean_del_object(v___x_4723_);
v___x_4729_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4730_ = l_Lean_MessageData_ofName(v___x_4714_);
lean_inc_ref(v___x_4730_);
if (v_isShared_4728_ == 0)
{
lean_ctor_set_tag(v___x_4727_, 7);
lean_ctor_set(v___x_4727_, 1, v___x_4730_);
lean_ctor_set(v___x_4727_, 0, v___x_4729_);
v___x_4732_ = v___x_4727_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4729_);
lean_ctor_set(v_reuseFailAlloc_4744_, 1, v___x_4730_);
v___x_4732_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4733_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4732_);
lean_ctor_set(v___x_4734_, 1, v___x_4733_);
v___x_4735_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4736_ = l_Lean_indentD(v___x_4735_);
v___x_4737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4734_);
lean_ctor_set(v___x_4737_, 1, v___x_4736_);
v___x_4738_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4737_);
lean_ctor_set(v___x_4739_, 1, v___x_4738_);
v___x_4740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
lean_ctor_set(v___x_4740_, 1, v___x_4730_);
v___x_4741_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4740_);
lean_ctor_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4742_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4743_;
}
}
else
{
lean_object* v_val_4745_; lean_object* v___x_4747_; 
lean_del_object(v___x_4727_);
lean_dec(v___x_4714_);
lean_dec(v_stx_2364_);
v_val_4745_ = lean_ctor_get(v_fst_4725_, 0);
lean_inc(v_val_4745_);
lean_dec_ref_known(v_fst_4725_, 1);
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v_val_4745_);
v___x_4747_ = v___x_4723_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_val_4745_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_dec(v___x_4714_);
lean_dec(v_stx_2364_);
v_a_4752_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4720_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4720_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
else
{
lean_object* v___x_4760_; uint8_t v___x_4761_; 
v___x_4760_ = l_Lean_Syntax_getArg(v___x_4711_, v___x_4660_);
lean_dec(v___x_4711_);
lean_inc(v___x_4760_);
v___x_4761_ = l_Lean_Syntax_matchesNull(v___x_4760_, v___x_4710_);
if (v___x_4761_ == 0)
{
lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v_env_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
lean_dec(v___x_4760_);
lean_inc_n(v_stx_2364_, 2);
v___x_4762_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4763_ = lean_st_ref_get(v_a_2370_);
v_env_4764_ = lean_ctor_get(v___x_4763_, 0);
lean_inc_ref(v_env_4764_);
lean_dec(v___x_4763_);
v___x_4765_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4766_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4765_, v_env_4764_, v___x_4762_);
v___x_4767_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4768_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4766_, v___x_4767_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4766_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4799_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4771_ = v___x_4768_;
v_isShared_4772_ = v_isSharedCheck_4799_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4768_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4799_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v_fst_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4797_; 
v_fst_4773_ = lean_ctor_get(v_a_4769_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v_a_4769_);
if (v_isSharedCheck_4797_ == 0)
{
lean_object* v_unused_4798_; 
v_unused_4798_ = lean_ctor_get(v_a_4769_, 1);
lean_dec(v_unused_4798_);
v___x_4775_ = v_a_4769_;
v_isShared_4776_ = v_isSharedCheck_4797_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_fst_4773_);
lean_dec(v_a_4769_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4797_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
if (lean_obj_tag(v_fst_4773_) == 0)
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4780_; 
lean_del_object(v___x_4771_);
v___x_4777_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4778_ = l_Lean_MessageData_ofName(v___x_4762_);
lean_inc_ref(v___x_4778_);
if (v_isShared_4776_ == 0)
{
lean_ctor_set_tag(v___x_4775_, 7);
lean_ctor_set(v___x_4775_, 1, v___x_4778_);
lean_ctor_set(v___x_4775_, 0, v___x_4777_);
v___x_4780_ = v___x_4775_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4777_);
lean_ctor_set(v_reuseFailAlloc_4792_, 1, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4781_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4780_);
lean_ctor_set(v___x_4782_, 1, v___x_4781_);
v___x_4783_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4784_ = l_Lean_indentD(v___x_4783_);
v___x_4785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4782_);
lean_ctor_set(v___x_4785_, 1, v___x_4784_);
v___x_4786_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4785_);
lean_ctor_set(v___x_4787_, 1, v___x_4786_);
v___x_4788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4787_);
lean_ctor_set(v___x_4788_, 1, v___x_4778_);
v___x_4789_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4788_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
v___x_4791_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4790_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4791_;
}
}
else
{
lean_object* v_val_4793_; lean_object* v___x_4795_; 
lean_del_object(v___x_4775_);
lean_dec(v___x_4762_);
lean_dec(v_stx_2364_);
v_val_4793_ = lean_ctor_get(v_fst_4773_, 0);
lean_inc(v_val_4793_);
lean_dec_ref_known(v_fst_4773_, 1);
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 0, v_val_4793_);
v___x_4795_ = v___x_4771_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_val_4793_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
}
else
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
lean_dec(v___x_4762_);
lean_dec(v_stx_2364_);
v_a_4800_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4768_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4768_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
else
{
lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v___x_4808_ = l_Lean_Syntax_getArg(v___x_4760_, v___x_4660_);
lean_dec(v___x_4760_);
v___x_4809_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94));
v___x_4810_ = l_Lean_Syntax_isOfKind(v___x_4808_, v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v_env_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4811_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4812_ = lean_st_ref_get(v_a_2370_);
v_env_4813_ = lean_ctor_get(v___x_4812_, 0);
lean_inc_ref(v_env_4813_);
lean_dec(v___x_4812_);
v___x_4814_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4815_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4814_, v_env_4813_, v___x_4811_);
v___x_4816_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4817_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4815_, v___x_4816_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4815_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4848_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4848_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4848_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v_fst_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4846_; 
v_fst_4822_ = lean_ctor_get(v_a_4818_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v_a_4818_);
if (v_isSharedCheck_4846_ == 0)
{
lean_object* v_unused_4847_; 
v_unused_4847_ = lean_ctor_get(v_a_4818_, 1);
lean_dec(v_unused_4847_);
v___x_4824_ = v_a_4818_;
v_isShared_4825_ = v_isSharedCheck_4846_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_fst_4822_);
lean_dec(v_a_4818_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4846_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
if (lean_obj_tag(v_fst_4822_) == 0)
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4829_; 
lean_del_object(v___x_4820_);
v___x_4826_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4827_ = l_Lean_MessageData_ofName(v___x_4811_);
lean_inc_ref(v___x_4827_);
if (v_isShared_4825_ == 0)
{
lean_ctor_set_tag(v___x_4824_, 7);
lean_ctor_set(v___x_4824_, 1, v___x_4827_);
lean_ctor_set(v___x_4824_, 0, v___x_4826_);
v___x_4829_ = v___x_4824_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4826_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v___x_4827_);
v___x_4829_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4830_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4829_);
lean_ctor_set(v___x_4831_, 1, v___x_4830_);
v___x_4832_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4833_ = l_Lean_indentD(v___x_4832_);
v___x_4834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4831_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
v___x_4835_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4834_);
lean_ctor_set(v___x_4836_, 1, v___x_4835_);
v___x_4837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
lean_ctor_set(v___x_4837_, 1, v___x_4827_);
v___x_4838_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4839_, 0, v___x_4837_);
lean_ctor_set(v___x_4839_, 1, v___x_4838_);
v___x_4840_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4839_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4840_;
}
}
else
{
lean_object* v_val_4842_; lean_object* v___x_4844_; 
lean_del_object(v___x_4824_);
lean_dec(v___x_4811_);
lean_dec(v_stx_2364_);
v_val_4842_ = lean_ctor_get(v_fst_4822_, 0);
lean_inc(v_val_4842_);
lean_dec_ref_known(v_fst_4822_, 1);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v_val_4842_);
v___x_4844_ = v___x_4820_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_val_4842_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
lean_dec(v___x_4811_);
lean_dec(v_stx_2364_);
v_a_4849_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4817_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4817_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4854_; 
if (v_isShared_4852_ == 0)
{
v___x_4854_ = v___x_4851_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
else
{
lean_object* v___x_4857_; lean_object* v___x_4858_; 
lean_dec(v_stx_2364_);
v___x_4857_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4857_);
return v___x_4858_;
}
}
}
}
}
}
else
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; uint8_t v___x_4862_; 
v___x_4859_ = lean_unsigned_to_nat(1u);
v___x_4860_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4859_);
v___x_4861_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4862_ = l_Lean_Syntax_isOfKind(v___x_4860_, v___x_4861_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v_env_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4863_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4864_ = lean_st_ref_get(v_a_2370_);
v_env_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc_ref(v_env_4865_);
lean_dec(v___x_4864_);
v___x_4866_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4867_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4866_, v_env_4865_, v___x_4863_);
v___x_4868_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4869_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4867_, v___x_4868_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4867_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4900_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4872_ = v___x_4869_;
v_isShared_4873_ = v_isSharedCheck_4900_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4869_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4900_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v_fst_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4898_; 
v_fst_4874_ = lean_ctor_get(v_a_4870_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v_a_4870_);
if (v_isSharedCheck_4898_ == 0)
{
lean_object* v_unused_4899_; 
v_unused_4899_ = lean_ctor_get(v_a_4870_, 1);
lean_dec(v_unused_4899_);
v___x_4876_ = v_a_4870_;
v_isShared_4877_ = v_isSharedCheck_4898_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_fst_4874_);
lean_dec(v_a_4870_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4898_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
if (lean_obj_tag(v_fst_4874_) == 0)
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4881_; 
lean_del_object(v___x_4872_);
v___x_4878_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4879_ = l_Lean_MessageData_ofName(v___x_4863_);
lean_inc_ref(v___x_4879_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set_tag(v___x_4876_, 7);
lean_ctor_set(v___x_4876_, 1, v___x_4879_);
lean_ctor_set(v___x_4876_, 0, v___x_4878_);
v___x_4881_ = v___x_4876_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4878_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4882_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4881_);
lean_ctor_set(v___x_4883_, 1, v___x_4882_);
v___x_4884_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4885_ = l_Lean_indentD(v___x_4884_);
v___x_4886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4883_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
v___x_4887_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4886_);
lean_ctor_set(v___x_4888_, 1, v___x_4887_);
v___x_4889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4888_);
lean_ctor_set(v___x_4889_, 1, v___x_4879_);
v___x_4890_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4889_);
lean_ctor_set(v___x_4891_, 1, v___x_4890_);
v___x_4892_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4891_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4892_;
}
}
else
{
lean_object* v_val_4894_; lean_object* v___x_4896_; 
lean_del_object(v___x_4876_);
lean_dec(v___x_4863_);
lean_dec(v_stx_2364_);
v_val_4894_ = lean_ctor_get(v_fst_4874_, 0);
lean_inc(v_val_4894_);
lean_dec_ref_known(v_fst_4874_, 1);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 0, v_val_4894_);
v___x_4896_ = v___x_4872_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_val_4894_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
else
{
lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4908_; 
lean_dec(v___x_4863_);
lean_dec(v_stx_2364_);
v_a_4901_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4903_ = v___x_4869_;
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___x_4869_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4906_; 
if (v_isShared_4904_ == 0)
{
v___x_4906_ = v___x_4903_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
}
else
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; uint8_t v___x_4912_; 
v___x_4909_ = lean_unsigned_to_nat(2u);
v___x_4910_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4909_);
v___x_4911_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4912_ = l_Lean_Syntax_isOfKind(v___x_4910_, v___x_4911_);
if (v___x_4912_ == 0)
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v_env_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
lean_inc_n(v_stx_2364_, 2);
v___x_4913_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4914_ = lean_st_ref_get(v_a_2370_);
v_env_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc_ref(v_env_4915_);
lean_dec(v___x_4914_);
v___x_4916_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4917_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4916_, v_env_4915_, v___x_4913_);
v___x_4918_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4919_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4917_, v___x_4918_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4917_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4950_; 
v_a_4920_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4922_ = v___x_4919_;
v_isShared_4923_ = v_isSharedCheck_4950_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4919_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4950_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v_fst_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4948_; 
v_fst_4924_ = lean_ctor_get(v_a_4920_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v_a_4920_);
if (v_isSharedCheck_4948_ == 0)
{
lean_object* v_unused_4949_; 
v_unused_4949_ = lean_ctor_get(v_a_4920_, 1);
lean_dec(v_unused_4949_);
v___x_4926_ = v_a_4920_;
v_isShared_4927_ = v_isSharedCheck_4948_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_fst_4924_);
lean_dec(v_a_4920_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4948_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
if (lean_obj_tag(v_fst_4924_) == 0)
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4931_; 
lean_del_object(v___x_4922_);
v___x_4928_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4929_ = l_Lean_MessageData_ofName(v___x_4913_);
lean_inc_ref(v___x_4929_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set_tag(v___x_4926_, 7);
lean_ctor_set(v___x_4926_, 1, v___x_4929_);
lean_ctor_set(v___x_4926_, 0, v___x_4928_);
v___x_4931_ = v___x_4926_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4928_);
lean_ctor_set(v_reuseFailAlloc_4943_, 1, v___x_4929_);
v___x_4931_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4932_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4931_);
lean_ctor_set(v___x_4933_, 1, v___x_4932_);
v___x_4934_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4935_ = l_Lean_indentD(v___x_4934_);
v___x_4936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4933_);
lean_ctor_set(v___x_4936_, 1, v___x_4935_);
v___x_4937_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4936_);
lean_ctor_set(v___x_4938_, 1, v___x_4937_);
v___x_4939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4938_);
lean_ctor_set(v___x_4939_, 1, v___x_4929_);
v___x_4940_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4939_);
lean_ctor_set(v___x_4941_, 1, v___x_4940_);
v___x_4942_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4941_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4942_;
}
}
else
{
lean_object* v_val_4944_; lean_object* v___x_4946_; 
lean_del_object(v___x_4926_);
lean_dec(v___x_4913_);
lean_dec(v_stx_2364_);
v_val_4944_ = lean_ctor_get(v_fst_4924_, 0);
lean_inc(v_val_4944_);
lean_dec_ref_known(v_fst_4924_, 1);
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 0, v_val_4944_);
v___x_4946_ = v___x_4922_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_val_4944_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
}
else
{
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4958_; 
lean_dec(v___x_4913_);
lean_dec(v_stx_2364_);
v_a_4951_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4953_ = v___x_4919_;
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4919_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v___x_4956_; 
if (v_isShared_4954_ == 0)
{
v___x_4956_ = v___x_4953_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4957_; 
v_reuseFailAlloc_4957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4957_, 0, v_a_4951_);
v___x_4956_ = v_reuseFailAlloc_4957_;
goto v_reusejp_4955_;
}
v_reusejp_4955_:
{
return v___x_4956_;
}
}
}
}
else
{
lean_object* v___x_4959_; lean_object* v___x_4960_; 
lean_dec(v_stx_2364_);
v___x_4959_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4959_);
return v___x_4960_;
}
}
}
}
else
{
lean_object* v___x_4961_; lean_object* v___x_4962_; uint8_t v___x_4963_; 
v___x_4961_ = lean_unsigned_to_nat(1u);
v___x_4962_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_4961_);
v___x_4963_ = l_Lean_Syntax_isNone(v___x_4962_);
if (v___x_4963_ == 0)
{
uint8_t v___x_4964_; 
v___x_4964_ = l_Lean_Syntax_matchesNull(v___x_4962_, v___x_4961_);
if (v___x_4964_ == 0)
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v_env_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
lean_del_object(v___x_2404_);
lean_inc_n(v_stx_2364_, 2);
v___x_4965_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_4966_ = lean_st_ref_get(v_a_2370_);
v_env_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc_ref(v_env_4967_);
lean_dec(v___x_4966_);
v___x_4968_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4969_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4968_, v_env_4967_, v___x_4965_);
v___x_4970_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4971_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_4969_, v___x_4970_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_4969_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_5002_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4974_ = v___x_4971_;
v_isShared_4975_ = v_isSharedCheck_5002_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4971_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_5002_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v_fst_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_5000_; 
v_fst_4976_ = lean_ctor_get(v_a_4972_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v_a_4972_);
if (v_isSharedCheck_5000_ == 0)
{
lean_object* v_unused_5001_; 
v_unused_5001_ = lean_ctor_get(v_a_4972_, 1);
lean_dec(v_unused_5001_);
v___x_4978_ = v_a_4972_;
v_isShared_4979_ = v_isSharedCheck_5000_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_fst_4976_);
lean_dec(v_a_4972_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_5000_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
if (lean_obj_tag(v_fst_4976_) == 0)
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4983_; 
lean_del_object(v___x_4974_);
v___x_4980_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4981_ = l_Lean_MessageData_ofName(v___x_4965_);
lean_inc_ref(v___x_4981_);
if (v_isShared_4979_ == 0)
{
lean_ctor_set_tag(v___x_4978_, 7);
lean_ctor_set(v___x_4978_, 1, v___x_4981_);
lean_ctor_set(v___x_4978_, 0, v___x_4980_);
v___x_4983_ = v___x_4978_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v___x_4980_);
lean_ctor_set(v_reuseFailAlloc_4995_, 1, v___x_4981_);
v___x_4983_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4984_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4983_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
v___x_4986_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_4987_ = l_Lean_indentD(v___x_4986_);
v___x_4988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4985_);
lean_ctor_set(v___x_4988_, 1, v___x_4987_);
v___x_4989_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4988_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
v___x_4991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4990_);
lean_ctor_set(v___x_4991_, 1, v___x_4981_);
v___x_4992_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4991_);
lean_ctor_set(v___x_4993_, 1, v___x_4992_);
v___x_4994_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4993_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_4994_;
}
}
else
{
lean_object* v_val_4996_; lean_object* v___x_4998_; 
lean_del_object(v___x_4978_);
lean_dec(v___x_4965_);
lean_dec(v_stx_2364_);
v_val_4996_ = lean_ctor_get(v_fst_4976_, 0);
lean_inc(v_val_4996_);
lean_dec_ref_known(v_fst_4976_, 1);
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 0, v_val_4996_);
v___x_4998_ = v___x_4974_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_val_4996_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
lean_dec(v___x_4965_);
lean_dec(v_stx_2364_);
v_a_5003_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_5005_ = v___x_4971_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_4971_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
}
}
else
{
v___y_2492_ = v_a_2365_;
v___y_2493_ = v_a_2366_;
v___y_2494_ = v_a_2367_;
v___y_2495_ = v_a_2368_;
v___y_2496_ = v_a_2369_;
v___y_2497_ = v_a_2370_;
goto v___jp_2491_;
}
}
else
{
lean_dec(v___x_4962_);
v___y_2492_ = v_a_2365_;
v___y_2493_ = v_a_2366_;
v___y_2494_ = v_a_2367_;
v___y_2495_ = v_a_2368_;
v___y_2496_ = v_a_2369_;
v___y_2497_ = v_a_2370_;
goto v___jp_2491_;
}
}
}
else
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
lean_del_object(v___x_2404_);
v___x_5011_ = lean_unsigned_to_nat(1u);
v___x_5012_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_5011_);
lean_dec(v_stx_2364_);
v___x_5013_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_5012_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_5013_;
}
}
else
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
lean_del_object(v___x_2404_);
v___x_5014_ = lean_unsigned_to_nat(0u);
v___x_5015_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_5014_);
lean_dec(v_stx_2364_);
v___x_5016_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_5015_);
if (lean_obj_tag(v___x_5016_) == 1)
{
lean_object* v_val_5017_; lean_object* v_snd_5018_; lean_object* v_body_5019_; lean_object* v___x_5020_; 
v_val_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_val_5017_);
lean_dec_ref_known(v___x_5016_, 1);
v_snd_5018_ = lean_ctor_get(v_val_5017_, 1);
lean_inc(v_snd_5018_);
lean_dec(v_val_5017_);
v_body_5019_ = lean_ctor_get(v_snd_5018_, 1);
lean_inc(v_body_5019_);
lean_dec(v_snd_5018_);
v___x_5020_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_5019_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5041_; 
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5023_ = v___x_5020_;
v_isShared_5024_ = v_isSharedCheck_5041_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5020_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5041_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
uint8_t v_breaks_5025_; uint8_t v_continues_5026_; uint8_t v_returnsEarly_5027_; lean_object* v_reassigns_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5039_; 
v_breaks_5025_ = lean_ctor_get_uint8(v_a_5021_, sizeof(void*)*2);
v_continues_5026_ = lean_ctor_get_uint8(v_a_5021_, sizeof(void*)*2 + 1);
v_returnsEarly_5027_ = lean_ctor_get_uint8(v_a_5021_, sizeof(void*)*2 + 2);
v_reassigns_5028_ = lean_ctor_get(v_a_5021_, 1);
v_isSharedCheck_5039_ = !lean_is_exclusive(v_a_5021_);
if (v_isSharedCheck_5039_ == 0)
{
lean_object* v_unused_5040_; 
v_unused_5040_ = lean_ctor_get(v_a_5021_, 0);
lean_dec(v_unused_5040_);
v___x_5030_ = v_a_5021_;
v_isShared_5031_ = v_isSharedCheck_5039_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_reassigns_5028_);
lean_dec(v_a_5021_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5039_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5032_; lean_object* v___x_5034_; 
v___x_5032_ = lean_unsigned_to_nat(1u);
if (v_isShared_5031_ == 0)
{
lean_ctor_set(v___x_5030_, 0, v___x_5032_);
v___x_5034_ = v___x_5030_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5032_);
lean_ctor_set(v_reuseFailAlloc_5038_, 1, v_reassigns_5028_);
lean_ctor_set_uint8(v_reuseFailAlloc_5038_, sizeof(void*)*2, v_breaks_5025_);
lean_ctor_set_uint8(v_reuseFailAlloc_5038_, sizeof(void*)*2 + 1, v_continues_5026_);
lean_ctor_set_uint8(v_reuseFailAlloc_5038_, sizeof(void*)*2 + 2, v_returnsEarly_5027_);
v___x_5034_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
lean_object* v___x_5036_; 
lean_ctor_set_uint8(v___x_5034_, sizeof(void*)*2 + 3, v___x_2608_);
if (v_isShared_5024_ == 0)
{
lean_ctor_set(v___x_5023_, 0, v___x_5034_);
v___x_5036_ = v___x_5023_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
}
else
{
return v___x_5020_;
}
}
else
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
lean_dec(v___x_5016_);
v___x_5042_ = lean_unsigned_to_nat(1u);
v___x_5043_ = l_Lean_NameSet_empty;
v___x_5044_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5044_, 0, v___x_5042_);
lean_ctor_set(v___x_5044_, 1, v___x_5043_);
lean_ctor_set_uint8(v___x_5044_, sizeof(void*)*2, v___x_2608_);
lean_ctor_set_uint8(v___x_5044_, sizeof(void*)*2 + 1, v___x_2608_);
lean_ctor_set_uint8(v___x_5044_, sizeof(void*)*2 + 2, v___x_2608_);
lean_ctor_set_uint8(v___x_5044_, sizeof(void*)*2 + 3, v___x_2608_);
v___x_5045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5044_);
return v___x_5045_;
}
}
}
else
{
lean_object* v___x_5046_; lean_object* v___x_5051_; lean_object* v___x_5052_; uint8_t v___x_5053_; 
lean_del_object(v___x_2404_);
v___x_5046_ = lean_unsigned_to_nat(0u);
v___x_5051_ = lean_unsigned_to_nat(1u);
v___x_5052_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_5051_);
v___x_5053_ = l_Lean_Syntax_isNone(v___x_5052_);
if (v___x_5053_ == 0)
{
uint8_t v___x_5054_; 
v___x_5054_ = l_Lean_Syntax_matchesNull(v___x_5052_, v___x_5051_);
if (v___x_5054_ == 0)
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v_env_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
lean_inc_n(v_stx_2364_, 2);
v___x_5055_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_5056_ = lean_st_ref_get(v_a_2370_);
v_env_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc_ref(v_env_5057_);
lean_dec(v___x_5056_);
v___x_5058_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_5059_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_5058_, v_env_5057_, v___x_5055_);
v___x_5060_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_5061_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_5059_, v___x_5060_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v___x_5059_);
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5092_; 
v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5064_ = v___x_5061_;
v_isShared_5065_ = v_isSharedCheck_5092_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___x_5061_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5092_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v_fst_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5090_; 
v_fst_5066_ = lean_ctor_get(v_a_5062_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v_a_5062_);
if (v_isSharedCheck_5090_ == 0)
{
lean_object* v_unused_5091_; 
v_unused_5091_ = lean_ctor_get(v_a_5062_, 1);
lean_dec(v_unused_5091_);
v___x_5068_ = v_a_5062_;
v_isShared_5069_ = v_isSharedCheck_5090_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_fst_5066_);
lean_dec(v_a_5062_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5090_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
if (lean_obj_tag(v_fst_5066_) == 0)
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5073_; 
lean_del_object(v___x_5064_);
v___x_5070_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_5071_ = l_Lean_MessageData_ofName(v___x_5055_);
lean_inc_ref(v___x_5071_);
if (v_isShared_5069_ == 0)
{
lean_ctor_set_tag(v___x_5068_, 7);
lean_ctor_set(v___x_5068_, 1, v___x_5071_);
lean_ctor_set(v___x_5068_, 0, v___x_5070_);
v___x_5073_ = v___x_5068_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5070_);
lean_ctor_set(v_reuseFailAlloc_5085_, 1, v___x_5071_);
v___x_5073_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5074_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_5075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5075_, 0, v___x_5073_);
lean_ctor_set(v___x_5075_, 1, v___x_5074_);
v___x_5076_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_5077_ = l_Lean_indentD(v___x_5076_);
v___x_5078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5078_, 0, v___x_5075_);
lean_ctor_set(v___x_5078_, 1, v___x_5077_);
v___x_5079_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_5080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5078_);
lean_ctor_set(v___x_5080_, 1, v___x_5079_);
v___x_5081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5080_);
lean_ctor_set(v___x_5081_, 1, v___x_5071_);
v___x_5082_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_5083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5083_, 0, v___x_5081_);
lean_ctor_set(v___x_5083_, 1, v___x_5082_);
v___x_5084_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5083_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_5084_;
}
}
else
{
lean_object* v_val_5086_; lean_object* v___x_5088_; 
lean_del_object(v___x_5068_);
lean_dec(v___x_5055_);
lean_dec(v_stx_2364_);
v_val_5086_ = lean_ctor_get(v_fst_5066_, 0);
lean_inc(v_val_5086_);
lean_dec_ref_known(v_fst_5066_, 1);
if (v_isShared_5065_ == 0)
{
lean_ctor_set(v___x_5064_, 0, v_val_5086_);
v___x_5088_ = v___x_5064_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_val_5086_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
}
}
else
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_dec(v___x_5055_);
lean_dec(v_stx_2364_);
v_a_5093_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5061_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5061_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
else
{
lean_dec(v_stx_2364_);
goto v___jp_5047_;
}
}
else
{
lean_dec(v___x_5052_);
lean_dec(v_stx_2364_);
goto v___jp_5047_;
}
v___jp_5047_:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
v___x_5048_ = l_Lean_NameSet_empty;
v___x_5049_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5049_, 0, v___x_5046_);
lean_ctor_set(v___x_5049_, 1, v___x_5048_);
lean_ctor_set_uint8(v___x_5049_, sizeof(void*)*2, v___x_2606_);
lean_ctor_set_uint8(v___x_5049_, sizeof(void*)*2 + 1, v___x_2606_);
lean_ctor_set_uint8(v___x_5049_, sizeof(void*)*2 + 2, v___x_2604_);
lean_ctor_set_uint8(v___x_5049_, sizeof(void*)*2 + 3, v___x_2604_);
v___x_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5050_, 0, v___x_5049_);
return v___x_5050_;
}
}
}
else
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
lean_del_object(v___x_2404_);
lean_dec(v_stx_2364_);
v___x_5101_ = lean_unsigned_to_nat(0u);
v___x_5102_ = l_Lean_NameSet_empty;
v___x_5103_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5103_, 0, v___x_5101_);
lean_ctor_set(v___x_5103_, 1, v___x_5102_);
lean_ctor_set_uint8(v___x_5103_, sizeof(void*)*2, v___x_2603_);
lean_ctor_set_uint8(v___x_5103_, sizeof(void*)*2 + 1, v___x_2604_);
lean_ctor_set_uint8(v___x_5103_, sizeof(void*)*2 + 2, v___x_2603_);
lean_ctor_set_uint8(v___x_5103_, sizeof(void*)*2 + 3, v___x_2604_);
v___x_5104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5103_);
return v___x_5104_;
}
}
else
{
lean_object* v___x_5105_; lean_object* v___x_5106_; 
lean_del_object(v___x_2404_);
lean_dec(v_stx_2364_);
v___x_5105_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95);
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5105_);
return v___x_5106_;
}
v___jp_2420_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2427_ = lean_unsigned_to_nat(2u);
v___x_2428_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2427_);
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2430_ = l_Lean_Syntax_isOfKind(v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_env_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_inc_n(v_stx_2364_, 2);
v___x_2431_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_2432_ = lean_st_ref_get(v___y_2426_);
v_env_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc_ref(v_env_2433_);
lean_dec(v___x_2432_);
v___x_2434_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2435_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2434_, v_env_2433_, v___x_2431_);
v___x_2436_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2437_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_2435_, v___x_2436_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___x_2435_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2468_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2468_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2468_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v_fst_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2466_; 
v_fst_2442_ = lean_ctor_get(v_a_2438_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_a_2438_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v_a_2438_, 1);
lean_dec(v_unused_2467_);
v___x_2444_ = v_a_2438_;
v_isShared_2445_ = v_isSharedCheck_2466_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_fst_2442_);
lean_dec(v_a_2438_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2466_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
if (lean_obj_tag(v_fst_2442_) == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
lean_del_object(v___x_2440_);
v___x_2446_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2447_ = l_Lean_MessageData_ofName(v___x_2431_);
lean_inc_ref(v___x_2447_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set_tag(v___x_2444_, 7);
lean_ctor_set(v___x_2444_, 1, v___x_2447_);
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2449_ = v___x_2444_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2450_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_2453_ = l_Lean_indentD(v___x_2452_);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2451_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2447_);
v___x_2458_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2459_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2460_;
}
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2464_; 
lean_del_object(v___x_2444_);
lean_dec(v___x_2431_);
lean_dec(v_stx_2364_);
v_val_2462_ = lean_ctor_get(v_fst_2442_, 0);
lean_inc(v_val_2462_);
lean_dec_ref_known(v_fst_2442_, 1);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v_val_2462_);
v___x_2464_ = v___x_2440_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_val_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v___x_2431_);
lean_dec(v_stx_2364_);
v_a_2469_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2437_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2437_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2477_ = lean_unsigned_to_nat(7u);
v___x_2478_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2477_);
v___x_2479_ = lean_unsigned_to_nat(8u);
v___x_2480_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2479_);
lean_dec(v_stx_2364_);
v___x_2481_ = l_Lean_Syntax_getOptional_x3f(v___x_2480_);
lean_dec(v___x_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_box(0);
v___y_2378_ = v___y_2424_;
v___y_2379_ = v___y_2425_;
v___y_2380_ = v___y_2421_;
v___y_2381_ = v___x_2478_;
v___y_2382_ = v___y_2426_;
v___y_2383_ = v___y_2423_;
v___y_2384_ = v___y_2422_;
v___y_2385_ = v___x_2482_;
goto v___jp_2377_;
}
else
{
lean_object* v_val_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
v_val_2483_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2481_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_val_2483_);
lean_dec(v___x_2481_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_val_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
v___y_2378_ = v___y_2424_;
v___y_2379_ = v___y_2425_;
v___y_2380_ = v___y_2421_;
v___y_2381_ = v___x_2478_;
v___y_2382_ = v___y_2426_;
v___y_2383_ = v___y_2423_;
v___y_2384_ = v___y_2422_;
v___y_2385_ = v___x_2488_;
goto v___jp_2377_;
}
}
}
}
}
v___jp_2491_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2498_ = lean_unsigned_to_nat(2u);
v___x_2499_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2498_);
v___x_2500_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2501_ = l_Lean_Syntax_isOfKind(v___x_2499_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v_env_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_del_object(v___x_2404_);
lean_inc_n(v_stx_2364_, 2);
v___x_2502_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_2503_ = lean_st_ref_get(v___y_2497_);
v_env_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc_ref(v_env_2504_);
lean_dec(v___x_2503_);
v___x_2505_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2506_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2505_, v_env_2504_, v___x_2502_);
v___x_2507_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2508_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_2506_, v___x_2507_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___x_2506_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2539_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2539_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2539_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_fst_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2537_; 
v_fst_2513_ = lean_ctor_get(v_a_2509_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_a_2509_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; 
v_unused_2538_ = lean_ctor_get(v_a_2509_, 1);
lean_dec(v_unused_2538_);
v___x_2515_ = v_a_2509_;
v_isShared_2516_ = v_isSharedCheck_2537_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_fst_2513_);
lean_dec(v_a_2509_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2537_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
if (lean_obj_tag(v_fst_2513_) == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
lean_del_object(v___x_2511_);
v___x_2517_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2518_ = l_Lean_MessageData_ofName(v___x_2502_);
lean_inc_ref(v___x_2518_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set_tag(v___x_2515_, 7);
lean_ctor_set(v___x_2515_, 1, v___x_2518_);
lean_ctor_set(v___x_2515_, 0, v___x_2517_);
v___x_2520_ = v___x_2515_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2521_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_2524_ = l_Lean_indentD(v___x_2523_);
v___x_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2522_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
lean_ctor_set(v___x_2528_, 1, v___x_2518_);
v___x_2529_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2530_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2531_;
}
}
else
{
lean_object* v_val_2533_; lean_object* v___x_2535_; 
lean_del_object(v___x_2515_);
lean_dec(v___x_2502_);
lean_dec(v_stx_2364_);
v_val_2533_ = lean_ctor_get(v_fst_2513_, 0);
lean_inc(v_val_2533_);
lean_dec_ref_known(v_fst_2513_, 1);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v_val_2533_);
v___x_2535_ = v___x_2511_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_val_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v___x_2502_);
lean_dec(v_stx_2364_);
v_a_2540_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2508_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2508_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2548_ = lean_unsigned_to_nat(3u);
v___x_2549_ = l_Lean_Syntax_getArg(v_stx_2364_, v___x_2548_);
v___x_2550_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2551_ = l_Lean_Syntax_isOfKind(v___x_2549_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_env_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
lean_del_object(v___x_2404_);
lean_inc_n(v_stx_2364_, 2);
v___x_2552_ = l_Lean_Syntax_getKind(v_stx_2364_);
v___x_2553_ = lean_st_ref_get(v___y_2497_);
v_env_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc_ref(v_env_2554_);
lean_dec(v___x_2553_);
v___x_2555_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2556_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2555_, v_env_2554_, v___x_2552_);
v___x_2557_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2558_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2364_, v___x_2556_, v___x_2557_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___x_2556_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2589_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2589_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2589_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_fst_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2587_; 
v_fst_2563_ = lean_ctor_get(v_a_2559_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_a_2559_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v_a_2559_, 1);
lean_dec(v_unused_2588_);
v___x_2565_ = v_a_2559_;
v_isShared_2566_ = v_isSharedCheck_2587_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_fst_2563_);
lean_dec(v_a_2559_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2587_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
if (lean_obj_tag(v_fst_2563_) == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
lean_del_object(v___x_2561_);
v___x_2567_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2568_ = l_Lean_MessageData_ofName(v___x_2552_);
lean_inc_ref(v___x_2568_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set_tag(v___x_2565_, 7);
lean_ctor_set(v___x_2565_, 1, v___x_2568_);
lean_ctor_set(v___x_2565_, 0, v___x_2567_);
v___x_2570_ = v___x_2565_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2567_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2571_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = l_Lean_MessageData_ofSyntax(v_stx_2364_);
v___x_2574_ = l_Lean_indentD(v___x_2573_);
v___x_2575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2572_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
lean_ctor_set(v___x_2578_, 1, v___x_2568_);
v___x_2579_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2580_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2581_;
}
}
else
{
lean_object* v_val_2583_; lean_object* v___x_2585_; 
lean_del_object(v___x_2565_);
lean_dec(v___x_2552_);
lean_dec(v_stx_2364_);
v_val_2583_ = lean_ctor_get(v_fst_2563_, 0);
lean_inc(v_val_2583_);
lean_dec_ref_known(v_fst_2563_, 1);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v_val_2583_);
v___x_2585_ = v___x_2561_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_val_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v___x_2552_);
lean_dec(v_stx_2364_);
v_a_2590_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2558_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2558_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_dec(v_stx_2364_);
v___x_2598_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2598_);
v___x_2600_ = v___x_2404_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5115_; 
lean_dec(v_stx_2364_);
v_a_5108_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5110_ = v___x_2401_;
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_2401_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
if (v_isShared_5111_ == 0)
{
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5108_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
}
v___jp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2373_, v_bodyInfo_2374_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
v___jp_2377_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2386_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___y_2381_);
v___x_2389_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2386_, v___x_2387_, v___x_2388_, v___y_2385_, v___y_2380_, v___y_2384_, v___y_2383_, v___y_2378_, v___y_2379_, v___y_2382_);
return v___x_2389_;
}
v___jp_2390_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
v___jp_2393_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2394_, v_bodyInfo_2395_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_5116_, size_t v_sz_5117_, size_t v_i_5118_, lean_object* v_b_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
uint8_t v___x_5127_; 
v___x_5127_ = lean_usize_dec_lt(v_i_5118_, v_sz_5117_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; 
v___x_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5128_, 0, v_b_5119_);
return v___x_5128_;
}
else
{
lean_object* v_a_5129_; lean_object* v___x_5130_; 
v_a_5129_ = lean_array_uget_borrowed(v_as_5116_, v_i_5118_);
lean_inc(v_a_5129_);
v___x_5130_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_5129_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; lean_object* v___x_5132_; size_t v___x_5133_; size_t v___x_5134_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref_known(v___x_5130_, 1);
v___x_5132_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_5119_, v_a_5131_);
v___x_5133_ = ((size_t)1ULL);
v___x_5134_ = lean_usize_add(v_i_5118_, v___x_5133_);
v_i_5118_ = v___x_5134_;
v_b_5119_ = v___x_5132_;
goto _start;
}
else
{
lean_dec_ref(v_b_5119_);
return v___x_5130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_){
_start:
{
lean_object* v_info_5144_; lean_object* v___x_5145_; size_t v_sz_5146_; size_t v___x_5147_; lean_object* v___x_5148_; 
v_info_5144_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_5145_ = l_Lean_Parser_Term_getDoElems(v_stx_5136_);
v_sz_5146_ = lean_array_size(v___x_5145_);
v___x_5147_ = ((size_t)0ULL);
v___x_5148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_5145_, v_sz_5146_, v___x_5147_, v_info_5144_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_);
lean_dec_ref(v___x_5145_);
return v___x_5148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_);
lean_dec(v_a_5155_);
lean_dec_ref(v_a_5154_);
lean_dec(v_a_5153_);
lean_dec_ref(v_a_5152_);
lean_dec(v_a_5151_);
lean_dec_ref(v_a_5150_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_){
_start:
{
lean_object* v_res_5166_; 
v_res_5166_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5163_);
lean_dec(v_a_5162_);
lean_dec_ref(v_a_5161_);
lean_dec(v_a_5160_);
lean_dec_ref(v_a_5159_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_5167_, lean_object* v_sz_5168_, lean_object* v_i_5169_, lean_object* v_b_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
size_t v_sz_boxed_5178_; size_t v_i_boxed_5179_; lean_object* v_res_5180_; 
v_sz_boxed_5178_ = lean_unbox_usize(v_sz_5168_);
lean_dec(v_sz_5168_);
v_i_boxed_5179_ = lean_unbox_usize(v_i_5169_);
lean_dec(v_i_5169_);
v_res_5180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_5167_, v_sz_boxed_5178_, v_i_boxed_5179_, v_b_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
lean_dec_ref(v_as_5167_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_5181_, lean_object* v_sz_5182_, lean_object* v_i_5183_, lean_object* v_b_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
size_t v_sz_boxed_5192_; size_t v_i_boxed_5193_; lean_object* v_res_5194_; 
v_sz_boxed_5192_ = lean_unbox_usize(v_sz_5182_);
lean_dec(v_sz_5182_);
v_i_boxed_5193_ = lean_unbox_usize(v_i_5183_);
lean_dec(v_i_5183_);
v_res_5194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_5181_, v_sz_boxed_5192_, v_i_boxed_5193_, v_b_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
lean_dec_ref(v_as_5181_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_5195_, lean_object* v_rhs_x3f_5196_, lean_object* v_otherwise_x3f_5197_, lean_object* v_body_x3f_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_5195_, v_rhs_x3f_5196_, v_otherwise_x3f_5197_, v_body_x3f_5198_, v_a_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
lean_dec(v_a_5204_);
lean_dec_ref(v_a_5203_);
lean_dec(v_a_5202_);
lean_dec_ref(v_a_5201_);
lean_dec(v_a_5200_);
lean_dec_ref(v_a_5199_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_5207_, lean_object* v_as_5208_, lean_object* v_sz_5209_, lean_object* v_i_5210_, lean_object* v_b_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
uint8_t v___x_175964__boxed_5219_; size_t v_sz_boxed_5220_; size_t v_i_boxed_5221_; lean_object* v_res_5222_; 
v___x_175964__boxed_5219_ = lean_unbox(v___x_5207_);
v_sz_boxed_5220_ = lean_unbox_usize(v_sz_5209_);
lean_dec(v_sz_5209_);
v_i_boxed_5221_ = lean_unbox_usize(v_i_5210_);
lean_dec(v_i_5210_);
v_res_5222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_175964__boxed_5219_, v_as_5208_, v_sz_boxed_5220_, v_i_boxed_5221_, v_b_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec_ref(v_as_5208_);
return v_res_5222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_5223_, lean_object* v_as_5224_, lean_object* v_sz_5225_, lean_object* v_i_5226_, lean_object* v_b_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
uint8_t v___x_176011__boxed_5235_; size_t v_sz_boxed_5236_; size_t v_i_boxed_5237_; lean_object* v_res_5238_; 
v___x_176011__boxed_5235_ = lean_unbox(v___x_5223_);
v_sz_boxed_5236_ = lean_unbox_usize(v_sz_5225_);
lean_dec(v_sz_5225_);
v_i_boxed_5237_ = lean_unbox_usize(v_i_5226_);
lean_dec(v_i_5226_);
v_res_5238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_176011__boxed_5235_, v_as_5224_, v_sz_boxed_5236_, v_i_boxed_5237_, v_b_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec(v___y_5229_);
lean_dec_ref(v___y_5228_);
lean_dec_ref(v_as_5224_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_5239_, lean_object* v_sz_5240_, lean_object* v_i_5241_, lean_object* v_b_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
size_t v_sz_boxed_5250_; size_t v_i_boxed_5251_; lean_object* v_res_5252_; 
v_sz_boxed_5250_ = lean_unbox_usize(v_sz_5240_);
lean_dec(v_sz_5240_);
v_i_boxed_5251_ = lean_unbox_usize(v_i_5241_);
lean_dec(v_i_5241_);
v_res_5252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_5239_, v_sz_boxed_5250_, v_i_boxed_5251_, v_b_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec_ref(v___y_5245_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec_ref(v_as_5239_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_5253_, lean_object* v_decl_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_){
_start:
{
uint8_t v_reassignment_boxed_5262_; lean_object* v_res_5263_; 
v_reassignment_boxed_5262_ = lean_unbox(v_reassignment_5253_);
v_res_5263_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_5262_, v_decl_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_);
lean_dec(v_a_5260_);
lean_dec_ref(v_a_5259_);
lean_dec(v_a_5258_);
lean_dec_ref(v_a_5257_);
lean_dec(v_a_5256_);
lean_dec_ref(v_a_5255_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_);
lean_dec(v_a_5270_);
lean_dec_ref(v_a_5269_);
lean_dec(v_a_5268_);
lean_dec_ref(v_a_5267_);
lean_dec(v_a_5266_);
lean_dec_ref(v_a_5265_);
return v_res_5272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object* v_00_u03b1_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_){
_start:
{
lean_object* v___x_5281_; 
v___x_5281_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_5281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_00_u03b1_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
lean_object* v_res_5290_; 
v_res_5290_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_00_u03b1_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
return v_res_5290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_5291_, lean_object* v_ref_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_){
_start:
{
lean_object* v___x_5300_; 
v___x_5300_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_5292_);
return v___x_5300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_5301_, lean_object* v_ref_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_5301_, v_ref_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_5311_, lean_object* v_x_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
lean_object* v___x_5320_; 
v___x_5320_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_);
return v___x_5320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_5321_, lean_object* v_x_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_5321_, v_x_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
return v_res_5330_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_5331_, lean_object* v_as_5332_, lean_object* v_as_x27_5333_, lean_object* v_b_5334_, lean_object* v_a_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
lean_object* v___x_5343_; 
v___x_5343_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_5331_, v_as_x27_5333_, v_b_5334_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
return v___x_5343_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_5344_, lean_object* v_as_5345_, lean_object* v_as_x27_5346_, lean_object* v_b_5347_, lean_object* v_a_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_5344_, v_as_5345_, v_as_x27_5346_, v_b_5347_, v_a_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec(v_as_x27_5346_);
lean_dec(v_as_5345_);
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_5357_, lean_object* v_msg_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_){
_start:
{
lean_object* v___x_5366_; 
v___x_5366_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
return v___x_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_5367_, lean_object* v_msg_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_5367_, v_msg_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_5377_, lean_object* v_msg_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_){
_start:
{
lean_object* v___x_5386_; 
v___x_5386_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_5377_, v_msg_5378_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
return v___x_5386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_5387_, lean_object* v_msg_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_5387_, v_msg_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_5397_, lean_object* v_as_x27_5398_, lean_object* v_b_5399_, lean_object* v_a_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_){
_start:
{
lean_object* v___x_5408_; 
v___x_5408_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_5398_, v_b_5399_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
return v___x_5408_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_5409_, lean_object* v_as_x27_5410_, lean_object* v_b_5411_, lean_object* v_a_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
lean_object* v_res_5420_; 
v_res_5420_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_5409_, v_as_x27_5410_, v_b_5411_, v_a_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
lean_dec(v_as_x27_5410_);
lean_dec(v_as_5409_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_5421_, lean_object* v_ref_5422_, lean_object* v_msg_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_){
_start:
{
lean_object* v___x_5431_; 
v___x_5431_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_5422_, v_msg_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
return v___x_5431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_5432_, lean_object* v_ref_5433_, lean_object* v_msg_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_){
_start:
{
lean_object* v_res_5442_; 
v_res_5442_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_5432_, v_ref_5433_, v_msg_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec(v_ref_5433_);
return v_res_5442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_5443_, lean_object* v_macroStack_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v___x_5452_; 
v___x_5452_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_5443_, v_macroStack_5444_, v___y_5449_);
return v___x_5452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_5453_, lean_object* v_macroStack_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_5453_, v_macroStack_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_5463_, lean_object* v_m_5464_, lean_object* v_a_5465_){
_start:
{
lean_object* v___x_5466_; 
v___x_5466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_5464_, v_a_5465_);
return v___x_5466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_5467_, lean_object* v_m_5468_, lean_object* v_a_5469_){
_start:
{
lean_object* v_res_5470_; 
v_res_5470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_5467_, v_m_5468_, v_a_5469_);
lean_dec(v_a_5469_);
lean_dec_ref(v_m_5468_);
return v_res_5470_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_5471_, lean_object* v_x_5472_, lean_object* v_x_5473_){
_start:
{
uint8_t v___x_5474_; 
v___x_5474_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_5472_, v_x_5473_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_5475_, lean_object* v_x_5476_, lean_object* v_x_5477_){
_start:
{
uint8_t v_res_5478_; lean_object* v_r_5479_; 
v_res_5478_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_5475_, v_x_5476_, v_x_5477_);
lean_dec_ref(v_x_5477_);
lean_dec_ref(v_x_5476_);
v_r_5479_ = lean_box(v_res_5478_);
return v_r_5479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_5480_, lean_object* v_a_5481_, lean_object* v_x_5482_){
_start:
{
lean_object* v___x_5483_; 
v___x_5483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_5481_, v_x_5482_);
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_5484_, lean_object* v_a_5485_, lean_object* v_x_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_5484_, v_a_5485_, v_x_5486_);
lean_dec(v_x_5486_);
lean_dec(v_a_5485_);
return v_res_5487_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_5488_, lean_object* v_x_5489_, size_t v_x_5490_, lean_object* v_x_5491_){
_start:
{
uint8_t v___x_5492_; 
v___x_5492_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_5489_, v_x_5490_, v_x_5491_);
return v___x_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_5493_, lean_object* v_x_5494_, lean_object* v_x_5495_, lean_object* v_x_5496_){
_start:
{
size_t v_x_183026__boxed_5497_; uint8_t v_res_5498_; lean_object* v_r_5499_; 
v_x_183026__boxed_5497_ = lean_unbox_usize(v_x_5495_);
lean_dec(v_x_5495_);
v_res_5498_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_5493_, v_x_5494_, v_x_183026__boxed_5497_, v_x_5496_);
lean_dec_ref(v_x_5496_);
lean_dec_ref(v_x_5494_);
v_r_5499_ = lean_box(v_res_5498_);
return v_r_5499_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_5500_, lean_object* v_keys_5501_, lean_object* v_vals_5502_, lean_object* v_heq_5503_, lean_object* v_i_5504_, lean_object* v_k_5505_){
_start:
{
uint8_t v___x_5506_; 
v___x_5506_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_5501_, v_i_5504_, v_k_5505_);
return v___x_5506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_5507_, lean_object* v_keys_5508_, lean_object* v_vals_5509_, lean_object* v_heq_5510_, lean_object* v_i_5511_, lean_object* v_k_5512_){
_start:
{
uint8_t v_res_5513_; lean_object* v_r_5514_; 
v_res_5513_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_5507_, v_keys_5508_, v_vals_5509_, v_heq_5510_, v_i_5511_, v_k_5512_);
lean_dec_ref(v_k_5512_);
lean_dec_ref(v_vals_5509_);
lean_dec_ref(v_keys_5508_);
v_r_5514_ = lean_box(v_res_5513_);
return v_r_5514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_){
_start:
{
lean_object* v___x_5523_; 
v___x_5523_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_);
return v___x_5523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_){
_start:
{
lean_object* v_res_5532_; 
v_res_5532_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_);
lean_dec(v_a_5530_);
lean_dec_ref(v_a_5529_);
lean_dec(v_a_5528_);
lean_dec_ref(v_a_5527_);
lean_dec(v_a_5526_);
lean_dec_ref(v_a_5525_);
return v_res_5532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_){
_start:
{
lean_object* v___x_5541_; 
v___x_5541_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_5533_, v_a_5534_, v_a_5535_, v_a_5536_, v_a_5537_, v_a_5538_, v_a_5539_);
return v___x_5541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_){
_start:
{
lean_object* v_res_5550_; 
v_res_5550_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_5542_, v_a_5543_, v_a_5544_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_);
lean_dec(v_a_5548_);
lean_dec_ref(v_a_5547_);
lean_dec(v_a_5546_);
lean_dec_ref(v_a_5545_);
lean_dec(v_a_5544_);
lean_dec_ref(v_a_5543_);
return v_res_5550_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_ForwardSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Do_instInhabitedControlInfo_default = _init_l_Lean_Elab_Do_instInhabitedControlInfo_default();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo_default);
l_Lean_Elab_Do_instInhabitedControlInfo = _init_l_Lean_Elab_Do_instInhabitedControlInfo();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo);
l_Lean_Elab_Do_ControlInfo_pure = _init_l_Lean_Elab_Do_ControlInfo_pure();
lean_mark_persistent(l_Lean_Elab_Do_ControlInfo_pure);
l_Lean_Elab_Do_ControlInfo_empty = _init_l_Lean_Elab_Do_ControlInfo_empty();
lean_mark_persistent(l_Lean_Elab_Do_ControlInfo_empty);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Do_controlInfoElemAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Do_controlInfoElemAttribute);
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_ForwardSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Do_InferControlInfo(builtin);
}
#ifdef __cplusplus
}
#endif
