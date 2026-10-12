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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Parser_Term_getDoElems(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
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
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "No `ControlInfo` inference handler found for `"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "` in syntax "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "\nRegister a handler with `@[doElem_control_info "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]`."};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object* v_ref_222_){
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
LEAN_EXPORT void l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_222_ = stack[0].m_obj;
lean_object* v_res_230_;
v_res_230_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v_ref_222_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object* v_ref_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v_ref_231_);
return v_res_233_;
}
}
lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_242_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_243_;
v_res_243_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2____boxed(lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
return v_res_245_;
}
}
lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1(){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_249_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0));
v___x_250_ = l_Lean_addBuiltinDocString(v___x_248_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_251_;
v_res_251_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
return v_res_253_;
}
}
lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3(){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_281_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6));
v___x_282_ = l_Lean_addBuiltinDeclarationRanges(v___x_280_, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_283_;
v_res_283_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
return v_res_285_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object* v_msgData_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___x_292_; lean_object* v_env_293_; uint8_t v___x_294_; lean_object* v_env_295_; lean_object* v___x_296_; lean_object* v_toCold_297_; lean_object* v_mctx_298_; lean_object* v_lctx_299_; lean_object* v_options_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_292_ = lean_st_ref_get(v___y_290_);
v_env_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_env_293_);
lean_dec(v___x_292_);
v___x_294_ = 0;
v_env_295_ = l_Lean_Environment_setRecordingDeps(v_env_293_, v___x_294_);
v___x_296_ = lean_st_ref_get(v___y_288_);
v_toCold_297_ = lean_ctor_get(v___y_289_, 0);
v_mctx_298_ = lean_ctor_get(v___x_296_, 0);
lean_inc_ref(v_mctx_298_);
lean_dec(v___x_296_);
v_lctx_299_ = lean_ctor_get(v___y_287_, 2);
v_options_300_ = lean_ctor_get(v_toCold_297_, 2);
lean_inc_ref(v_options_300_);
lean_inc_ref(v_lctx_299_);
v___x_301_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_301_, 0, v_env_295_);
lean_ctor_set(v___x_301_, 1, v_mctx_298_);
lean_ctor_set(v___x_301_, 2, v_lctx_299_);
lean_ctor_set(v___x_301_, 3, v_options_300_);
v___x_302_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v_msgData_286_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_286_ = stack[0].m_obj;
lean_object* v___y_287_ = stack[1].m_obj;
lean_object* v___y_288_ = stack[2].m_obj;
lean_object* v___y_289_ = stack[3].m_obj;
lean_object* v___y_290_ = stack[4].m_obj;
lean_object* v_res_304_;
v_res_304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
stack->m_obj
 = v_res_304_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_311_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_box(1);
v___x_313_ = l_Lean_MessageData_ofFormat(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_318_ = l_Lean_MessageData_ofFormat(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
return v_x_319_;
}
else
{
lean_object* v_head_321_; lean_object* v_tail_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_344_; 
v_head_321_ = lean_ctor_get(v_x_320_, 0);
v_tail_322_ = lean_ctor_get(v_x_320_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_320_);
if (v_isSharedCheck_344_ == 0)
{
v___x_324_ = v_x_320_;
v_isShared_325_ = v_isSharedCheck_344_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_tail_322_);
lean_inc(v_head_321_);
lean_dec(v_x_320_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_344_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_before_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_342_; 
v_before_326_ = lean_ctor_get(v_head_321_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_head_321_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; 
v_unused_343_ = lean_ctor_get(v_head_321_, 1);
lean_dec(v_unused_343_);
v___x_328_ = v_head_321_;
v_isShared_329_ = v_isSharedCheck_342_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_before_326_);
lean_dec(v_head_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_342_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 7);
lean_ctor_set(v___x_328_, 1, v___x_330_);
lean_ctor_set(v___x_328_, 0, v_x_319_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_x_319_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_341_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 7);
lean_ctor_set(v___x_324_, 1, v___x_333_);
lean_ctor_set(v___x_324_, 0, v___x_332_);
v___x_335_ = v___x_324_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_340_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = l_Lean_MessageData_ofSyntax(v_before_326_);
v___x_337_ = l_Lean_indentD(v___x_336_);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_335_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v_x_319_ = v___x_338_;
v_x_320_ = v_tail_322_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_345_, lean_object* v_opt_346_){
_start:
{
lean_object* v_name_347_; lean_object* v_defValue_348_; lean_object* v_map_349_; lean_object* v___x_350_; 
v_name_347_ = lean_ctor_get(v_opt_346_, 0);
v_defValue_348_ = lean_ctor_get(v_opt_346_, 1);
v_map_349_ = lean_ctor_get(v_opts_345_, 0);
v___x_350_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_349_, v_name_347_);
if (lean_obj_tag(v___x_350_) == 0)
{
uint8_t v___x_351_; 
v___x_351_ = lean_unbox(v_defValue_348_);
return v___x_351_;
}
else
{
lean_object* v_val_352_; 
v_val_352_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_val_352_);
lean_dec_ref_known(v___x_350_, 1);
if (lean_obj_tag(v_val_352_) == 1)
{
uint8_t v_v_353_; 
v_v_353_ = lean_ctor_get_uint8(v_val_352_, 0);
lean_dec_ref_known(v_val_352_, 0);
return v_v_353_;
}
else
{
uint8_t v___x_354_; 
lean_dec(v_val_352_);
v___x_354_ = lean_unbox(v_defValue_348_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_345_ = stack[0].m_obj;
lean_object* v_opt_346_ = stack[1].m_obj;
uint8_t v_res_355_;
v_res_355_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_345_, v_opt_346_);
stack->m_num = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_356_, lean_object* v_opt_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_356_, v_opt_357_);
lean_dec_ref(v_opt_357_);
lean_dec_ref(v_opts_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_364_ = l_Lean_MessageData_ofFormat(v___x_363_);
return v___x_364_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_365_, lean_object* v_macroStack_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_369_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_367_);
v___x_370_ = l_Lean_Elab_pp_macroStack;
v___x_371_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v___x_369_, v___x_370_);
lean_dec_ref(v___x_369_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec(v_macroStack_366_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v_msgData_365_);
return v___x_372_;
}
else
{
if (lean_obj_tag(v_macroStack_366_) == 0)
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v_msgData_365_);
return v___x_373_;
}
else
{
lean_object* v_head_374_; lean_object* v_after_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_390_; 
v_head_374_ = lean_ctor_get(v_macroStack_366_, 0);
lean_inc(v_head_374_);
v_after_375_ = lean_ctor_get(v_head_374_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_head_374_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v_head_374_, 0);
lean_dec(v_unused_391_);
v___x_377_ = v_head_374_;
v_isShared_378_ = v_isSharedCheck_390_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_after_375_);
lean_dec(v_head_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_390_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 7);
lean_ctor_set(v___x_377_, 1, v___x_379_);
lean_ctor_set(v___x_377_, 0, v_msgData_365_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_msgData_365_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_379_);
v___x_381_ = v_reuseFailAlloc_389_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_msgData_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_382_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = l_Lean_MessageData_ofSyntax(v_after_375_);
v___x_385_ = l_Lean_indentD(v___x_384_);
v_msgData_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_386_, 0, v___x_383_);
lean_ctor_set(v_msgData_386_, 1, v___x_385_);
v___x_387_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_386_, v_macroStack_366_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_365_ = stack[0].m_obj;
lean_object* v_macroStack_366_ = stack[1].m_obj;
lean_object* v___y_367_ = stack[2].m_obj;
lean_object* v_res_392_;
v_res_392_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_365_, v_macroStack_366_, v___y_367_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_393_, lean_object* v_macroStack_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_393_, v_macroStack_394_, v___y_395_);
lean_dec_ref(v___y_395_);
return v_res_397_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_ref_406_; lean_object* v_macroStack_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_a_410_; lean_object* v___x_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
v_ref_406_ = lean_ctor_get(v___y_403_, 2);
v_macroStack_407_ = lean_ctor_get(v___y_399_, 1);
v___x_408_ = l_Lean_Elab_getBetterRef(v_ref_406_, v_macroStack_407_);
v___x_409_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_398_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref(v___x_409_);
lean_inc(v_macroStack_407_);
v___x_411_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_410_, v_macroStack_407_, v___y_403_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_408_);
lean_ctor_set(v___x_416_, 1, v_a_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 1);
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_398_ = stack[0].m_obj;
lean_object* v___y_399_ = stack[1].m_obj;
lean_object* v___y_400_ = stack[2].m_obj;
lean_object* v___y_401_ = stack[3].m_obj;
lean_object* v___y_402_ = stack[4].m_obj;
lean_object* v___y_403_ = stack[5].m_obj;
lean_object* v___y_404_ = stack[6].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_430_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_431_, size_t v_i_432_, size_t v_stop_433_, lean_object* v_b_434_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = lean_usize_dec_eq(v_i_432_, v_stop_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; size_t v___x_438_; size_t v___x_439_; 
v___x_436_ = lean_array_uget_borrowed(v_as_431_, v_i_432_);
lean_inc(v___x_436_);
v___x_437_ = l_Lean_NameSet_insert(v_b_434_, v___x_436_);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_add(v_i_432_, v___x_438_);
v_i_432_ = v___x_439_;
v_b_434_ = v___x_437_;
goto _start;
}
else
{
return v_b_434_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_431_ = stack[0].m_obj;
size_t v_i_432_ = stack[1].m_num;
size_t v_stop_433_ = stack[2].m_num;
lean_object* v_b_434_ = stack[3].m_obj;
lean_object* v_res_441_;
v_res_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_431_, v_i_432_, v_stop_433_, v_b_434_);
stack->m_obj
 = v_res_441_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_442_, lean_object* v_i_443_, lean_object* v_stop_444_, lean_object* v_b_445_){
_start:
{
size_t v_i_boxed_446_; size_t v_stop_boxed_447_; lean_object* v_res_448_; 
v_i_boxed_446_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_stop_boxed_447_ = lean_unbox_usize(v_stop_444_);
lean_dec(v_stop_444_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_442_, v_i_boxed_446_, v_stop_boxed_447_, v_b_445_);
lean_dec_ref(v_as_442_);
return v_res_448_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_449_, size_t v_i_450_, lean_object* v_bs_451_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = lean_usize_dec_lt(v_i_450_, v_sz_449_);
if (v___x_452_ == 0)
{
return v_bs_451_;
}
else
{
lean_object* v_v_453_; lean_object* v___x_454_; lean_object* v_bs_x27_455_; lean_object* v___x_456_; size_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; 
v_v_453_ = lean_array_uget(v_bs_451_, v_i_450_);
v___x_454_ = lean_unsigned_to_nat(0u);
v_bs_x27_455_ = lean_array_uset(v_bs_451_, v_i_450_, v___x_454_);
v___x_456_ = l_Lean_TSyntax_getId(v_v_453_);
lean_dec(v_v_453_);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_add(v_i_450_, v___x_457_);
v___x_459_ = lean_array_uset(v_bs_x27_455_, v_i_450_, v___x_456_);
v_i_450_ = v___x_458_;
v_bs_451_ = v___x_459_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20_0interp(lean_interpreter_value* stack)
{
size_t v_sz_449_ = stack[0].m_num;
size_t v_i_450_ = stack[1].m_num;
lean_object* v_bs_451_ = stack[2].m_obj;
lean_object* v_res_461_;
v_res_461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_449_, v_i_450_, v_bs_451_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_462_, lean_object* v_i_463_, lean_object* v_bs_464_){
_start:
{
size_t v_sz_boxed_465_; size_t v_i_boxed_466_; lean_object* v_res_467_; 
v_sz_boxed_465_ = lean_unbox_usize(v_sz_462_);
lean_dec(v_sz_462_);
v_i_boxed_466_ = lean_unbox_usize(v_i_463_);
lean_dec(v_i_463_);
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_465_, v_i_boxed_466_, v_bs_464_);
return v_res_467_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_box(0);
v___x_469_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
return v___x_470_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg(){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_474_;
v_res_474_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v_res_476_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t v_sz_477_, size_t v_i_478_, lean_object* v_bs_479_){
_start:
{
uint8_t v___x_480_; 
v___x_480_ = lean_usize_dec_lt(v_i_478_, v_sz_477_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v_bs_479_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v_bs_x27_483_; lean_object* v___x_484_; size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v_bs_x27_483_ = lean_array_uset(v_bs_479_, v_i_478_, v___x_482_);
v___x_484_ = lean_box(0);
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_add(v_i_478_, v___x_485_);
v___x_487_ = lean_array_uset(v_bs_x27_483_, v_i_478_, v___x_484_);
v_i_478_ = v___x_486_;
v_bs_479_ = v___x_487_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_477_ = stack[0].m_num;
size_t v_i_478_ = stack[1].m_num;
lean_object* v_bs_479_ = stack[2].m_obj;
lean_object* v_res_489_;
v_res_489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_477_, v_i_478_, v_bs_479_);
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_sz_490_, lean_object* v_i_491_, lean_object* v_bs_492_){
_start:
{
size_t v_sz_boxed_493_; size_t v_i_boxed_494_; lean_object* v_res_495_; 
v_sz_boxed_493_ = lean_unbox_usize(v_sz_490_);
lean_dec(v_sz_490_);
v_i_boxed_494_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_res_495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_boxed_493_, v_i_boxed_494_, v_bs_492_);
return v_res_495_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_496_, uint8_t v___x_497_, lean_object* v_as_498_, size_t v_i_499_, size_t v_stop_500_, lean_object* v_b_501_){
_start:
{
lean_object* v___y_503_; uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_eq(v_i_499_, v_stop_500_);
if (v___x_507_ == 0)
{
lean_object* v_fst_508_; uint8_t v___x_509_; 
v_fst_508_ = lean_ctor_get(v_b_501_, 0);
v___x_509_ = lean_unbox(v_fst_508_);
if (v___x_509_ == 0)
{
lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_snd_510_ = lean_ctor_get(v_b_501_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_b_501_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_b_501_, 0);
lean_dec(v_unused_519_);
v___x_512_ = v_b_501_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_dec(v_b_501_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_box(v___x_496_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_snd_510_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v___y_503_ = v___x_516_;
goto v___jp_502_;
}
}
}
else
{
lean_object* v_snd_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_530_; 
v_snd_520_ = lean_ctor_get(v_b_501_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_b_501_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_b_501_, 0);
lean_dec(v_unused_531_);
v___x_522_ = v_b_501_;
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snd_520_);
lean_dec(v_b_501_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_524_ = lean_array_uget_borrowed(v_as_498_, v_i_499_);
lean_inc(v___x_524_);
v___x_525_ = lean_array_push(v_snd_520_, v___x_524_);
v___x_526_ = lean_box(v___x_497_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_525_);
lean_ctor_set(v___x_522_, 0, v___x_526_);
v___x_528_ = v___x_522_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_525_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v___y_503_ = v___x_528_;
goto v___jp_502_;
}
}
}
}
else
{
return v_b_501_;
}
v___jp_502_:
{
size_t v___x_504_; size_t v___x_505_; 
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_499_, v___x_504_);
v_i_499_ = v___x_505_;
v_b_501_ = v___y_503_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_496_ = stack[0].m_num;
uint8_t v___x_497_ = stack[1].m_num;
lean_object* v_as_498_ = stack[2].m_obj;
size_t v_i_499_ = stack[3].m_num;
size_t v_stop_500_ = stack[4].m_num;
lean_object* v_b_501_ = stack[5].m_obj;
lean_object* v_res_532_;
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_496_, v___x_497_, v_as_498_, v_i_499_, v_stop_500_, v_b_501_);
stack->m_obj
 = v_res_532_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v_as_535_, lean_object* v_i_536_, lean_object* v_stop_537_, lean_object* v_b_538_){
_start:
{
uint8_t v___x_175964__boxed_539_; uint8_t v___x_175965__boxed_540_; size_t v_i_boxed_541_; size_t v_stop_boxed_542_; lean_object* v_res_543_; 
v___x_175964__boxed_539_ = lean_unbox(v___x_533_);
v___x_175965__boxed_540_ = lean_unbox(v___x_534_);
v_i_boxed_541_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_stop_boxed_542_ = lean_unbox_usize(v_stop_537_);
lean_dec(v_stop_537_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_175964__boxed_539_, v___x_175965__boxed_540_, v_as_535_, v_i_boxed_541_, v_stop_boxed_542_, v_b_538_);
lean_dec_ref(v_as_535_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_544_, lean_object* v___y_545_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; 
v_a_546_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_a_546_);
v___x_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_547_, 0, v_a_546_);
lean_ctor_set(v___x_547_, 1, v___y_545_);
return v___x_547_;
}
else
{
lean_object* v_a_548_; lean_object* v___x_549_; 
v_a_548_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_a_548_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_a_548_);
lean_ctor_set(v___x_549_, 1, v___y_545_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_550_, v___y_551_);
lean_dec_ref(v_x_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_553_, lean_object* v_stx_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_553_, v_stx_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
if (lean_obj_tag(v_a_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_a_559_ = lean_ctor_get(v___x_557_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v___x_557_, 0);
lean_dec(v_unused_568_);
v___x_561_ = v___x_557_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_box(0);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_a_559_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_597_; 
v_val_569_ = lean_ctor_get(v_a_558_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_558_);
if (v_isSharedCheck_597_ == 0)
{
v___x_571_ = v_a_558_;
v_isShared_572_ = v_isSharedCheck_597_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v_a_558_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_597_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_snd_573_; 
v_snd_573_ = lean_ctor_get(v_val_569_, 1);
lean_inc(v_snd_573_);
lean_dec(v_val_569_);
if (lean_obj_tag(v_snd_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_583_; 
lean_del_object(v___x_571_);
v_a_574_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_557_, 2);
v_a_575_ = lean_ctor_get(v_snd_573_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_573_);
if (v_isSharedCheck_583_ == 0)
{
v___x_577_ = v_snd_573_;
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v_snd_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_582_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; 
v___x_581_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_580_, v_a_574_);
lean_dec_ref(v___x_580_);
return v___x_581_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_596_; 
v_a_584_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_557_, 2);
v_a_585_ = lean_ctor_get(v_snd_573_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v_snd_573_);
if (v_isSharedCheck_596_ == 0)
{
v___x_587_ = v_snd_573_;
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v_snd_573_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_a_585_);
v___x_590_ = v___x_571_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_595_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_592_, v_a_584_);
lean_dec_ref(v___x_592_);
return v___x_593_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_598_ = lean_ctor_get(v___x_557_, 0);
v_a_599_ = lean_ctor_get(v___x_557_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_557_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_inc(v_a_598_);
lean_dec(v___x_557_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_598_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_607_, lean_object* v_stx_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_607_, v_stx_608_, v___y_609_, v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_611_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = l_Lean_maxRecDepthErrorMessage;
v___x_618_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_620_ = l_Lean_MessageData_ofFormat(v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_622_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_623_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
return v___x_623_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_624_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_ref_624_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_624_ = stack[0].m_obj;
lean_object* v_res_629_;
v_res_629_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_624_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_633_, lean_object* v_declName_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
uint8_t v___x_637_; lean_object* v_env_638_; lean_object* v___x_639_; uint8_t v___x_640_; uint8_t v___x_641_; 
v___x_637_ = 0;
v_env_638_ = l_Lean_Environment_setExporting(v_env_633_, v___x_637_);
lean_inc(v_declName_634_);
v___x_639_ = l_Lean_mkPrivateName(v_env_638_, v_declName_634_);
v___x_640_ = 1;
lean_inc_ref(v_env_638_);
v___x_641_ = l_Lean_Environment_contains(v_env_638_, v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = l_Lean_privateToUserName(v_declName_634_);
v___x_643_ = l_Lean_Environment_contains(v_env_638_, v___x_642_, v___x_640_);
v___x_644_ = lean_box(v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___y_636_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec_ref(v_env_638_);
lean_dec(v_declName_634_);
v___x_646_ = lean_box(v___x_641_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v___y_636_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_648_, lean_object* v_declName_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_648_, v_declName_649_, v___y_650_, v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_652_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_653_, lean_object* v_msg_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_toCold_662_; lean_object* v_currRecDepth_663_; lean_object* v_ref_664_; uint16_t v_optionFlags_665_; uint8_t v_suppressElabErrors_666_; uint8_t v_isRecordingDeps_667_; lean_object* v_ref_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_toCold_662_ = lean_ctor_get(v___y_659_, 0);
v_currRecDepth_663_ = lean_ctor_get(v___y_659_, 1);
v_ref_664_ = lean_ctor_get(v___y_659_, 2);
v_optionFlags_665_ = lean_ctor_get_uint16(v___y_659_, sizeof(void*)*3);
v_suppressElabErrors_666_ = lean_ctor_get_uint8(v___y_659_, sizeof(void*)*3 + 2);
v_isRecordingDeps_667_ = lean_ctor_get_uint8(v___y_659_, sizeof(void*)*3 + 3);
v_ref_668_ = l_Lean_replaceRef(v_ref_653_, v_ref_664_);
lean_inc(v_currRecDepth_663_);
lean_inc_ref(v_toCold_662_);
v___x_669_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_669_, 0, v_toCold_662_);
lean_ctor_set(v___x_669_, 1, v_currRecDepth_663_);
lean_ctor_set(v___x_669_, 2, v_ref_668_);
lean_ctor_set_uint16(v___x_669_, sizeof(void*)*3, v_optionFlags_665_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*3 + 2, v_suppressElabErrors_666_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*3 + 3, v_isRecordingDeps_667_);
v___x_670_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___x_669_, v___y_660_);
lean_dec_ref_known(v___x_669_, 3);
return v___x_670_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_653_ = stack[0].m_obj;
lean_object* v_msg_654_ = stack[1].m_obj;
lean_object* v___y_655_ = stack[2].m_obj;
lean_object* v___y_656_ = stack[3].m_obj;
lean_object* v___y_657_ = stack[4].m_obj;
lean_object* v___y_658_ = stack[5].m_obj;
lean_object* v___y_659_ = stack[6].m_obj;
lean_object* v___y_660_ = stack[7].m_obj;
lean_object* v_res_671_;
v_res_671_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_653_, v_msg_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_672_, v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v_ref_672_);
return v_res_681_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_682_; double v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_float_of_nat(v___x_682_);
return v___x_683_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_687_, lean_object* v_msg_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_ref_694_; lean_object* v___x_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_741_; 
v_ref_694_ = lean_ctor_get(v___y_691_, 2);
v___x_695_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_741_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_741_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_741_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v_traceState_701_; lean_object* v_env_702_; lean_object* v_nextMacroScope_703_; lean_object* v_ngen_704_; lean_object* v_auxDeclNGen_705_; lean_object* v_cache_706_; lean_object* v_recordedDeps_707_; lean_object* v_messages_708_; lean_object* v_infoState_709_; lean_object* v_snapshotTasks_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_740_; 
v___x_700_ = lean_st_ref_take(v___y_692_);
v_traceState_701_ = lean_ctor_get(v___x_700_, 4);
v_env_702_ = lean_ctor_get(v___x_700_, 0);
v_nextMacroScope_703_ = lean_ctor_get(v___x_700_, 1);
v_ngen_704_ = lean_ctor_get(v___x_700_, 2);
v_auxDeclNGen_705_ = lean_ctor_get(v___x_700_, 3);
v_cache_706_ = lean_ctor_get(v___x_700_, 5);
v_recordedDeps_707_ = lean_ctor_get(v___x_700_, 6);
v_messages_708_ = lean_ctor_get(v___x_700_, 7);
v_infoState_709_ = lean_ctor_get(v___x_700_, 8);
v_snapshotTasks_710_ = lean_ctor_get(v___x_700_, 9);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_740_ == 0)
{
v___x_712_ = v___x_700_;
v_isShared_713_ = v_isSharedCheck_740_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snapshotTasks_710_);
lean_inc(v_infoState_709_);
lean_inc(v_messages_708_);
lean_inc(v_recordedDeps_707_);
lean_inc(v_cache_706_);
lean_inc(v_traceState_701_);
lean_inc(v_auxDeclNGen_705_);
lean_inc(v_ngen_704_);
lean_inc(v_nextMacroScope_703_);
lean_inc(v_env_702_);
lean_dec(v___x_700_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_740_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint64_t v_tid_714_; lean_object* v_traces_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_739_; 
v_tid_714_ = lean_ctor_get_uint64(v_traceState_701_, sizeof(void*)*1);
v_traces_715_ = lean_ctor_get(v_traceState_701_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_traceState_701_);
if (v_isSharedCheck_739_ == 0)
{
v___x_717_ = v_traceState_701_;
v_isShared_718_ = v_isSharedCheck_739_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_traces_715_);
lean_dec(v_traceState_701_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_739_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_720_; double v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_719_ = lean_box(0);
v___x_720_ = lean_box(0);
v___x_721_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_722_ = 0;
v___x_723_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_724_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_724_, 0, v_cls_687_);
lean_ctor_set(v___x_724_, 1, v___x_720_);
lean_ctor_set(v___x_724_, 2, v___x_723_);
lean_ctor_set_float(v___x_724_, sizeof(void*)*3, v___x_721_);
lean_ctor_set_float(v___x_724_, sizeof(void*)*3 + 8, v___x_721_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*3 + 16, v___x_722_);
v___x_725_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_726_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v_a_696_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
lean_inc(v_ref_694_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_ref_694_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_PersistentArray_push___redArg(v_traces_715_, v___x_727_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_728_);
v___x_730_ = v___x_717_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_728_);
lean_ctor_set_uint64(v_reuseFailAlloc_738_, sizeof(void*)*1, v_tid_714_);
v___x_730_ = v_reuseFailAlloc_738_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 4, v___x_730_);
v___x_732_ = v___x_712_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_env_702_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_nextMacroScope_703_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_ngen_704_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_auxDeclNGen_705_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_737_, 5, v_cache_706_);
lean_ctor_set(v_reuseFailAlloc_737_, 6, v_recordedDeps_707_);
lean_ctor_set(v_reuseFailAlloc_737_, 7, v_messages_708_);
lean_ctor_set(v_reuseFailAlloc_737_, 8, v_infoState_709_);
lean_ctor_set(v_reuseFailAlloc_737_, 9, v_snapshotTasks_710_);
v___x_732_ = v_reuseFailAlloc_737_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = lean_st_ref_put(v___y_692_, v___x_732_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_719_);
v___x_735_ = v___x_698_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_719_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_687_ = stack[0].m_obj;
lean_object* v_msg_688_ = stack[1].m_obj;
lean_object* v___y_689_ = stack[2].m_obj;
lean_object* v___y_690_ = stack[3].m_obj;
lean_object* v___y_691_ = stack[4].m_obj;
lean_object* v___y_692_ = stack[5].m_obj;
lean_object* v_res_742_;
v_res_742_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_687_, v_msg_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
stack->m_obj
 = v_res_742_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_743_, lean_object* v_msg_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_743_, v_msg_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_750_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
if (lean_obj_tag(v_as_754_) == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
else
{
lean_object* v_toCold_764_; lean_object* v_options_765_; uint8_t v_hasTrace_766_; 
v_toCold_764_ = lean_ctor_get(v___y_759_, 0);
v_options_765_ = lean_ctor_get(v_toCold_764_, 2);
v_hasTrace_766_ = lean_ctor_get_uint8(v_options_765_, sizeof(void*)*1);
if (v_hasTrace_766_ == 0)
{
lean_object* v_tail_767_; 
v_tail_767_ = lean_ctor_get(v_as_754_, 1);
lean_inc(v_tail_767_);
lean_dec_ref_known(v_as_754_, 2);
v_as_754_ = v_tail_767_;
goto _start;
}
else
{
lean_object* v_head_769_; lean_object* v_tail_770_; lean_object* v_fst_771_; lean_object* v_snd_772_; lean_object* v_inheritedTraceOptions_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_head_769_ = lean_ctor_get(v_as_754_, 0);
lean_inc(v_head_769_);
v_tail_770_ = lean_ctor_get(v_as_754_, 1);
lean_inc(v_tail_770_);
lean_dec_ref_known(v_as_754_, 2);
v_fst_771_ = lean_ctor_get(v_head_769_, 0);
lean_inc_n(v_fst_771_, 2);
v_snd_772_ = lean_ctor_get(v_head_769_, 1);
lean_inc(v_snd_772_);
lean_dec(v_head_769_);
v_inheritedTraceOptions_773_ = lean_ctor_get(v_toCold_764_, 11);
v___x_774_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_775_ = l_Lean_Name_append(v___x_774_, v_fst_771_);
v___x_776_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_773_, v_options_765_, v___x_775_);
lean_dec(v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v_snd_772_);
lean_dec(v_fst_771_);
v_as_754_ = v_tail_770_;
goto _start;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_778_, 0, v_snd_772_);
v___x_779_ = l_Lean_MessageData_ofFormat(v___x_778_);
v___x_780_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_771_, v___x_779_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_dec_ref_known(v___x_780_, 1);
v_as_754_ = v_tail_770_;
goto _start;
}
else
{
lean_dec(v_tail_770_);
return v___x_780_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_754_ = stack[0].m_obj;
lean_object* v___y_755_ = stack[1].m_obj;
lean_object* v___y_756_ = stack[2].m_obj;
lean_object* v___y_757_ = stack[3].m_obj;
lean_object* v___y_758_ = stack[4].m_obj;
lean_object* v___y_759_ = stack[5].m_obj;
lean_object* v___y_760_ = stack[6].m_obj;
lean_object* v_res_782_;
v_res_782_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_792_, lean_object* v_x_793_){
_start:
{
if (lean_obj_tag(v_x_793_) == 0)
{
lean_object* v___x_794_; 
v___x_794_ = lean_box(0);
return v___x_794_;
}
else
{
lean_object* v_key_795_; lean_object* v_value_796_; lean_object* v_tail_797_; uint8_t v___x_798_; 
v_key_795_ = lean_ctor_get(v_x_793_, 0);
v_value_796_ = lean_ctor_get(v_x_793_, 1);
v_tail_797_ = lean_ctor_get(v_x_793_, 2);
v___x_798_ = lean_name_eq(v_key_795_, v_a_792_);
if (v___x_798_ == 0)
{
v_x_793_ = v_tail_797_;
goto _start;
}
else
{
lean_object* v___x_800_; 
lean_inc(v_value_796_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v_value_796_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_801_, lean_object* v_x_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_801_, v_x_802_);
lean_dec(v_x_802_);
lean_dec(v_a_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_buckets_806_; lean_object* v___x_807_; uint64_t v___y_809_; 
v_buckets_806_ = lean_ctor_get(v_m_804_, 1);
v___x_807_ = lean_array_get_size(v_buckets_806_);
if (lean_obj_tag(v_a_805_) == 0)
{
uint64_t v___x_823_; 
v___x_823_ = 1723ULL;
v___y_809_ = v___x_823_;
goto v___jp_808_;
}
else
{
uint64_t v_hash_824_; 
v_hash_824_ = lean_ctor_get_uint64(v_a_805_, sizeof(void*)*2);
v___y_809_ = v_hash_824_;
goto v___jp_808_;
}
v___jp_808_:
{
uint64_t v___x_810_; uint64_t v___x_811_; uint64_t v_fold_812_; uint64_t v___x_813_; uint64_t v___x_814_; uint64_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_810_ = 32ULL;
v___x_811_ = lean_uint64_shift_right(v___y_809_, v___x_810_);
v_fold_812_ = lean_uint64_xor(v___y_809_, v___x_811_);
v___x_813_ = 16ULL;
v___x_814_ = lean_uint64_shift_right(v_fold_812_, v___x_813_);
v___x_815_ = lean_uint64_xor(v_fold_812_, v___x_814_);
v___x_816_ = lean_uint64_to_usize(v___x_815_);
v___x_817_ = lean_usize_of_nat(v___x_807_);
v___x_818_ = ((size_t)1ULL);
v___x_819_ = lean_usize_sub(v___x_817_, v___x_818_);
v___x_820_ = lean_usize_land(v___x_816_, v___x_819_);
v___x_821_ = lean_array_uget_borrowed(v_buckets_806_, v___x_820_);
v___x_822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_805_, v___x_821_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_m_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0(lean_object* v___x_828_, lean_object* v_entry_829_, lean_object* v_s_830_){
_start:
{
lean_object* v_addEntryFn_831_; lean_object* v_importedEntries_832_; lean_object* v_state_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_addEntryFn_831_ = lean_ctor_get(v___x_828_, 3);
lean_inc(v_addEntryFn_831_);
lean_dec_ref(v___x_828_);
v_importedEntries_832_ = lean_ctor_get(v_s_830_, 0);
v_state_833_ = lean_ctor_get(v_s_830_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_s_830_);
if (v_isSharedCheck_841_ == 0)
{
v___x_835_ = v_s_830_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_state_833_);
lean_inc(v_importedEntries_832_);
lean_dec(v_s_830_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_state_837_; lean_object* v___x_839_; 
v_state_837_ = lean_apply_2(v_addEntryFn_831_, v_state_833_, v_entry_829_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_state_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_importedEntries_832_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_state_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_842_, lean_object* v_i_843_, lean_object* v_k_844_){
_start:
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_array_get_size(v_keys_842_);
v___x_846_ = lean_nat_dec_lt(v_i_843_, v___x_845_);
if (v___x_846_ == 0)
{
lean_dec(v_i_843_);
return v___x_846_;
}
else
{
lean_object* v_k_x27_847_; uint8_t v___x_848_; 
v_k_x27_847_ = lean_array_fget_borrowed(v_keys_842_, v_i_843_);
v___x_848_ = l_Lean_instBEqExtraModUse_beq(v_k_844_, v_k_x27_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_add(v_i_843_, v___x_849_);
lean_dec(v_i_843_);
v_i_843_ = v___x_850_;
goto _start;
}
else
{
lean_dec(v_i_843_);
return v___x_846_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_842_ = stack[0].m_obj;
lean_object* v_i_843_ = stack[1].m_obj;
lean_object* v_k_844_ = stack[2].m_obj;
uint8_t v_res_852_;
v_res_852_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_842_, v_i_843_, v_k_844_);
stack->m_num = v_res_852_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_853_, lean_object* v_i_854_, lean_object* v_k_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_853_, v_i_854_, v_k_855_);
lean_dec_ref(v_k_855_);
lean_dec_ref(v_keys_853_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_858_, size_t v_x_859_, lean_object* v_x_860_){
_start:
{
if (lean_obj_tag(v_x_858_) == 0)
{
lean_object* v_es_861_; lean_object* v___x_862_; size_t v___x_863_; size_t v___x_864_; lean_object* v_j_865_; lean_object* v___x_866_; 
v_es_861_ = lean_ctor_get(v_x_858_, 0);
v___x_862_ = lean_box(2);
v___x_863_ = ((size_t)31ULL);
v___x_864_ = lean_usize_land(v_x_859_, v___x_863_);
v_j_865_ = lean_usize_to_nat(v___x_864_);
v___x_866_ = lean_array_get_borrowed(v___x_862_, v_es_861_, v_j_865_);
lean_dec(v_j_865_);
switch(lean_obj_tag(v___x_866_))
{
case 0:
{
lean_object* v_key_867_; uint8_t v___x_868_; 
v_key_867_ = lean_ctor_get(v___x_866_, 0);
v___x_868_ = l_Lean_instBEqExtraModUse_beq(v_x_860_, v_key_867_);
return v___x_868_;
}
case 1:
{
lean_object* v_node_869_; size_t v___x_870_; size_t v___x_871_; 
v_node_869_ = lean_ctor_get(v___x_866_, 0);
v___x_870_ = ((size_t)5ULL);
v___x_871_ = lean_usize_shift_right(v_x_859_, v___x_870_);
v_x_858_ = v_node_869_;
v_x_859_ = v___x_871_;
goto _start;
}
default: 
{
uint8_t v___x_873_; 
v___x_873_ = 0;
return v___x_873_;
}
}
}
else
{
lean_object* v_ks_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v_ks_874_ = lean_ctor_get(v_x_858_, 0);
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_874_, v___x_875_, v_x_860_);
return v___x_876_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_858_ = stack[0].m_obj;
size_t v_x_859_ = stack[1].m_num;
lean_object* v_x_860_ = stack[2].m_obj;
uint8_t v_res_877_;
v_res_877_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_858_, v_x_859_, v_x_860_);
stack->m_num = v_res_877_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
size_t v_x_176758__boxed_881_; uint8_t v_res_882_; lean_object* v_r_883_; 
v_x_176758__boxed_881_ = lean_unbox_usize(v_x_879_);
lean_dec(v_x_879_);
v_res_882_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_878_, v_x_176758__boxed_881_, v_x_880_);
lean_dec_ref(v_x_880_);
lean_dec_ref(v_x_878_);
v_r_883_ = lean_box(v_res_882_);
return v_r_883_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
uint64_t v___x_886_; size_t v___x_887_; uint8_t v___x_888_; 
v___x_886_ = l_Lean_instHashableExtraModUse_hash(v_x_885_);
v___x_887_ = lean_uint64_to_usize(v___x_886_);
v___x_888_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_884_, v___x_887_, v_x_885_);
return v___x_888_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_884_ = stack[0].m_obj;
lean_object* v_x_885_ = stack[1].m_obj;
uint8_t v_res_889_;
v_res_889_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_884_, v_x_885_);
stack->m_num = v_res_889_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_890_, v_x_891_);
lean_dec_ref(v_x_891_);
lean_dec_ref(v_x_890_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0(void){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_894_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_900_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
lean_ctor_set(v___x_900_, 2, v___x_899_);
lean_ctor_set(v___x_900_, 3, v___x_899_);
lean_ctor_set(v___x_900_, 4, v___x_899_);
lean_ctor_set(v___x_900_, 5, v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v_cls_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_cls_913_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_914_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_915_ = l_Lean_Name_append(v___x_914_, v_cls_913_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13));
v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
return v___x_918_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_926_, uint8_t v_isMeta_927_, lean_object* v_hint_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_env_970_; uint8_t v_isExporting_971_; lean_object* v_entry_972_; lean_object* v___x_973_; lean_object* v_env_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_968_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_969_ = lean_st_ref_get(v___y_934_);
v_env_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_970_);
lean_dec(v___x_969_);
v_isExporting_971_ = lean_ctor_get_uint8(v_env_970_, sizeof(void*)*13);
lean_dec_ref(v_env_970_);
lean_inc(v_mod_926_);
v_entry_972_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_972_, 0, v_mod_926_);
lean_ctor_set_uint8(v_entry_972_, sizeof(void*)*1, v_isExporting_971_);
lean_ctor_set_uint8(v_entry_972_, sizeof(void*)*1 + 1, v_isMeta_927_);
v___x_973_ = lean_st_ref_get(v___y_934_);
v_env_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc_ref(v_env_974_);
lean_dec(v___x_973_);
v___x_975_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_976_ = lean_box(1);
v___x_977_ = lean_box(0);
v___x_978_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_968_, v___x_975_, v_env_974_, v___x_976_, v___x_977_);
v___x_979_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_978_, v_entry_972_);
lean_dec(v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v_toCold_980_; lean_object* v_options_981_; lean_object* v_inheritedTraceOptions_982_; uint8_t v_hasTrace_983_; lean_object* v___f_984_; uint8_t v___x_985_; lean_object* v___y_987_; lean_object* v___y_988_; 
v_toCold_980_ = lean_ctor_get(v___y_933_, 0);
v_options_981_ = lean_ctor_get(v_toCold_980_, 2);
v_inheritedTraceOptions_982_ = lean_ctor_get(v_toCold_980_, 11);
v_hasTrace_983_ = lean_ctor_get_uint8(v_options_981_, sizeof(void*)*1);
v___f_984_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0), 3, 2);
lean_closure_set(v___f_984_, 0, v___x_975_);
lean_closure_set(v___f_984_, 1, v_entry_972_);
v___x_985_ = 1;
if (v_hasTrace_983_ == 0)
{
lean_dec(v_hint_928_);
lean_dec(v_mod_926_);
v___y_987_ = v___y_932_;
v___y_988_ = v___y_934_;
goto v___jp_986_;
}
else
{
lean_object* v_cls_1015_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v_cls_1015_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_1035_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_1036_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_982_, v_options_981_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_dec(v_hint_928_);
lean_dec(v_mod_926_);
v___y_987_ = v___y_932_;
v___y_988_ = v___y_934_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1037_; lean_object* v___y_1039_; 
v___x_1037_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
if (v_isExporting_971_ == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_1039_ = v___x_1046_;
goto v___jp_1038_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_1039_ = v___x_1047_;
goto v___jp_1038_;
}
v___jp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_inc_ref(v___y_1039_);
v___x_1040_ = l_Lean_stringToMessageData(v___y_1039_);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1037_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
if (v_isMeta_927_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___y_1022_ = v___x_1043_;
v___y_1023_ = v___x_1044_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18));
v___y_1022_ = v___x_1043_;
v___y_1023_ = v___x_1045_;
goto v___jp_1021_;
}
}
}
v___jp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___y_1017_);
lean_ctor_set(v___x_1019_, 1, v___y_1018_);
v___x_1020_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_1015_, v___x_1019_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_dec_ref_known(v___x_1020_, 1);
v___y_987_ = v___y_932_;
v___y_988_ = v___y_934_;
goto v___jp_986_;
}
else
{
lean_dec_ref(v___f_984_);
return v___x_1020_;
}
}
v___jp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
lean_inc_ref(v___y_1023_);
v___x_1024_ = l_Lean_stringToMessageData(v___y_1023_);
v___x_1025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___y_1022_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_MessageData_ofName(v_mod_926_);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = l_Lean_Name_isAnonymous(v_hint_928_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_1032_ = l_Lean_MessageData_ofName(v_hint_928_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___y_1017_ = v___x_1029_;
v___y_1018_ = v___x_1033_;
goto v___jp_1016_;
}
else
{
lean_object* v___x_1034_; 
lean_dec(v_hint_928_);
v___x_1034_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11);
v___y_1017_ = v___x_1029_;
v___y_1018_ = v___x_1034_;
goto v___jp_1016_;
}
}
}
v___jp_986_:
{
lean_object* v___x_989_; lean_object* v_toEnvExtension_990_; uint8_t v_logWrites_991_; 
v___x_989_ = lean_st_ref_take(v___y_988_);
v_toEnvExtension_990_ = lean_ctor_get(v___x_975_, 0);
v_logWrites_991_ = lean_ctor_get_uint8(v_toEnvExtension_990_, sizeof(void*)*6);
if (v_logWrites_991_ == 0)
{
lean_object* v_env_992_; lean_object* v_nextMacroScope_993_; lean_object* v_ngen_994_; lean_object* v_auxDeclNGen_995_; lean_object* v_traceState_996_; lean_object* v_recordedDeps_997_; lean_object* v_messages_998_; lean_object* v_infoState_999_; lean_object* v_snapshotTasks_1000_; lean_object* v_asyncMode_1001_; lean_object* v___x_1002_; 
v_env_992_ = lean_ctor_get(v___x_989_, 0);
lean_inc_ref(v_env_992_);
v_nextMacroScope_993_ = lean_ctor_get(v___x_989_, 1);
lean_inc(v_nextMacroScope_993_);
v_ngen_994_ = lean_ctor_get(v___x_989_, 2);
lean_inc_ref(v_ngen_994_);
v_auxDeclNGen_995_ = lean_ctor_get(v___x_989_, 3);
lean_inc_ref(v_auxDeclNGen_995_);
v_traceState_996_ = lean_ctor_get(v___x_989_, 4);
lean_inc_ref(v_traceState_996_);
v_recordedDeps_997_ = lean_ctor_get(v___x_989_, 6);
lean_inc_ref(v_recordedDeps_997_);
v_messages_998_ = lean_ctor_get(v___x_989_, 7);
lean_inc_ref(v_messages_998_);
v_infoState_999_ = lean_ctor_get(v___x_989_, 8);
lean_inc_ref(v_infoState_999_);
v_snapshotTasks_1000_ = lean_ctor_get(v___x_989_, 9);
lean_inc_ref(v_snapshotTasks_1000_);
lean_dec(v___x_989_);
v_asyncMode_1001_ = lean_ctor_get(v_toEnvExtension_990_, 2);
lean_inc_ref(v_toEnvExtension_990_);
v___x_1002_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_990_, v_env_992_, v___f_984_, v_asyncMode_1001_, v___x_977_, v___x_985_);
v___y_937_ = v_recordedDeps_997_;
v___y_938_ = v_traceState_996_;
v___y_939_ = v___y_987_;
v___y_940_ = v___y_988_;
v___y_941_ = v_auxDeclNGen_995_;
v___y_942_ = v_messages_998_;
v___y_943_ = v_ngen_994_;
v___y_944_ = v_nextMacroScope_993_;
v___y_945_ = v_snapshotTasks_1000_;
v___y_946_ = v_infoState_999_;
v___y_947_ = v___x_1002_;
goto v___jp_936_;
}
else
{
lean_object* v_env_1003_; lean_object* v_nextMacroScope_1004_; lean_object* v_ngen_1005_; lean_object* v_auxDeclNGen_1006_; lean_object* v_traceState_1007_; lean_object* v_recordedDeps_1008_; lean_object* v_messages_1009_; lean_object* v_infoState_1010_; lean_object* v_snapshotTasks_1011_; lean_object* v_asyncMode_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_env_1003_ = lean_ctor_get(v___x_989_, 0);
lean_inc_ref(v_env_1003_);
v_nextMacroScope_1004_ = lean_ctor_get(v___x_989_, 1);
lean_inc(v_nextMacroScope_1004_);
v_ngen_1005_ = lean_ctor_get(v___x_989_, 2);
lean_inc_ref(v_ngen_1005_);
v_auxDeclNGen_1006_ = lean_ctor_get(v___x_989_, 3);
lean_inc_ref(v_auxDeclNGen_1006_);
v_traceState_1007_ = lean_ctor_get(v___x_989_, 4);
lean_inc_ref(v_traceState_1007_);
v_recordedDeps_1008_ = lean_ctor_get(v___x_989_, 6);
lean_inc_ref(v_recordedDeps_1008_);
v_messages_1009_ = lean_ctor_get(v___x_989_, 7);
lean_inc_ref(v_messages_1009_);
v_infoState_1010_ = lean_ctor_get(v___x_989_, 8);
lean_inc_ref(v_infoState_1010_);
v_snapshotTasks_1011_ = lean_ctor_get(v___x_989_, 9);
lean_inc_ref(v_snapshotTasks_1011_);
lean_dec(v___x_989_);
v_asyncMode_1012_ = lean_ctor_get(v_toEnvExtension_990_, 2);
lean_inc_ref_n(v_toEnvExtension_990_, 2);
v___x_1013_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_990_, v_env_1003_);
lean_dec_ref(v_env_1003_);
v___x_1014_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_990_, v___x_1013_, v___f_984_, v_asyncMode_1012_, v___x_977_, v___x_985_);
v___y_937_ = v_recordedDeps_1008_;
v___y_938_ = v_traceState_1007_;
v___y_939_ = v___y_987_;
v___y_940_ = v___y_988_;
v___y_941_ = v_auxDeclNGen_1006_;
v___y_942_ = v_messages_1009_;
v___y_943_ = v_ngen_1005_;
v___y_944_ = v_nextMacroScope_1004_;
v___y_945_ = v_snapshotTasks_1011_;
v___y_946_ = v_infoState_1010_;
v___y_947_ = v___x_1014_;
goto v___jp_936_;
}
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref_known(v_entry_972_, 1);
lean_dec(v_hint_928_);
lean_dec(v_mod_926_);
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
v___jp_936_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_mctx_952_; lean_object* v_zetaDeltaFVarIds_953_; lean_object* v_postponed_954_; lean_object* v_diag_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_966_; 
v___x_948_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
v___x_949_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_949_, 0, v___y_947_);
lean_ctor_set(v___x_949_, 1, v___y_944_);
lean_ctor_set(v___x_949_, 2, v___y_943_);
lean_ctor_set(v___x_949_, 3, v___y_941_);
lean_ctor_set(v___x_949_, 4, v___y_938_);
lean_ctor_set(v___x_949_, 5, v___x_948_);
lean_ctor_set(v___x_949_, 6, v___y_937_);
lean_ctor_set(v___x_949_, 7, v___y_942_);
lean_ctor_set(v___x_949_, 8, v___y_946_);
lean_ctor_set(v___x_949_, 9, v___y_945_);
v___x_950_ = lean_st_ref_put(v___y_940_, v___x_949_);
v___x_951_ = lean_st_ref_take(v___y_939_);
v_mctx_952_ = lean_ctor_get(v___x_951_, 0);
v_zetaDeltaFVarIds_953_ = lean_ctor_get(v___x_951_, 2);
v_postponed_954_ = lean_ctor_get(v___x_951_, 3);
v_diag_955_ = lean_ctor_get(v___x_951_, 4);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_951_, 1);
lean_dec(v_unused_967_);
v___x_957_ = v___x_951_;
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_diag_955_);
lean_inc(v_postponed_954_);
lean_inc(v_zetaDeltaFVarIds_953_);
lean_inc(v_mctx_952_);
lean_dec(v___x_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_959_ = lean_box(0);
v___x_960_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_960_);
v___x_962_ = v___x_957_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_mctx_952_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_zetaDeltaFVarIds_953_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_postponed_954_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_diag_955_);
v___x_962_ = v_reuseFailAlloc_965_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_st_ref_put(v___y_939_, v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_959_);
return v___x_964_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_926_ = stack[0].m_obj;
uint8_t v_isMeta_927_ = stack[1].m_num;
lean_object* v_hint_928_ = stack[2].m_obj;
lean_object* v___y_929_ = stack[3].m_obj;
lean_object* v___y_930_ = stack[4].m_obj;
lean_object* v___y_931_ = stack[5].m_obj;
lean_object* v___y_932_ = stack[6].m_obj;
lean_object* v___y_933_ = stack[7].m_obj;
lean_object* v___y_934_ = stack[8].m_obj;
lean_object* v_res_1050_;
v_res_1050_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_926_, v_isMeta_927_, v_hint_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_1051_, lean_object* v_isMeta_1052_, lean_object* v_hint_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
uint8_t v_isMeta_boxed_1061_; lean_object* v_res_1062_; 
v_isMeta_boxed_1061_ = lean_unbox(v_isMeta_1052_);
v_res_1062_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_1051_, v_isMeta_boxed_1061_, v_hint_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1062_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1063_, lean_object* v_declName_1064_, lean_object* v_as_1065_, size_t v_sz_1066_, size_t v_i_1067_, lean_object* v_b_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_usize_dec_lt(v_i_1067_, v_sz_1066_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
lean_dec(v_declName_1064_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_b_1068_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; lean_object* v_modules_1079_; lean_object* v___x_1080_; lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v_toImport_1083_; lean_object* v_module_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1078_ = l_Lean_Environment_header(v___x_1063_);
v_modules_1079_ = lean_ctor_get(v___x_1078_, 3);
lean_inc_ref(v_modules_1079_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1081_ = lean_array_uget_borrowed(v_as_1065_, v_i_1067_);
v___x_1082_ = lean_array_get(v___x_1080_, v_modules_1079_, v_a_1081_);
lean_dec_ref(v_modules_1079_);
v_toImport_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_toImport_1083_);
lean_dec(v___x_1082_);
v_module_1084_ = lean_ctor_get(v_toImport_1083_, 0);
lean_inc(v_module_1084_);
lean_dec_ref(v_toImport_1083_);
v___x_1085_ = lean_box(0);
v___x_1086_ = 0;
lean_inc(v_declName_1064_);
v___x_1087_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1084_, v___x_1086_, v_declName_1064_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1087_) == 0)
{
size_t v___x_1088_; size_t v___x_1089_; 
lean_dec_ref_known(v___x_1087_, 1);
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1067_, v___x_1088_);
v_i_1067_ = v___x_1089_;
v_b_1068_ = v___x_1085_;
goto _start;
}
else
{
lean_dec(v_declName_1064_);
return v___x_1087_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1063_ = stack[0].m_obj;
lean_object* v_declName_1064_ = stack[1].m_obj;
lean_object* v_as_1065_ = stack[2].m_obj;
size_t v_sz_1066_ = stack[3].m_num;
size_t v_i_1067_ = stack[4].m_num;
lean_object* v_b_1068_ = stack[5].m_obj;
lean_object* v___y_1069_ = stack[6].m_obj;
lean_object* v___y_1070_ = stack[7].m_obj;
lean_object* v___y_1071_ = stack[8].m_obj;
lean_object* v___y_1072_ = stack[9].m_obj;
lean_object* v___y_1073_ = stack[10].m_obj;
lean_object* v___y_1074_ = stack[11].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1063_, v_declName_1064_, v_as_1065_, v_sz_1066_, v_i_1067_, v_b_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1092_, lean_object* v_declName_1093_, lean_object* v_as_1094_, lean_object* v_sz_1095_, lean_object* v_i_1096_, lean_object* v_b_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
size_t v_sz_boxed_1105_; size_t v_i_boxed_1106_; lean_object* v_res_1107_; 
v_sz_boxed_1105_ = lean_unbox_usize(v_sz_1095_);
lean_dec(v_sz_1095_);
v_i_boxed_1106_ = lean_unbox_usize(v_i_1096_);
lean_dec(v_i_1096_);
v_res_1107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1092_, v_declName_1093_, v_as_1094_, v_sz_boxed_1105_, v_i_boxed_1106_, v_b_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec_ref(v_as_1094_);
lean_dec_ref(v___x_1092_);
return v_res_1107_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1108_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1111_, uint8_t v_isMeta_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_env_1125_; lean_object* v___y_1127_; lean_object* v___x_1140_; 
v___x_1120_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0);
v___x_1121_ = lean_st_ref_get(v___y_1118_);
v_env_1125_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_env_1125_);
lean_dec(v___x_1121_);
v___x_1140_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1125_, v_declName_1111_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_dec_ref(v_env_1125_);
lean_dec(v_declName_1111_);
goto v___jp_1122_;
}
else
{
lean_object* v_val_1141_; lean_object* v___x_1142_; lean_object* v_modules_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_val_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_val_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = l_Lean_Environment_header(v_env_1125_);
v_modules_1143_ = lean_ctor_get(v___x_1142_, 3);
lean_inc_ref(v_modules_1143_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = lean_array_get_size(v_modules_1143_);
v___x_1145_ = lean_nat_dec_lt(v_val_1141_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec_ref(v_modules_1143_);
lean_dec(v_val_1141_);
lean_dec_ref(v_env_1125_);
lean_dec(v_declName_1111_);
goto v___jp_1122_;
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___y_1149_; 
v___x_1146_ = lean_array_fget(v_modules_1143_, v_val_1141_);
lean_dec(v_val_1141_);
lean_dec_ref(v_modules_1143_);
v___x_1147_ = lean_st_ref_get(v___y_1118_);
if (v_isMeta_1112_ == 0)
{
lean_dec(v___x_1147_);
v___y_1149_ = v_isMeta_1112_;
goto v___jp_1148_;
}
else
{
lean_object* v_env_1160_; uint8_t v___x_1161_; 
v_env_1160_ = lean_ctor_get(v___x_1147_, 0);
lean_inc_ref(v_env_1160_);
lean_dec(v___x_1147_);
lean_inc(v_declName_1111_);
v___x_1161_ = l_Lean_isMarkedMeta(v_env_1160_, v_declName_1111_);
if (v___x_1161_ == 0)
{
v___y_1149_ = v_isMeta_1112_;
goto v___jp_1148_;
}
else
{
uint8_t v___x_1162_; 
v___x_1162_ = 0;
v___y_1149_ = v___x_1162_;
goto v___jp_1148_;
}
}
v___jp_1148_:
{
lean_object* v_toImport_1150_; lean_object* v_module_1151_; lean_object* v___x_1152_; 
v_toImport_1150_ = lean_ctor_get(v___x_1146_, 0);
lean_inc_ref(v_toImport_1150_);
lean_dec(v___x_1146_);
v_module_1151_ = lean_ctor_get(v_toImport_1150_, 0);
lean_inc(v_module_1151_);
lean_dec_ref(v_toImport_1150_);
lean_inc(v_declName_1111_);
v___x_1152_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1151_, v___y_1149_, v_declName_1111_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref_known(v___x_1152_, 1);
v___x_1153_ = l_Lean_indirectModUseExt;
v___x_1154_ = lean_box(1);
v___x_1155_ = lean_box(0);
lean_inc_ref(v_env_1125_);
v___x_1156_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1120_, v___x_1153_, v_env_1125_, v___x_1154_, v___x_1155_);
v___x_1157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1156_, v_declName_1111_);
lean_dec(v___x_1156_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___y_1127_ = v___x_1158_;
goto v___jp_1126_;
}
else
{
lean_object* v_val_1159_; 
v_val_1159_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_val_1159_);
lean_dec_ref_known(v___x_1157_, 1);
v___y_1127_ = v_val_1159_;
goto v___jp_1126_;
}
}
else
{
lean_dec_ref(v_env_1125_);
lean_dec(v_declName_1111_);
return v___x_1152_;
}
}
}
}
v___jp_1122_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
v___jp_1126_:
{
lean_object* v___x_1128_; size_t v_sz_1129_; size_t v___x_1130_; lean_object* v___x_1131_; 
v___x_1128_ = lean_box(0);
v_sz_1129_ = lean_array_size(v___y_1127_);
v___x_1130_ = ((size_t)0ULL);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1125_, v_declName_1111_, v___y_1127_, v_sz_1129_, v___x_1130_, v___x_1128_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec_ref(v___y_1127_);
lean_dec_ref(v_env_1125_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v___x_1131_, 0);
lean_dec(v_unused_1139_);
v___x_1133_ = v___x_1131_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_dec(v___x_1131_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1128_);
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1128_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
return v___x_1131_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1111_ = stack[0].m_obj;
uint8_t v_isMeta_1112_ = stack[1].m_num;
lean_object* v___y_1113_ = stack[2].m_obj;
lean_object* v___y_1114_ = stack[3].m_obj;
lean_object* v___y_1115_ = stack[4].m_obj;
lean_object* v___y_1116_ = stack[5].m_obj;
lean_object* v___y_1117_ = stack[6].m_obj;
lean_object* v___y_1118_ = stack[7].m_obj;
lean_object* v_res_1163_;
v_res_1163_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1111_, v_isMeta_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
stack->m_obj
 = v_res_1163_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1164_, lean_object* v_isMeta_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
uint8_t v_isMeta_boxed_1173_; lean_object* v_res_1174_; 
v_isMeta_boxed_1173_ = lean_unbox(v_isMeta_1165_);
v_res_1174_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1164_, v_isMeta_boxed_1173_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1174_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1175_, lean_object* v_b_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
if (lean_obj_tag(v_as_x27_1175_) == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_b_1176_);
return v___x_1184_;
}
else
{
lean_object* v_head_1185_; lean_object* v_tail_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; 
v_head_1185_ = lean_ctor_get(v_as_x27_1175_, 0);
v_tail_1186_ = lean_ctor_get(v_as_x27_1175_, 1);
v___x_1187_ = lean_box(0);
v___x_1188_ = 1;
lean_inc(v_head_1185_);
v___x_1189_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1185_, v___x_1188_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_dec_ref_known(v___x_1189_, 1);
v_as_x27_1175_ = v_tail_1186_;
v_b_1176_ = v___x_1187_;
goto _start;
}
else
{
return v___x_1189_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1175_ = stack[0].m_obj;
lean_object* v_b_1176_ = stack[1].m_obj;
lean_object* v___y_1177_ = stack[2].m_obj;
lean_object* v___y_1178_ = stack[3].m_obj;
lean_object* v___y_1179_ = stack[4].m_obj;
lean_object* v___y_1180_ = stack[5].m_obj;
lean_object* v___y_1181_ = stack[6].m_obj;
lean_object* v___y_1182_ = stack[7].m_obj;
lean_object* v_res_1191_;
v_res_1191_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1175_, v_b_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
stack->m_obj
 = v_res_1191_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1192_, lean_object* v_b_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1192_, v_b_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v_as_x27_1192_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_currNamespace_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v_currNamespace_1202_);
lean_ctor_set(v___x_1205_, 1, v___y_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_currNamespace_1206_, v___y_1207_, v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_env_1210_, lean_object* v___x_1211_, lean_object* v_currNamespace_1212_, lean_object* v_openDecls_1213_, lean_object* v_n_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = l_Lean_ResolveName_resolveGlobalName(v_env_1210_, v___x_1211_, v_currNamespace_1212_, v_openDecls_1213_, v_n_1214_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___y_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_env_1219_, lean_object* v___x_1220_, lean_object* v_currNamespace_1221_, lean_object* v_openDecls_1222_, lean_object* v_n_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_env_1219_, v___x_1220_, v_currNamespace_1221_, v_openDecls_1222_, v_n_1223_, v___y_1224_, v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___x_1220_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1227_, lean_object* v_currNamespace_1228_, lean_object* v_openDecls_1229_, lean_object* v_n_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = l_Lean_ResolveName_resolveNamespace(v_env_1227_, v_currNamespace_1228_, v_openDecls_1229_, v_n_1230_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___y_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1235_, lean_object* v_currNamespace_1236_, lean_object* v_openDecls_1237_, lean_object* v_n_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1235_, v_currNamespace_1236_, v_openDecls_1237_, v_n_1238_, v___y_1239_, v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1241_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; lean_object* v_toCold_1252_; lean_object* v_env_1253_; lean_object* v_currRecDepth_1254_; lean_object* v_ref_1255_; lean_object* v_maxRecDepth_1256_; lean_object* v_currNamespace_1257_; lean_object* v_openDecls_1258_; lean_object* v_quotContext_1259_; lean_object* v_currMacroScope_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v_methods_1267_; lean_object* v___x_1268_; lean_object* v_nextMacroScope_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1251_ = lean_st_ref_get(v___y_1249_);
v_toCold_1252_ = lean_ctor_get(v___y_1248_, 0);
v_env_1253_ = lean_ctor_get(v___x_1251_, 0);
lean_inc_ref_n(v_env_1253_, 4);
lean_dec(v___x_1251_);
v_currRecDepth_1254_ = lean_ctor_get(v___y_1248_, 1);
v_ref_1255_ = lean_ctor_get(v___y_1248_, 2);
v_maxRecDepth_1256_ = lean_ctor_get(v_toCold_1252_, 3);
v_currNamespace_1257_ = lean_ctor_get(v_toCold_1252_, 4);
v_openDecls_1258_ = lean_ctor_get(v_toCold_1252_, 5);
v_quotContext_1259_ = lean_ctor_get(v_toCold_1252_, 8);
v_currMacroScope_1260_ = lean_ctor_get(v_toCold_1252_, 9);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1261_, 0, v_env_1253_);
v___f_1262_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1262_, 0, v_env_1253_);
v___x_1263_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1248_);
lean_inc_n(v_currNamespace_1257_, 3);
v___f_1264_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1264_, 0, v_currNamespace_1257_);
lean_inc_n(v_openDecls_1258_, 2);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1265_, 0, v_env_1253_);
lean_closure_set(v___f_1265_, 1, v___x_1263_);
lean_closure_set(v___f_1265_, 2, v_currNamespace_1257_);
lean_closure_set(v___f_1265_, 3, v_openDecls_1258_);
v___f_1266_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1266_, 0, v_env_1253_);
lean_closure_set(v___f_1266_, 1, v_currNamespace_1257_);
lean_closure_set(v___f_1266_, 2, v_openDecls_1258_);
v_methods_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1267_, 0, v___f_1262_);
lean_ctor_set(v_methods_1267_, 1, v___f_1264_);
lean_ctor_set(v_methods_1267_, 2, v___f_1261_);
lean_ctor_set(v_methods_1267_, 3, v___f_1266_);
lean_ctor_set(v_methods_1267_, 4, v___f_1265_);
v___x_1268_ = lean_st_ref_get(v___y_1249_);
v_nextMacroScope_1269_ = lean_ctor_get(v___x_1268_, 1);
lean_inc(v_nextMacroScope_1269_);
lean_dec(v___x_1268_);
lean_inc(v_ref_1255_);
lean_inc(v_maxRecDepth_1256_);
lean_inc(v_currRecDepth_1254_);
lean_inc(v_currMacroScope_1260_);
lean_inc(v_quotContext_1259_);
v___x_1270_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1270_, 0, v_methods_1267_);
lean_ctor_set(v___x_1270_, 1, v_quotContext_1259_);
lean_ctor_set(v___x_1270_, 2, v_currMacroScope_1260_);
lean_ctor_set(v___x_1270_, 3, v_currRecDepth_1254_);
lean_ctor_set(v___x_1270_, 4, v_maxRecDepth_1256_);
lean_ctor_set(v___x_1270_, 5, v_ref_1255_);
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1272_, 0, v_nextMacroScope_1269_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
lean_ctor_set(v___x_1272_, 2, v___x_1271_);
v___x_1273_ = lean_apply_2(v_x_1243_, v___x_1270_, v___x_1272_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v_a_1275_; lean_object* v_macroScope_1276_; lean_object* v_traceMsgs_1277_; lean_object* v_expandedMacroDecls_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 1);
lean_inc(v_a_1274_);
v_a_1275_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1273_, 2);
v_macroScope_1276_ = lean_ctor_get(v_a_1274_, 0);
lean_inc(v_macroScope_1276_);
v_traceMsgs_1277_ = lean_ctor_get(v_a_1274_, 1);
lean_inc(v_traceMsgs_1277_);
v_expandedMacroDecls_1278_ = lean_ctor_get(v_a_1274_, 2);
lean_inc(v_expandedMacroDecls_1278_);
lean_dec(v_a_1274_);
v___x_1279_ = lean_box(0);
v___x_1280_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1278_, v___x_1279_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v_expandedMacroDecls_1278_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1281_; lean_object* v_env_1282_; lean_object* v_ngen_1283_; lean_object* v_auxDeclNGen_1284_; lean_object* v_traceState_1285_; lean_object* v_cache_1286_; lean_object* v_recordedDeps_1287_; lean_object* v_messages_1288_; lean_object* v_infoState_1289_; lean_object* v_snapshotTasks_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref_known(v___x_1280_, 1);
v___x_1281_ = lean_st_ref_take(v___y_1249_);
v_env_1282_ = lean_ctor_get(v___x_1281_, 0);
v_ngen_1283_ = lean_ctor_get(v___x_1281_, 2);
v_auxDeclNGen_1284_ = lean_ctor_get(v___x_1281_, 3);
v_traceState_1285_ = lean_ctor_get(v___x_1281_, 4);
v_cache_1286_ = lean_ctor_get(v___x_1281_, 5);
v_recordedDeps_1287_ = lean_ctor_get(v___x_1281_, 6);
v_messages_1288_ = lean_ctor_get(v___x_1281_, 7);
v_infoState_1289_ = lean_ctor_get(v___x_1281_, 8);
v_snapshotTasks_1290_ = lean_ctor_get(v___x_1281_, 9);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1281_, 1);
lean_dec(v_unused_1317_);
v___x_1292_ = v___x_1281_;
v_isShared_1293_ = v_isSharedCheck_1316_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_snapshotTasks_1290_);
lean_inc(v_infoState_1289_);
lean_inc(v_messages_1288_);
lean_inc(v_recordedDeps_1287_);
lean_inc(v_cache_1286_);
lean_inc(v_traceState_1285_);
lean_inc(v_auxDeclNGen_1284_);
lean_inc(v_ngen_1283_);
lean_inc(v_env_1282_);
lean_dec(v___x_1281_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1316_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v_macroScope_1276_);
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_env_1282_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_macroScope_1276_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_ngen_1283_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v_auxDeclNGen_1284_);
lean_ctor_set(v_reuseFailAlloc_1315_, 4, v_traceState_1285_);
lean_ctor_set(v_reuseFailAlloc_1315_, 5, v_cache_1286_);
lean_ctor_set(v_reuseFailAlloc_1315_, 6, v_recordedDeps_1287_);
lean_ctor_set(v_reuseFailAlloc_1315_, 7, v_messages_1288_);
lean_ctor_set(v_reuseFailAlloc_1315_, 8, v_infoState_1289_);
lean_ctor_set(v_reuseFailAlloc_1315_, 9, v_snapshotTasks_1290_);
v___x_1295_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_st_ref_put(v___y_1249_, v___x_1295_);
v___x_1297_ = l_List_reverse___redArg(v_traceMsgs_1277_);
v___x_1298_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1297_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v___x_1298_, 0);
lean_dec(v_unused_1306_);
v___x_1300_ = v___x_1298_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_dec(v___x_1298_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v_a_1275_);
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1275_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v_a_1275_);
v_a_1307_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1298_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1298_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v_traceMsgs_1277_);
lean_dec(v_macroScope_1276_);
lean_dec(v_a_1275_);
v_a_1318_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1280_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1280_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; 
v_a_1326_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1273_, 2);
if (lean_obj_tag(v_a_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v_a_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_a_1327_ = lean_ctor_get(v_a_1326_, 0);
lean_inc(v_a_1327_);
v_a_1328_ = lean_ctor_get(v_a_1326_, 1);
lean_inc_ref(v_a_1328_);
lean_dec_ref_known(v_a_1326_, 2);
v___x_1329_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1330_ = lean_string_dec_eq(v_a_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1328_);
v___x_1332_ = l_Lean_MessageData_ofFormat(v___x_1331_);
v___x_1333_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1327_, v___x_1332_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v_a_1327_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; 
lean_dec_ref(v_a_1328_);
v___x_1334_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1327_);
return v___x_1334_;
}
}
else
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_1335_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1243_ = stack[0].m_obj;
lean_object* v___y_1244_ = stack[1].m_obj;
lean_object* v___y_1245_ = stack[2].m_obj;
lean_object* v___y_1246_ = stack[3].m_obj;
lean_object* v___y_1247_ = stack[4].m_obj;
lean_object* v___y_1248_ = stack[5].m_obj;
lean_object* v___y_1249_ = stack[6].m_obj;
lean_object* v_res_1336_;
v_res_1336_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1345_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_bs_1351_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_bs_1351_);
return v___x_1353_;
}
else
{
lean_object* v_v_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_v_1354_ = lean_array_uget(v_bs_1351_, v_i_1350_);
v___x_1355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1354_);
v___x_1356_ = l_Lean_Syntax_isOfKind(v_v_1354_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; 
lean_dec(v_v_1354_);
lean_dec_ref(v_bs_1351_);
v___x_1357_ = lean_box(0);
return v___x_1357_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = l_Lean_Syntax_getArg(v_v_1354_, v___x_1358_);
v___x_1360_ = l_Lean_Syntax_isOfKind(v___x_1359_, v___x_1355_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_dec(v_v_1354_);
lean_dec_ref(v_bs_1351_);
v___x_1361_ = lean_box(0);
return v___x_1361_;
}
else
{
lean_object* v___x_1362_; lean_object* v_bs_x27_1363_; lean_object* v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1362_ = lean_unsigned_to_nat(3u);
v_bs_x27_1363_ = lean_array_uset(v_bs_1351_, v_i_1350_, v___x_1358_);
v___x_1364_ = l_Lean_Syntax_getArg(v_v_1354_, v___x_1362_);
lean_dec(v_v_1354_);
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_add(v_i_1350_, v___x_1365_);
v___x_1367_ = lean_array_uset(v_bs_x27_1363_, v_i_1350_, v___x_1364_);
v_i_1350_ = v___x_1366_;
v_bs_1351_ = v___x_1367_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1349_ = stack[0].m_num;
size_t v_i_1350_ = stack[1].m_num;
lean_object* v_bs_1351_ = stack[2].m_obj;
lean_object* v_res_1369_;
v_res_1369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_1349_, v_i_1350_, v_bs_1351_);
stack->m_obj
 = v_res_1369_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1370_, lean_object* v_i_1371_, lean_object* v_bs_1372_){
_start:
{
size_t v_sz_boxed_1373_; size_t v_i_boxed_1374_; lean_object* v_res_1375_; 
v_sz_boxed_1373_ = lean_unbox_usize(v_sz_1370_);
lean_dec(v_sz_1370_);
v_i_boxed_1374_ = lean_unbox_usize(v_i_1371_);
lean_dec(v_i_1371_);
v_res_1375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1373_, v_i_boxed_1374_, v_bs_1372_);
return v_res_1375_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(uint8_t v___x_1388_, size_t v_sz_1389_, size_t v_i_1390_, lean_object* v_bs_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_usize_dec_lt(v_i_1390_, v_sz_1389_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_bs_1391_);
return v___x_1393_;
}
else
{
lean_object* v_v_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_v_1394_ = lean_array_uget(v_bs_1391_, v_i_1390_);
v___x_1395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1394_);
v___x_1396_ = l_Lean_Syntax_isOfKind(v_v_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v_v_1394_);
lean_dec_ref(v_bs_1391_);
v___x_1397_ = lean_box(0);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_bs_x27_1400_; 
v___x_1398_ = lean_unsigned_to_nat(3u);
v___x_1399_ = lean_unsigned_to_nat(0u);
v_bs_x27_1400_ = lean_array_uset(v_bs_1391_, v_i_1390_, v___x_1399_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = l_Lean_Syntax_getArg(v_v_1394_, v___x_1407_);
v___x_1409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1410_ = l_Lean_Syntax_isOfKind(v___x_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_dec_ref(v_bs_x27_1400_);
lean_dec(v_v_1394_);
v___x_1411_ = lean_box(0);
return v___x_1411_;
}
else
{
goto v___jp_1401_;
}
}
else
{
goto v___jp_1401_;
}
v___jp_1401_:
{
lean_object* v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1402_ = l_Lean_Syntax_getArg(v_v_1394_, v___x_1398_);
lean_dec(v_v_1394_);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_add(v_i_1390_, v___x_1403_);
v___x_1405_ = lean_array_uset(v_bs_x27_1400_, v_i_1390_, v___x_1402_);
v_i_1390_ = v___x_1404_;
v_bs_1391_ = v___x_1405_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1388_ = stack[0].m_num;
size_t v_sz_1389_ = stack[1].m_num;
size_t v_i_1390_ = stack[2].m_num;
lean_object* v_bs_1391_ = stack[3].m_obj;
lean_object* v_res_1412_;
v_res_1412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_1388_, v_sz_1389_, v_i_1390_, v_bs_1391_);
stack->m_obj
 = v_res_1412_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v___x_1413_, lean_object* v_sz_1414_, lean_object* v_i_1415_, lean_object* v_bs_1416_){
_start:
{
uint8_t v___x_177915__boxed_1417_; size_t v_sz_boxed_1418_; size_t v_i_boxed_1419_; lean_object* v_res_1420_; 
v___x_177915__boxed_1417_ = lean_unbox(v___x_1413_);
v_sz_boxed_1418_ = lean_unbox_usize(v_sz_1414_);
lean_dec(v_sz_1414_);
v_i_boxed_1419_ = lean_unbox_usize(v_i_1415_);
lean_dec(v_i_1415_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_177915__boxed_1417_, v_sz_boxed_1418_, v_i_boxed_1419_, v_bs_1416_);
return v_res_1420_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1427_, size_t v_i_1428_, lean_object* v_bs_1429_){
_start:
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_usize_dec_lt(v_i_1428_, v_sz_1427_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_bs_1429_);
return v___x_1431_;
}
else
{
lean_object* v_v_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_v_1432_ = lean_array_uget(v_bs_1429_, v_i_1428_);
v___x_1433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1432_);
v___x_1434_ = l_Lean_Syntax_isOfKind(v_v_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
lean_dec(v_v_1432_);
lean_dec_ref(v_bs_1429_);
v___x_1435_ = lean_box(0);
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; lean_object* v_bs_x27_1437_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v_bs_x27_1437_ = lean_array_uset(v_bs_1429_, v_i_1428_, v___x_1436_);
v___x_1444_ = l_Lean_Syntax_getArg(v_v_1432_, v___x_1436_);
lean_dec(v_v_1432_);
v___x_1445_ = l_Lean_Syntax_isNone(v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = lean_unsigned_to_nat(2u);
v___x_1447_ = l_Lean_Syntax_matchesNull(v___x_1444_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
lean_dec_ref(v_bs_x27_1437_);
v___x_1448_ = lean_box(0);
return v___x_1448_;
}
else
{
goto v___jp_1438_;
}
}
else
{
lean_dec(v___x_1444_);
goto v___jp_1438_;
}
v___jp_1438_:
{
lean_object* v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; lean_object* v___x_1442_; 
v___x_1439_ = lean_box(0);
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_add(v_i_1428_, v___x_1440_);
v___x_1442_ = lean_array_uset(v_bs_x27_1437_, v_i_1428_, v___x_1439_);
v_i_1428_ = v___x_1441_;
v_bs_1429_ = v___x_1442_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1427_ = stack[0].m_num;
size_t v_i_1428_ = stack[1].m_num;
lean_object* v_bs_1429_ = stack[2].m_obj;
lean_object* v_res_1449_;
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_1427_, v_i_1428_, v_bs_1429_);
stack->m_obj
 = v_res_1449_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1450_, lean_object* v_i_1451_, lean_object* v_bs_1452_){
_start:
{
size_t v_sz_boxed_1453_; size_t v_i_boxed_1454_; lean_object* v_res_1455_; 
v_sz_boxed_1453_ = lean_unbox_usize(v_sz_1450_);
lean_dec(v_sz_1450_);
v_i_boxed_1454_ = lean_unbox_usize(v_i_1451_);
lean_dec(v_i_1451_);
v_res_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1453_, v_i_boxed_1454_, v_bs_1452_);
return v_res_1455_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1456_, size_t v_i_1457_, lean_object* v_bs_1458_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_usize_dec_lt(v_i_1457_, v_sz_1456_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_bs_1458_);
return v___x_1460_;
}
else
{
lean_object* v_v_1461_; lean_object* v___x_1462_; lean_object* v_bs_x27_1463_; size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; 
v_v_1461_ = lean_array_uget(v_bs_1458_, v_i_1457_);
v___x_1462_ = lean_unsigned_to_nat(0u);
v_bs_x27_1463_ = lean_array_uset(v_bs_1458_, v_i_1457_, v___x_1462_);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_add(v_i_1457_, v___x_1464_);
v___x_1466_ = lean_array_uset(v_bs_x27_1463_, v_i_1457_, v_v_1461_);
v_i_1457_ = v___x_1465_;
v_bs_1458_ = v___x_1466_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1456_ = stack[0].m_num;
size_t v_i_1457_ = stack[1].m_num;
lean_object* v_bs_1458_ = stack[2].m_obj;
lean_object* v_res_1468_;
v_res_1468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_1456_, v_i_1457_, v_bs_1458_);
stack->m_obj
 = v_res_1468_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1469_, lean_object* v_i_1470_, lean_object* v_bs_1471_){
_start:
{
size_t v_sz_boxed_1472_; size_t v_i_boxed_1473_; lean_object* v_res_1474_; 
v_sz_boxed_1472_ = lean_unbox_usize(v_sz_1469_);
lean_dec(v_sz_1469_);
v_i_boxed_1473_ = lean_unbox_usize(v_i_1470_);
lean_dec(v_i_1470_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1472_, v_i_boxed_1473_, v_bs_1471_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1475_, lean_object* v_x_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1476_, v___y_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1480_, v_x_1481_, v___y_1482_, v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec_ref(v_x_1481_);
return v_res_1484_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1488_, lean_object* v_as_x27_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
if (lean_obj_tag(v_as_x27_1489_) == 0)
{
lean_object* v___x_1498_; 
lean_dec(v_stx_1488_);
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_b_1490_);
return v___x_1498_;
}
else
{
lean_object* v_head_1499_; lean_object* v_tail_1500_; lean_object* v_value_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_b_1490_);
v_head_1499_ = lean_ctor_get(v_as_x27_1489_, 0);
v_tail_1500_ = lean_ctor_get(v_as_x27_1489_, 1);
v_value_1501_ = lean_ctor_get(v_head_1499_, 1);
v___x_1502_ = lean_box(0);
v___x_1503_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1504_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_value_1501_);
lean_inc(v___y_1496_);
lean_inc_ref(v___y_1495_);
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
lean_inc(v_stx_1488_);
v___x_1505_ = lean_apply_8(v_value_1501_, v_stx_1488_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, lean_box(0));
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_stx_1488_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_a_1506_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v___x_1502_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1536_; 
v_a_1516_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1518_ = v___x_1505_;
v_isShared_1519_ = v_isSharedCheck_1536_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1505_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1536_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint8_t v___y_1521_; uint8_t v___x_1534_; 
v___x_1534_ = l_Lean_Exception_isInterrupt(v_a_1516_);
if (v___x_1534_ == 0)
{
uint8_t v___x_1535_; 
lean_inc(v_a_1516_);
v___x_1535_ = l_Lean_Exception_isRuntime(v_a_1516_);
v___y_1521_ = v___x_1535_;
goto v___jp_1520_;
}
else
{
v___y_1521_ = v___x_1534_;
goto v___jp_1520_;
}
v___jp_1520_:
{
if (v___y_1521_ == 0)
{
if (lean_obj_tag(v_a_1516_) == 0)
{
lean_object* v___x_1523_; 
lean_dec(v_stx_1488_);
if (v_isShared_1519_ == 0)
{
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1516_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
else
{
lean_object* v_id_1525_; uint8_t v___x_1526_; 
v_id_1525_ = lean_ctor_get(v_a_1516_, 0);
v___x_1526_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1504_, v_id_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1528_; 
lean_dec(v_stx_1488_);
if (v_isShared_1519_ == 0)
{
v___x_1528_ = v___x_1518_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1516_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
else
{
lean_dec_ref_known(v_a_1516_, 2);
lean_del_object(v___x_1518_);
v_as_x27_1489_ = v_tail_1500_;
v_b_1490_ = v___x_1503_;
goto _start;
}
}
}
else
{
lean_object* v___x_1532_; 
lean_dec(v_stx_1488_);
if (v_isShared_1519_ == 0)
{
v___x_1532_ = v___x_1518_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1516_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1488_ = stack[0].m_obj;
lean_object* v_as_x27_1489_ = stack[1].m_obj;
lean_object* v_b_1490_ = stack[2].m_obj;
lean_object* v___y_1491_ = stack[3].m_obj;
lean_object* v___y_1492_ = stack[4].m_obj;
lean_object* v___y_1493_ = stack[5].m_obj;
lean_object* v___y_1494_ = stack[6].m_obj;
lean_object* v___y_1495_ = stack[7].m_obj;
lean_object* v___y_1496_ = stack[8].m_obj;
lean_object* v_res_1537_;
v_res_1537_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1488_, v_as_x27_1489_, v_b_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
stack->m_obj
 = v_res_1537_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1538_, lean_object* v_as_x27_1539_, lean_object* v_b_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1538_, v_as_x27_1539_, v_b_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_as_x27_1539_);
return v_res_1548_;
}
}
lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1551_, lean_object* v_rhs_x3f_1552_, lean_object* v_otherwise_x3f_1553_, lean_object* v_body_x3f_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v___y_1563_; uint8_t v___y_1564_; uint8_t v___y_1565_; uint8_t v___y_1566_; uint8_t v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v_body_1574_; lean_object* v___y_1595_; lean_object* v_otherwise_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v_rhs_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; 
if (lean_obj_tag(v_rhs_x3f_1552_) == 0)
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1608_ = v___x_1619_;
v___y_1609_ = v_a_1555_;
v___y_1610_ = v_a_1556_;
v___y_1611_ = v_a_1557_;
v___y_1612_ = v_a_1558_;
v___y_1613_ = v_a_1559_;
v___y_1614_ = v_a_1560_;
goto v___jp_1607_;
}
else
{
lean_object* v_val_1620_; lean_object* v___x_1621_; 
v_val_1620_ = lean_ctor_get(v_rhs_x3f_1552_, 0);
lean_inc(v_val_1620_);
lean_dec_ref_known(v_rhs_x3f_1552_, 1);
v___x_1621_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1620_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v_rhs_1608_ = v_a_1622_;
v___y_1609_ = v_a_1555_;
v___y_1610_ = v_a_1556_;
v___y_1611_ = v_a_1557_;
v___y_1612_ = v_a_1558_;
v___y_1613_ = v_a_1559_;
v___y_1614_ = v_a_1560_;
goto v___jp_1607_;
}
else
{
lean_dec(v_body_x3f_1554_);
lean_dec(v_otherwise_x3f_1553_);
lean_dec_ref(v_reassigned_1551_);
return v___x_1621_;
}
}
v___jp_1562_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1569_, 0, v___y_1563_);
lean_ctor_set(v___x_1569_, 1, v___y_1568_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*2, v___y_1564_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*2 + 1, v___y_1567_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*2 + 2, v___y_1566_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*2 + 3, v___y_1565_);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
v___jp_1571_:
{
lean_object* v___x_1575_; lean_object* v_info_1576_; uint8_t v_breaks_1577_; uint8_t v_continues_1578_; uint8_t v_returnsEarly_1579_; lean_object* v_numRegularExits_1580_; uint8_t v_noFallthrough_1581_; lean_object* v_reassigns_1582_; size_t v_sz_1583_; size_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1575_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1574_, v___y_1573_);
v_info_1576_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1572_, v___x_1575_);
v_breaks_1577_ = lean_ctor_get_uint8(v_info_1576_, sizeof(void*)*2);
v_continues_1578_ = lean_ctor_get_uint8(v_info_1576_, sizeof(void*)*2 + 1);
v_returnsEarly_1579_ = lean_ctor_get_uint8(v_info_1576_, sizeof(void*)*2 + 2);
v_numRegularExits_1580_ = lean_ctor_get(v_info_1576_, 0);
lean_inc(v_numRegularExits_1580_);
v_noFallthrough_1581_ = lean_ctor_get_uint8(v_info_1576_, sizeof(void*)*2 + 3);
v_reassigns_1582_ = lean_ctor_get(v_info_1576_, 1);
lean_inc(v_reassigns_1582_);
lean_dec_ref(v_info_1576_);
v_sz_1583_ = lean_array_size(v_reassigned_1551_);
v___x_1584_ = ((size_t)0ULL);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1583_, v___x_1584_, v_reassigned_1551_);
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = lean_array_get_size(v___x_1585_);
v___x_1588_ = lean_nat_dec_lt(v___x_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_dec_ref(v___x_1585_);
v___y_1563_ = v_numRegularExits_1580_;
v___y_1564_ = v_breaks_1577_;
v___y_1565_ = v_noFallthrough_1581_;
v___y_1566_ = v_returnsEarly_1579_;
v___y_1567_ = v_continues_1578_;
v___y_1568_ = v_reassigns_1582_;
goto v___jp_1562_;
}
else
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_nat_dec_le(v___x_1587_, v___x_1587_);
if (v___x_1589_ == 0)
{
if (v___x_1588_ == 0)
{
lean_dec_ref(v___x_1585_);
v___y_1563_ = v_numRegularExits_1580_;
v___y_1564_ = v_breaks_1577_;
v___y_1565_ = v_noFallthrough_1581_;
v___y_1566_ = v_returnsEarly_1579_;
v___y_1567_ = v_continues_1578_;
v___y_1568_ = v_reassigns_1582_;
goto v___jp_1562_;
}
else
{
size_t v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_usize_of_nat(v___x_1587_);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1585_, v___x_1584_, v___x_1590_, v_reassigns_1582_);
lean_dec_ref(v___x_1585_);
v___y_1563_ = v_numRegularExits_1580_;
v___y_1564_ = v_breaks_1577_;
v___y_1565_ = v_noFallthrough_1581_;
v___y_1566_ = v_returnsEarly_1579_;
v___y_1567_ = v_continues_1578_;
v___y_1568_ = v___x_1591_;
goto v___jp_1562_;
}
}
else
{
size_t v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_usize_of_nat(v___x_1587_);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1585_, v___x_1584_, v___x_1592_, v_reassigns_1582_);
lean_dec_ref(v___x_1585_);
v___y_1563_ = v_numRegularExits_1580_;
v___y_1564_ = v_breaks_1577_;
v___y_1565_ = v_noFallthrough_1581_;
v___y_1566_ = v_returnsEarly_1579_;
v___y_1567_ = v_continues_1578_;
v___y_1568_ = v___x_1593_;
goto v___jp_1562_;
}
}
}
v___jp_1594_:
{
if (lean_obj_tag(v_body_x3f_1554_) == 0)
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1572_ = v___y_1595_;
v___y_1573_ = v_otherwise_1596_;
v_body_1574_ = v___x_1603_;
goto v___jp_1571_;
}
else
{
lean_object* v_val_1604_; lean_object* v___x_1605_; 
v_val_1604_ = lean_ctor_get(v_body_x3f_1554_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v_body_x3f_1554_, 1);
v___x_1605_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1604_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v___y_1572_ = v___y_1595_;
v___y_1573_ = v_otherwise_1596_;
v_body_1574_ = v_a_1606_;
goto v___jp_1571_;
}
else
{
lean_dec_ref(v_otherwise_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v_reassigned_1551_);
return v___x_1605_;
}
}
}
v___jp_1607_:
{
if (lean_obj_tag(v_otherwise_x3f_1553_) == 0)
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1595_ = v_rhs_1608_;
v_otherwise_1596_ = v___x_1615_;
v___y_1597_ = v___y_1609_;
v___y_1598_ = v___y_1610_;
v___y_1599_ = v___y_1611_;
v___y_1600_ = v___y_1612_;
v___y_1601_ = v___y_1613_;
v___y_1602_ = v___y_1614_;
goto v___jp_1594_;
}
else
{
lean_object* v_val_1616_; lean_object* v___x_1617_; 
v_val_1616_ = lean_ctor_get(v_otherwise_x3f_1553_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v_otherwise_x3f_1553_, 1);
v___x_1617_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1616_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___y_1595_ = v_rhs_1608_;
v_otherwise_1596_ = v_a_1618_;
v___y_1597_ = v___y_1609_;
v___y_1598_ = v___y_1610_;
v___y_1599_ = v___y_1611_;
v___y_1600_ = v___y_1612_;
v___y_1601_ = v___y_1613_;
v___y_1602_ = v___y_1614_;
goto v___jp_1594_;
}
else
{
lean_dec_ref(v_rhs_1608_);
lean_dec(v_body_x3f_1554_);
lean_dec_ref(v_reassigned_1551_);
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign_0interp(lean_interpreter_value* stack)
{
lean_object* v_reassigned_1551_ = stack[0].m_obj;
lean_object* v_rhs_x3f_1552_ = stack[1].m_obj;
lean_object* v_otherwise_x3f_1553_ = stack[2].m_obj;
lean_object* v_body_x3f_1554_ = stack[3].m_obj;
lean_object* v_a_1555_ = stack[4].m_obj;
lean_object* v_a_1556_ = stack[5].m_obj;
lean_object* v_a_1557_ = stack[6].m_obj;
lean_object* v_a_1558_ = stack[7].m_obj;
lean_object* v_a_1559_ = stack[8].m_obj;
lean_object* v_a_1560_ = stack[9].m_obj;
lean_object* v_res_1623_;
v_res_1623_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_1551_, v_rhs_x3f_1552_, v_otherwise_x3f_1553_, v_body_x3f_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
stack->m_obj
 = v_res_1623_;
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12));
v___x_1662_ = l_Lean_stringToMessageData(v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14));
v___x_1665_ = l_Lean_stringToMessageData(v___x_1664_);
return v___x_1665_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16));
v___x_1668_ = l_Lean_stringToMessageData(v___x_1667_);
return v___x_1668_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18));
v___x_1671_ = l_Lean_stringToMessageData(v___x_1670_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
return v___x_1716_;
}
}
lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1726_, lean_object* v_decl_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v_reassigns_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1727_);
v___x_1764_ = l_Lean_Syntax_isOfKind(v_decl_1727_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1727_);
v___x_1766_ = l_Lean_Syntax_isOfKind(v_decl_1727_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1767_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1768_ = lean_box(0);
v___x_1769_ = l_Lean_Syntax_formatStx(v_decl_1727_, v___x_1768_, v___x_1766_);
v___x_1770_ = l_Std_Format_defWidth;
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = l_Std_Format_pretty(v___x_1769_, v___x_1770_, v___x_1771_, v___x_1771_);
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1767_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1774_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; lean_object* v_pattern_1777_; lean_object* v___y_1779_; lean_object* v_otherwise_x3f_1780_; lean_object* v_body_x3f_x3f_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v_body_x3f_x3f_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___x_1811_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1776_ = lean_unsigned_to_nat(0u);
v_pattern_1777_ = l_Lean_Syntax_getArg(v_decl_1727_, v___x_1776_);
v___x_1811_ = lean_unsigned_to_nat(1u);
v___x_1850_ = l_Lean_Syntax_getArg(v_decl_1727_, v___x_1811_);
v___x_1851_ = l_Lean_Syntax_isNone(v___x_1850_);
if (v___x_1851_ == 0)
{
uint8_t v___x_1852_; 
lean_inc(v___x_1850_);
v___x_1852_ = l_Lean_Syntax_matchesNull(v___x_1850_, v___x_1811_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec(v___x_1850_);
lean_dec(v_pattern_1777_);
v___x_1853_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1854_ = lean_box(0);
v___x_1855_ = l_Lean_Syntax_formatStx(v_decl_1727_, v___x_1854_, v___x_1852_);
v___x_1856_ = l_Std_Format_defWidth;
v___x_1857_ = l_Std_Format_pretty(v___x_1855_, v___x_1856_, v___x_1776_, v___x_1776_);
v___x_1858_ = l_Lean_stringToMessageData(v___x_1857_);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1853_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1859_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1861_ = l_Lean_Syntax_getArg(v___x_1850_, v___x_1776_);
lean_dec(v___x_1850_);
v___x_1862_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1863_ = l_Lean_Syntax_isOfKind(v___x_1861_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec(v_pattern_1777_);
v___x_1864_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1865_ = lean_box(0);
v___x_1866_ = l_Lean_Syntax_formatStx(v_decl_1727_, v___x_1865_, v___x_1863_);
v___x_1867_ = l_Std_Format_defWidth;
v___x_1868_ = l_Std_Format_pretty(v___x_1866_, v___x_1867_, v___x_1776_, v___x_1776_);
v___x_1869_ = l_Lean_stringToMessageData(v___x_1868_);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1864_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1870_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1871_;
}
else
{
v___y_1813_ = v_a_1728_;
v___y_1814_ = v_a_1729_;
v___y_1815_ = v_a_1730_;
v___y_1816_ = v_a_1731_;
v___y_1817_ = v_a_1732_;
v___y_1818_ = v_a_1733_;
goto v___jp_1812_;
}
}
}
else
{
lean_dec(v___x_1850_);
v___y_1813_ = v_a_1728_;
v___y_1814_ = v_a_1729_;
v___y_1815_ = v_a_1730_;
v___y_1816_ = v_a_1731_;
v___y_1817_ = v_a_1732_;
v___y_1818_ = v_a_1733_;
goto v___jp_1812_;
}
v___jp_1778_:
{
if (v_reassignment_1726_ == 0)
{
lean_object* v___x_1788_; 
lean_dec(v_pattern_1777_);
v___x_1788_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1748_ = v_otherwise_x3f_1780_;
v___y_1749_ = v_body_x3f_x3f_1781_;
v___y_1750_ = v___y_1779_;
v_reassigns_1751_ = v___x_1788_;
v___y_1752_ = v___y_1782_;
v___y_1753_ = v___y_1783_;
v___y_1754_ = v___y_1784_;
v___y_1755_ = v___y_1785_;
v___y_1756_ = v___y_1786_;
v___y_1757_ = v___y_1787_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1777_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1789_, 1);
v___y_1748_ = v_otherwise_x3f_1780_;
v___y_1749_ = v_body_x3f_x3f_1781_;
v___y_1750_ = v___y_1779_;
v_reassigns_1751_ = v_a_1790_;
v___y_1752_ = v___y_1782_;
v___y_1753_ = v___y_1783_;
v___y_1754_ = v___y_1784_;
v___y_1755_ = v___y_1785_;
v___y_1756_ = v___y_1786_;
v___y_1757_ = v___y_1787_;
goto v___jp_1747_;
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_body_x3f_x3f_1781_);
lean_dec(v_otherwise_x3f_1780_);
lean_dec(v___y_1779_);
v_a_1791_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1789_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1789_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
v___jp_1799_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___y_1800_);
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_body_x3f_x3f_1802_);
v___y_1779_ = v___y_1801_;
v_otherwise_x3f_1780_ = v___x_1809_;
v_body_x3f_x3f_1781_ = v___x_1810_;
v___y_1782_ = v___y_1803_;
v___y_1783_ = v___y_1804_;
v___y_1784_ = v___y_1805_;
v___y_1785_ = v___y_1806_;
v___y_1786_ = v___y_1807_;
v___y_1787_ = v___y_1808_;
goto v___jp_1778_;
}
v___jp_1812_:
{
lean_object* v___x_1819_; lean_object* v_rhs_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1819_ = lean_unsigned_to_nat(3u);
v_rhs_1820_ = l_Lean_Syntax_getArg(v_decl_1727_, v___x_1819_);
v___x_1821_ = lean_unsigned_to_nat(4u);
v___x_1822_ = l_Lean_Syntax_getArg(v_decl_1727_, v___x_1821_);
v___x_1823_ = l_Lean_Syntax_isNone(v___x_1822_);
if (v___x_1823_ == 0)
{
uint8_t v___x_1824_; 
lean_inc(v___x_1822_);
v___x_1824_ = l_Lean_Syntax_matchesNull(v___x_1822_, v___x_1819_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v___x_1822_);
lean_dec(v_rhs_1820_);
lean_dec(v_pattern_1777_);
v___x_1825_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1826_ = lean_box(0);
v___x_1827_ = l_Lean_Syntax_formatStx(v_decl_1727_, v___x_1826_, v___x_1824_);
v___x_1828_ = l_Std_Format_defWidth;
v___x_1829_ = l_Std_Format_pretty(v___x_1827_, v___x_1828_, v___x_1776_, v___x_1776_);
v___x_1830_ = l_Lean_stringToMessageData(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1825_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1831_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; lean_object* v_otherwise_x3f_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1833_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1834_ = l_Lean_Syntax_getArg(v___x_1822_, v___x_1811_);
v___x_1835_ = l_Lean_Syntax_getArg(v___x_1822_, v___x_1833_);
lean_dec(v___x_1822_);
v___x_1836_ = l_Lean_Syntax_isNone(v___x_1835_);
if (v___x_1836_ == 0)
{
uint8_t v___x_1837_; 
lean_inc(v___x_1835_);
v___x_1837_ = l_Lean_Syntax_matchesNull(v___x_1835_, v___x_1811_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v___x_1835_);
lean_dec(v_otherwise_x3f_1834_);
lean_dec(v_rhs_1820_);
lean_dec(v_pattern_1777_);
v___x_1838_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1839_ = lean_box(0);
v___x_1840_ = l_Lean_Syntax_formatStx(v_decl_1727_, v___x_1839_, v___x_1837_);
v___x_1841_ = l_Std_Format_defWidth;
v___x_1842_ = l_Std_Format_pretty(v___x_1840_, v___x_1841_, v___x_1776_, v___x_1776_);
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1838_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1844_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
return v___x_1845_;
}
else
{
lean_object* v_body_x3f_x3f_1846_; lean_object* v___x_1847_; 
lean_dec(v_decl_1727_);
v_body_x3f_x3f_1846_ = l_Lean_Syntax_getArg(v___x_1835_, v___x_1776_);
lean_dec(v___x_1835_);
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_body_x3f_x3f_1846_);
v___y_1800_ = v_otherwise_x3f_1834_;
v___y_1801_ = v_rhs_1820_;
v_body_x3f_x3f_1802_ = v___x_1847_;
v___y_1803_ = v___y_1813_;
v___y_1804_ = v___y_1814_;
v___y_1805_ = v___y_1815_;
v___y_1806_ = v___y_1816_;
v___y_1807_ = v___y_1817_;
v___y_1808_ = v___y_1818_;
goto v___jp_1799_;
}
}
else
{
lean_object* v___x_1848_; 
lean_dec(v___x_1835_);
lean_dec(v_decl_1727_);
v___x_1848_ = lean_box(0);
v___y_1800_ = v_otherwise_x3f_1834_;
v___y_1801_ = v_rhs_1820_;
v_body_x3f_x3f_1802_ = v___x_1848_;
v___y_1803_ = v___y_1813_;
v___y_1804_ = v___y_1814_;
v___y_1805_ = v___y_1815_;
v___y_1806_ = v___y_1816_;
v___y_1807_ = v___y_1817_;
v___y_1808_ = v___y_1818_;
goto v___jp_1799_;
}
}
}
else
{
lean_object* v___x_1849_; 
lean_dec(v___x_1822_);
lean_dec(v_decl_1727_);
v___x_1849_ = lean_box(0);
v___y_1779_ = v_rhs_1820_;
v_otherwise_x3f_1780_ = v___x_1849_;
v_body_x3f_x3f_1781_ = v___x_1849_;
v___y_1782_ = v___y_1813_;
v___y_1783_ = v___y_1814_;
v___y_1784_ = v___y_1815_;
v___y_1785_ = v___y_1816_;
v___y_1786_ = v___y_1817_;
v___y_1787_ = v___y_1818_;
goto v___jp_1778_;
}
}
}
}
else
{
lean_object* v___x_1872_; lean_object* v_x_1873_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1872_ = lean_unsigned_to_nat(0u);
v_x_1873_ = l_Lean_Syntax_getArg(v_decl_1727_, v___x_1872_);
v___x_1887_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1873_);
v___x_1888_ = l_Lean_Syntax_isOfKind(v_x_1873_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_x_1873_);
v___x_1889_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1890_ = lean_box(0);
v___x_1891_ = l_Lean_Syntax_formatStx(v_decl_1727_, v___x_1890_, v___x_1888_);
v___x_1892_ = l_Std_Format_defWidth;
v___x_1893_ = l_Std_Format_pretty(v___x_1891_, v___x_1892_, v___x_1872_, v___x_1872_);
v___x_1894_ = l_Lean_stringToMessageData(v___x_1893_);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1889_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1895_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = l_Lean_Syntax_getArg(v_decl_1727_, v___x_1897_);
v___x_1899_ = l_Lean_Syntax_isNone(v___x_1898_);
if (v___x_1899_ == 0)
{
uint8_t v___x_1900_; 
lean_inc(v___x_1898_);
v___x_1900_ = l_Lean_Syntax_matchesNull(v___x_1898_, v___x_1897_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
lean_dec(v___x_1898_);
lean_dec(v_x_1873_);
v___x_1901_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1902_ = lean_box(0);
v___x_1903_ = l_Lean_Syntax_formatStx(v_decl_1727_, v___x_1902_, v___x_1900_);
v___x_1904_ = l_Std_Format_defWidth;
v___x_1905_ = l_Std_Format_pretty(v___x_1903_, v___x_1904_, v___x_1872_, v___x_1872_);
v___x_1906_ = l_Lean_stringToMessageData(v___x_1905_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1901_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1907_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1908_;
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1909_ = l_Lean_Syntax_getArg(v___x_1898_, v___x_1872_);
lean_dec(v___x_1898_);
v___x_1910_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1911_ = l_Lean_Syntax_isOfKind(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec(v_x_1873_);
v___x_1912_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1913_ = lean_box(0);
v___x_1914_ = l_Lean_Syntax_formatStx(v_decl_1727_, v___x_1913_, v___x_1911_);
v___x_1915_ = l_Std_Format_defWidth;
v___x_1916_ = l_Std_Format_pretty(v___x_1914_, v___x_1915_, v___x_1872_, v___x_1872_);
v___x_1917_ = l_Lean_stringToMessageData(v___x_1916_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1912_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1918_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1919_;
}
else
{
v___y_1875_ = v_a_1728_;
v___y_1876_ = v_a_1729_;
v___y_1877_ = v_a_1730_;
v___y_1878_ = v_a_1731_;
v___y_1879_ = v_a_1732_;
v___y_1880_ = v_a_1733_;
goto v___jp_1874_;
}
}
}
else
{
lean_dec(v___x_1898_);
v___y_1875_ = v_a_1728_;
v___y_1876_ = v_a_1729_;
v___y_1877_ = v_a_1730_;
v___y_1878_ = v_a_1731_;
v___y_1879_ = v_a_1732_;
v___y_1880_ = v_a_1733_;
goto v___jp_1874_;
}
}
v___jp_1874_:
{
lean_object* v___x_1881_; lean_object* v_rhs_1882_; 
v___x_1881_ = lean_unsigned_to_nat(3u);
v_rhs_1882_ = l_Lean_Syntax_getArg(v_decl_1727_, v___x_1881_);
lean_dec(v_decl_1727_);
if (v_reassignment_1726_ == 0)
{
lean_object* v___x_1883_; 
lean_dec(v_x_1873_);
v___x_1883_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1736_ = v___y_1879_;
v___y_1737_ = v___y_1875_;
v___y_1738_ = v___y_1880_;
v___y_1739_ = v___y_1878_;
v___y_1740_ = v___y_1877_;
v___y_1741_ = v___y_1876_;
v___y_1742_ = v_rhs_1882_;
v___y_1743_ = v___x_1883_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_unsigned_to_nat(1u);
v___x_1885_ = lean_mk_empty_array_with_capacity(v___x_1884_);
v___x_1886_ = lean_array_push(v___x_1885_, v_x_1873_);
v___y_1736_ = v___y_1879_;
v___y_1737_ = v___y_1875_;
v___y_1738_ = v___y_1880_;
v___y_1739_ = v___y_1878_;
v___y_1740_ = v___y_1877_;
v___y_1741_ = v___y_1876_;
v___y_1742_ = v_rhs_1882_;
v___y_1743_ = v___x_1886_;
goto v___jp_1735_;
}
}
}
v___jp_1735_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___y_1742_);
v___x_1745_ = lean_box(0);
v___x_1746_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1743_, v___x_1744_, v___x_1745_, v___x_1745_, v___y_1737_, v___y_1741_, v___y_1740_, v___y_1739_, v___y_1736_, v___y_1738_);
return v___x_1746_;
}
v___jp_1747_:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___y_1750_);
if (lean_obj_tag(v___y_1749_) == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_box(0);
v___x_1760_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1751_, v___x_1758_, v___y_1748_, v___x_1759_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
return v___x_1760_;
}
else
{
lean_object* v_val_1761_; lean_object* v___x_1762_; 
v_val_1761_ = lean_ctor_get(v___y_1749_, 0);
lean_inc(v_val_1761_);
lean_dec_ref_known(v___y_1749_, 1);
v___x_1762_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1751_, v___x_1758_, v___y_1748_, v_val_1761_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
return v___x_1762_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow_0interp(lean_interpreter_value* stack)
{
uint8_t v_reassignment_1726_ = stack[0].m_num;
lean_object* v_decl_1727_ = stack[1].m_obj;
lean_object* v_a_1728_ = stack[2].m_obj;
lean_object* v_a_1729_ = stack[3].m_obj;
lean_object* v_a_1730_ = stack[4].m_obj;
lean_object* v_a_1731_ = stack[5].m_obj;
lean_object* v_a_1732_ = stack[6].m_obj;
lean_object* v_a_1733_ = stack[7].m_obj;
lean_object* v_res_1920_;
v_res_1920_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_1726_, v_decl_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
stack->m_obj
 = v_res_1920_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_2046_, size_t v_sz_2047_, size_t v_i_2048_, lean_object* v_b_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
uint8_t v___x_2057_; 
v___x_2057_ = lean_usize_dec_lt(v_i_2048_, v_sz_2047_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_b_2049_);
return v___x_2058_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2060_; 
v_a_2059_ = lean_array_uget_borrowed(v_as_2046_, v_i_2048_);
lean_inc(v_a_2059_);
v___x_2060_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_2059_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; size_t v___x_2063_; size_t v___x_2064_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2061_, v_b_2049_);
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_add(v_i_2048_, v___x_2063_);
v_i_2048_ = v___x_2064_;
v_b_2049_ = v___x_2062_;
goto _start;
}
else
{
lean_dec_ref(v_b_2049_);
return v___x_2060_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2046_ = stack[0].m_obj;
size_t v_sz_2047_ = stack[1].m_num;
size_t v_i_2048_ = stack[2].m_num;
lean_object* v_b_2049_ = stack[3].m_obj;
lean_object* v___y_2050_ = stack[4].m_obj;
lean_object* v___y_2051_ = stack[5].m_obj;
lean_object* v___y_2052_ = stack[6].m_obj;
lean_object* v___y_2053_ = stack[7].m_obj;
lean_object* v___y_2054_ = stack[8].m_obj;
lean_object* v___y_2055_ = stack[9].m_obj;
lean_object* v_res_2066_;
v_res_2066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_2046_, v_sz_2047_, v_i_2048_, v_b_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
stack->m_obj
 = v_res_2066_;
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2081_ = l_Lean_stringToMessageData(v___x_2080_);
return v___x_2081_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2096_, lean_object* v_as_2097_, size_t v_sz_2098_, size_t v_i_2099_, lean_object* v_b_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_a_2109_; uint8_t v___x_2113_; 
v___x_2113_ = lean_usize_dec_lt(v_i_2099_, v_sz_2098_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_b_2100_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; lean_object* v_a_2116_; uint8_t v___x_2117_; 
v___x_2115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2116_ = lean_array_uget_borrowed(v_as_2097_, v_i_2099_);
lean_inc(v_a_2116_);
v___x_2117_ = l_Lean_Syntax_isOfKind(v_a_2116_, v___x_2115_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_dec_ref_known(v___x_2118_, 1);
v_a_2109_ = v_b_2100_;
goto v___jp_2108_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v_b_2100_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v___x_2127_; lean_object* v___y_2129_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2127_ = lean_unsigned_to_nat(3u);
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = l_Lean_Syntax_getArg(v_a_2116_, v___x_2146_);
v___x_2148_ = l_Lean_Syntax_getArgs(v___x_2147_);
lean_dec(v___x_2147_);
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2151_ = lean_array_get_size(v___x_2148_);
v___x_2152_ = lean_nat_dec_lt(v___x_2149_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_dec_ref(v___x_2148_);
v___y_2129_ = v___x_2150_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; size_t v___x_2155_; size_t v___x_2156_; lean_object* v___x_2157_; lean_object* v_snd_2158_; 
v___x_2153_ = lean_box(v___x_2152_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
lean_ctor_set(v___x_2154_, 1, v___x_2150_);
v___x_2155_ = ((size_t)0ULL);
v___x_2156_ = lean_usize_of_nat(v___x_2151_);
v___x_2157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2117_, v___x_2096_, v___x_2148_, v___x_2155_, v___x_2156_, v___x_2154_);
lean_dec_ref(v___x_2148_);
v_snd_2158_ = lean_ctor_get(v___x_2157_, 1);
lean_inc(v_snd_2158_);
lean_dec_ref(v___x_2157_);
v___y_2129_ = v_snd_2158_;
goto v___jp_2128_;
}
v___jp_2128_:
{
size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v_sz_2130_ = lean_array_size(v___y_2129_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2130_, v___x_2131_, v___y_2129_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_dec_ref_known(v___x_2133_, 1);
v_a_2109_ = v_b_2100_;
goto v___jp_2108_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_b_2100_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref_known(v___x_2132_, 1);
v___x_2142_ = l_Lean_Syntax_getArg(v_a_2116_, v___x_2127_);
v___x_2143_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2142_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2100_, v_a_2144_);
v_a_2109_ = v___x_2145_;
goto v___jp_2108_;
}
else
{
lean_dec_ref(v_b_2100_);
return v___x_2143_;
}
}
}
}
}
v___jp_2108_:
{
size_t v___x_2110_; size_t v___x_2111_; 
v___x_2110_ = ((size_t)1ULL);
v___x_2111_ = lean_usize_add(v_i_2099_, v___x_2110_);
v_i_2099_ = v___x_2111_;
v_b_2100_ = v_a_2109_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2096_ = stack[0].m_num;
lean_object* v_as_2097_ = stack[1].m_obj;
size_t v_sz_2098_ = stack[2].m_num;
size_t v_i_2099_ = stack[3].m_num;
lean_object* v_b_2100_ = stack[4].m_obj;
lean_object* v___y_2101_ = stack[5].m_obj;
lean_object* v___y_2102_ = stack[6].m_obj;
lean_object* v___y_2103_ = stack[7].m_obj;
lean_object* v___y_2104_ = stack[8].m_obj;
lean_object* v___y_2105_ = stack[9].m_obj;
lean_object* v___y_2106_ = stack[10].m_obj;
lean_object* v_res_2159_;
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2096_, v_as_2097_, v_sz_2098_, v_i_2099_, v_b_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
stack->m_obj
 = v_res_2159_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2160_, size_t v_sz_2161_, size_t v_i_2162_, lean_object* v_b_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_a_2172_; uint8_t v___x_2176_; 
v___x_2176_ = lean_usize_dec_lt(v_i_2162_, v_sz_2161_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_b_2163_);
return v___x_2177_;
}
else
{
lean_object* v___x_2178_; lean_object* v_a_2179_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2178_ = lean_unsigned_to_nat(0u);
v_a_2179_ = lean_array_uget_borrowed(v_as_2160_, v_i_2162_);
v___x_2192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2179_);
v___x_2193_ = l_Lean_Syntax_isOfKind(v_a_2179_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2179_);
v___x_2195_ = l_Lean_Syntax_isOfKind(v_a_2179_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2196_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2197_ = lean_box(0);
lean_inc(v_a_2179_);
v___x_2198_ = l_Lean_Syntax_formatStx(v_a_2179_, v___x_2197_, v___x_2195_);
v___x_2199_ = l_Std_Format_defWidth;
v___x_2200_ = l_Std_Format_pretty(v___x_2198_, v___x_2199_, v___x_2178_, v___x_2178_);
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2196_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2202_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_dec_ref_known(v___x_2203_, 1);
v_a_2172_ = v_b_2163_;
goto v___jp_2171_;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref(v_b_2163_);
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2212_ = lean_unsigned_to_nat(1u);
v___x_2213_ = l_Lean_Syntax_getArg(v_a_2179_, v___x_2212_);
v___x_2214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2213_);
v___x_2215_ = l_Lean_Syntax_isOfKind(v___x_2213_, v___x_2214_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec(v___x_2213_);
v___x_2216_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2217_ = lean_box(0);
lean_inc(v_a_2179_);
v___x_2218_ = l_Lean_Syntax_formatStx(v_a_2179_, v___x_2217_, v___x_2215_);
v___x_2219_ = l_Std_Format_defWidth;
v___x_2220_ = l_Std_Format_pretty(v___x_2218_, v___x_2219_, v___x_2178_, v___x_2178_);
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2216_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2222_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_dec_ref_known(v___x_2223_, 1);
v_a_2172_ = v_b_2163_;
goto v___jp_2171_;
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec_ref(v_b_2163_);
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2223_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; size_t v_sz_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2232_ = l_Lean_Syntax_getArg(v___x_2213_, v___x_2178_);
lean_dec(v___x_2213_);
v___x_2233_ = l_Lean_Syntax_getArgs(v___x_2232_);
lean_dec(v___x_2232_);
v_sz_2234_ = lean_array_size(v___x_2233_);
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2193_, v___x_2233_, v_sz_2234_, v___x_2235_, v_b_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec_ref(v___x_2233_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v_a_2172_ = v_a_2237_;
goto v___jp_2171_;
}
else
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2238_ = lean_unsigned_to_nat(2u);
v___x_2239_ = l_Lean_Syntax_getArg(v_a_2179_, v___x_2238_);
v___x_2240_ = l_Lean_Syntax_isNone(v___x_2239_);
if (v___x_2240_ == 0)
{
uint8_t v___x_2241_; 
v___x_2241_ = l_Lean_Syntax_matchesNull(v___x_2239_, v___x_2238_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2242_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2243_ = lean_box(0);
lean_inc(v_a_2179_);
v___x_2244_ = l_Lean_Syntax_formatStx(v_a_2179_, v___x_2243_, v___x_2241_);
v___x_2245_ = l_Std_Format_defWidth;
v___x_2246_ = l_Std_Format_pretty(v___x_2244_, v___x_2245_, v___x_2178_, v___x_2178_);
v___x_2247_ = l_Lean_stringToMessageData(v___x_2246_);
v___x_2248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2242_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2248_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_dec_ref_known(v___x_2249_, 1);
v_a_2172_ = v_b_2163_;
goto v___jp_2171_;
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v_b_2163_);
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
v___y_2181_ = v___y_2164_;
v___y_2182_ = v___y_2165_;
v___y_2183_ = v___y_2166_;
v___y_2184_ = v___y_2167_;
v___y_2185_ = v___y_2168_;
v___y_2186_ = v___y_2169_;
goto v___jp_2180_;
}
}
else
{
lean_dec(v___x_2239_);
v___y_2181_ = v___y_2164_;
v___y_2182_ = v___y_2165_;
v___y_2183_ = v___y_2166_;
v___y_2184_ = v___y_2167_;
v___y_2185_ = v___y_2168_;
v___y_2186_ = v___y_2169_;
goto v___jp_2180_;
}
}
v___jp_2180_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_unsigned_to_nat(4u);
v___x_2188_ = l_Lean_Syntax_getArg(v_a_2179_, v___x_2187_);
v___x_2189_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2188_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2191_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___x_2191_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2190_, v_b_2163_);
v_a_2172_ = v___x_2191_;
goto v___jp_2171_;
}
else
{
lean_dec_ref(v_b_2163_);
return v___x_2189_;
}
}
}
v___jp_2171_:
{
size_t v___x_2173_; size_t v___x_2174_; 
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_add(v_i_2162_, v___x_2173_);
v_i_2162_ = v___x_2174_;
v_b_2163_ = v_a_2172_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2160_ = stack[0].m_obj;
size_t v_sz_2161_ = stack[1].m_num;
size_t v_i_2162_ = stack[2].m_num;
lean_object* v_b_2163_ = stack[3].m_obj;
lean_object* v___y_2164_ = stack[4].m_obj;
lean_object* v___y_2165_ = stack[5].m_obj;
lean_object* v___y_2166_ = stack[6].m_obj;
lean_object* v___y_2167_ = stack[7].m_obj;
lean_object* v___y_2168_ = stack[8].m_obj;
lean_object* v___y_2169_ = stack[9].m_obj;
lean_object* v_res_2258_;
v_res_2258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_2160_, v_sz_2161_, v_i_2162_, v_b_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
stack->m_obj
 = v_res_2258_;
}
lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2259_) == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
else
{
lean_object* v_val_2269_; lean_object* v___x_2270_; 
v_val_2269_ = lean_ctor_get(v_stx_x3f_2259_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v_stx_x3f_2259_, 1);
v___x_2270_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2269_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
return v___x_2270_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_InferControlInfo_ofOptionSeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_x3f_2259_ = stack[0].m_obj;
lean_object* v_a_2260_ = stack[1].m_obj;
lean_object* v_a_2261_ = stack[2].m_obj;
lean_object* v_a_2262_ = stack[3].m_obj;
lean_object* v_a_2263_ = stack[4].m_obj;
lean_object* v_a_2264_ = stack[5].m_obj;
lean_object* v_a_2265_ = stack[6].m_obj;
lean_object* v_res_2271_;
v_res_2271_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
stack->m_obj
 = v_res_2271_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2290_, lean_object* v_as_2291_, size_t v_sz_2292_, size_t v_i_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_a_2303_; uint8_t v___x_2307_; 
v___x_2307_ = lean_usize_dec_lt(v_i_2293_, v_sz_2292_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v_b_2294_);
return v___x_2308_;
}
else
{
lean_object* v___x_2309_; lean_object* v_a_2310_; uint8_t v___x_2311_; 
v___x_2309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2310_ = lean_array_uget_borrowed(v_as_2291_, v_i_2293_);
lean_inc(v_a_2310_);
v___x_2311_ = l_Lean_Syntax_isOfKind(v_a_2310_, v___x_2309_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_dec_ref_known(v___x_2312_, 1);
v_a_2303_ = v_b_2294_;
goto v___jp_2302_;
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v_b_2294_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
else
{
lean_object* v___x_2321_; lean_object* v___y_2323_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2321_ = lean_unsigned_to_nat(3u);
v___x_2340_ = lean_unsigned_to_nat(1u);
v___x_2341_ = l_Lean_Syntax_getArg(v_a_2310_, v___x_2340_);
v___x_2342_ = l_Lean_Syntax_getArgs(v___x_2341_);
lean_dec(v___x_2341_);
v___x_2343_ = lean_unsigned_to_nat(0u);
v___x_2344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2345_ = lean_array_get_size(v___x_2342_);
v___x_2346_ = lean_nat_dec_lt(v___x_2343_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_dec_ref(v___x_2342_);
v___y_2323_ = v___x_2344_;
goto v___jp_2322_;
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2351_; lean_object* v_snd_2352_; 
v___x_2347_ = lean_box(v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___x_2344_);
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = lean_usize_of_nat(v___x_2345_);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2311_, v___x_2290_, v___x_2342_, v___x_2349_, v___x_2350_, v___x_2348_);
lean_dec_ref(v___x_2342_);
v_snd_2352_ = lean_ctor_get(v___x_2351_, 1);
lean_inc(v_snd_2352_);
lean_dec_ref(v___x_2351_);
v___y_2323_ = v_snd_2352_;
goto v___jp_2322_;
}
v___jp_2322_:
{
size_t v_sz_2324_; size_t v___x_2325_; lean_object* v___x_2326_; 
v_sz_2324_ = lean_array_size(v___y_2323_);
v___x_2325_ = ((size_t)0ULL);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2324_, v___x_2325_, v___y_2323_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_dec_ref_known(v___x_2327_, 1);
v_a_2303_ = v_b_2294_;
goto v___jp_2302_;
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec_ref(v_b_2294_);
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref_known(v___x_2326_, 1);
v___x_2336_ = l_Lean_Syntax_getArg(v_a_2310_, v___x_2321_);
v___x_2337_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2336_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2294_, v_a_2338_);
v_a_2303_ = v___x_2339_;
goto v___jp_2302_;
}
else
{
lean_dec_ref(v_b_2294_);
return v___x_2337_;
}
}
}
}
}
v___jp_2302_:
{
size_t v___x_2304_; size_t v___x_2305_; 
v___x_2304_ = ((size_t)1ULL);
v___x_2305_ = lean_usize_add(v_i_2293_, v___x_2304_);
v_i_2293_ = v___x_2305_;
v_b_2294_ = v_a_2303_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2290_ = stack[0].m_num;
lean_object* v_as_2291_ = stack[1].m_obj;
size_t v_sz_2292_ = stack[2].m_num;
size_t v_i_2293_ = stack[3].m_num;
lean_object* v_b_2294_ = stack[4].m_obj;
lean_object* v___y_2295_ = stack[5].m_obj;
lean_object* v___y_2296_ = stack[6].m_obj;
lean_object* v___y_2297_ = stack[7].m_obj;
lean_object* v___y_2298_ = stack[8].m_obj;
lean_object* v___y_2299_ = stack[9].m_obj;
lean_object* v___y_2300_ = stack[10].m_obj;
lean_object* v_res_2353_;
v_res_2353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2290_, v_as_2291_, v_sz_2292_, v_i_2293_, v_b_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
stack->m_obj
 = v_res_2353_;
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; 
v___x_2402_ = l_Lean_NameSet_empty;
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = 0;
v___x_2405_ = 1;
v___x_2406_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2406_, 0, v___x_2403_);
lean_ctor_set(v___x_2406_, 1, v___x_2402_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*2, v___x_2405_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*2 + 1, v___x_2404_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*2 + 2, v___x_2404_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*2 + 3, v___x_2405_);
return v___x_2406_;
}
}
lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___y_2416_; lean_object* v_bodyInfo_2417_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2461_; lean_object* v_bodyInfo_2462_; lean_object* v___x_2465_; lean_object* v_env_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2465_ = lean_st_ref_get(v_a_2413_);
v_env_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc_ref(v_env_2466_);
lean_dec(v___x_2465_);
lean_inc(v_stx_2407_);
v___x_2467_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2467_, 0, v_env_2466_);
lean_closure_set(v___x_2467_, 1, v_stx_2407_);
v___x_2468_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2467_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_5179_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_5179_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_5179_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
if (lean_obj_tag(v_a_2469_) == 1)
{
lean_object* v_val_2481_; lean_object* v_snd_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_del_object(v___x_2471_);
lean_dec(v_stx_2407_);
v_val_2481_ = lean_ctor_get(v_a_2469_, 0);
lean_inc(v_val_2481_);
lean_dec_ref_known(v_a_2469_, 1);
v_snd_2482_ = lean_ctor_get(v_val_2481_, 1);
lean_inc(v_snd_2482_);
lean_dec(v_val_2481_);
v___x_2483_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2483_, 0, lean_box(0));
lean_closure_set(v___x_2483_, 1, v_snd_2482_);
v___x_2484_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2483_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___x_2484_, 1);
v_stx_2407_ = v_a_2485_;
goto _start;
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
v_a_2487_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2484_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2484_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_object* v___x_2495_; uint8_t v___x_2496_; uint8_t v___x_2497_; 
lean_dec(v_a_2469_);
v___x_2495_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
lean_inc(v_stx_2407_);
v___x_2496_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2495_);
v___x_2497_ = 1;
if (v___x_2496_ == 0)
{
lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3));
lean_inc(v_stx_2407_);
v___x_2499_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5));
lean_inc(v_stx_2407_);
v___x_2501_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2502_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7));
lean_inc(v_stx_2407_);
v___x_2503_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; uint8_t v___x_2505_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; 
v___x_2504_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9));
lean_inc(v_stx_2407_);
v___x_2505_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2620_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2407_);
v___x_2621_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2407_);
v___x_2674_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; uint8_t v___x_2676_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; 
v___x_2675_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2407_);
v___x_2676_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2734_; uint8_t v___x_2735_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; 
lean_del_object(v___x_2471_);
v___x_2734_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2407_);
v___x_2735_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2803_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2407_);
v___x_2804_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2805_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2407_);
v___x_2806_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; uint8_t v___x_2808_; 
v___x_2807_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2407_);
v___x_2808_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2407_);
v___x_2810_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2811_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2407_);
v___x_2812_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2813_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2407_);
v___x_2814_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2813_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2815_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2407_);
v___x_2816_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; uint8_t v___x_2818_; uint8_t v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; uint8_t v___y_2823_; 
v___x_2817_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2407_);
v___x_2818_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2407_);
v___x_2827_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2407_);
v___x_2829_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2830_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2407_);
v___x_2831_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2407_);
v___x_2833_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2832_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2834_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2407_);
v___x_2835_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2407_);
v___x_2837_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2407_);
v___x_2839_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2840_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2407_);
v___x_2841_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2840_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2842_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v_stx_2407_);
v___x_2843_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; uint8_t v___x_2845_; 
v___x_2844_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v_stx_2407_);
v___x_2845_ = l_Lean_Syntax_isOfKind(v_stx_2407_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v_env_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
lean_inc_n(v_stx_2407_, 2);
v___x_2846_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_2847_ = lean_st_ref_get(v_a_2413_);
v_env_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc_ref(v_env_2848_);
lean_dec(v___x_2847_);
v___x_2849_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2850_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2849_, v_env_2848_, v___x_2846_);
v___x_2851_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2852_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_2850_, v___x_2851_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_2850_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2883_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2883_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2883_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_fst_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2881_; 
v_fst_2857_ = lean_ctor_get(v_a_2853_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_a_2853_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v_a_2853_, 1);
lean_dec(v_unused_2882_);
v___x_2859_ = v_a_2853_;
v_isShared_2860_ = v_isSharedCheck_2881_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_fst_2857_);
lean_dec(v_a_2853_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2881_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
if (lean_obj_tag(v_fst_2857_) == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
lean_del_object(v___x_2855_);
v___x_2861_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2862_ = l_Lean_MessageData_ofName(v___x_2846_);
lean_inc_ref(v___x_2862_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set_tag(v___x_2859_, 7);
lean_ctor_set(v___x_2859_, 1, v___x_2862_);
lean_ctor_set(v___x_2859_, 0, v___x_2861_);
v___x_2864_ = v___x_2859_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2865_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_2868_ = l_Lean_indentD(v___x_2867_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2866_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v___x_2862_);
v___x_2873_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2874_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2875_;
}
}
else
{
lean_object* v_val_2877_; lean_object* v___x_2879_; 
lean_del_object(v___x_2859_);
lean_dec(v___x_2846_);
lean_dec(v_stx_2407_);
v_val_2877_ = lean_ctor_get(v_fst_2857_, 0);
lean_inc(v_val_2877_);
lean_dec_ref_known(v_fst_2857_, 1);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_val_2877_);
v___x_2879_ = v___x_2855_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_val_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v___x_2846_);
lean_dec(v_stx_2407_);
v_a_2884_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2852_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2852_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___y_2896_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_unsigned_to_nat(5u);
v___x_2894_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2893_);
v___x_2905_ = lean_unsigned_to_nat(6u);
v___x_2906_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2905_);
lean_dec(v_stx_2407_);
v___x_2907_ = l_Lean_Syntax_getOptional_x3f(v___x_2906_);
lean_dec(v___x_2906_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_box(0);
v___y_2896_ = v___x_2908_;
goto v___jp_2895_;
}
else
{
lean_object* v_val_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
v_val_2909_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2907_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_val_2909_);
lean_dec(v___x_2907_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_val_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
v___y_2896_ = v___x_2914_;
goto v___jp_2895_;
}
}
}
v___jp_2895_:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2894_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2897_) == 0)
{
if (lean_obj_tag(v___y_2896_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
v___x_2899_ = l_Lean_NameSet_empty;
v___x_2900_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2900_, 0, v___x_2892_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*2, v___x_2843_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*2 + 1, v___x_2843_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*2 + 2, v___x_2843_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*2 + 3, v___x_2843_);
v___y_2416_ = v_a_2898_;
v_bodyInfo_2417_ = v___x_2900_;
goto v___jp_2415_;
}
else
{
lean_object* v_a_2901_; lean_object* v_val_2902_; lean_object* v___x_2903_; 
v_a_2901_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2897_, 1);
v_val_2902_ = lean_ctor_get(v___y_2896_, 0);
lean_inc(v_val_2902_);
lean_dec_ref_known(v___y_2896_, 1);
v___x_2903_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2902_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___y_2416_ = v_a_2901_;
v_bodyInfo_2417_ = v_a_2904_;
goto v___jp_2415_;
}
else
{
lean_dec(v_a_2901_);
return v___x_2903_;
}
}
}
else
{
lean_dec(v___y_2896_);
return v___x_2897_;
}
}
}
}
else
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___y_2921_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2917_ = lean_unsigned_to_nat(1u);
v___x_2918_ = lean_unsigned_to_nat(5u);
v___x_2919_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2918_);
v___x_2930_ = lean_unsigned_to_nat(6u);
v___x_2931_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2930_);
lean_dec(v_stx_2407_);
v___x_2932_ = l_Lean_Syntax_getOptional_x3f(v___x_2931_);
lean_dec(v___x_2931_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_box(0);
v___y_2921_ = v___x_2933_;
goto v___jp_2920_;
}
else
{
lean_object* v_val_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
v_val_2934_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2932_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_val_2934_);
lean_dec(v___x_2932_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_val_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
v___y_2921_ = v___x_2939_;
goto v___jp_2920_;
}
}
}
v___jp_2920_:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2919_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2922_) == 0)
{
if (lean_obj_tag(v___y_2921_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = l_Lean_NameSet_empty;
v___x_2925_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2925_, 0, v___x_2917_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*2, v___x_2841_);
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*2 + 1, v___x_2841_);
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*2 + 2, v___x_2841_);
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*2 + 3, v___x_2841_);
v___y_2461_ = v_a_2923_;
v_bodyInfo_2462_ = v___x_2925_;
goto v___jp_2460_;
}
else
{
lean_object* v_a_2926_; lean_object* v_val_2927_; lean_object* v___x_2928_; 
v_a_2926_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2922_, 1);
v_val_2927_ = lean_ctor_get(v___y_2921_, 0);
lean_inc(v_val_2927_);
lean_dec_ref_known(v___y_2921_, 1);
v___x_2928_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2927_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2928_, 1);
v___y_2461_ = v_a_2926_;
v_bodyInfo_2462_ = v_a_2929_;
goto v___jp_2460_;
}
else
{
lean_dec(v_a_2926_);
return v___x_2928_;
}
}
}
else
{
lean_dec(v___y_2921_);
return v___x_2922_;
}
}
}
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_2942_ = lean_unsigned_to_nat(0u);
v___x_2943_ = lean_unsigned_to_nat(1u);
v___x_3157_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2943_);
v___x_3158_ = l_Lean_Syntax_isNone(v___x_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3159_ = lean_unsigned_to_nat(5u);
v___x_3160_ = l_Lean_Syntax_matchesNull(v___x_3157_, v___x_3159_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_env_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_inc_n(v_stx_2407_, 2);
v___x_3161_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3162_ = lean_st_ref_get(v_a_2413_);
v_env_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc_ref(v_env_3163_);
lean_dec(v___x_3162_);
v___x_3164_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3165_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3164_, v_env_3163_, v___x_3161_);
v___x_3166_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3167_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3165_, v___x_3166_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3165_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3198_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3198_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3198_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_fst_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3196_; 
v_fst_3172_ = lean_ctor_get(v_a_3168_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_a_3168_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; 
v_unused_3197_ = lean_ctor_get(v_a_3168_, 1);
lean_dec(v_unused_3197_);
v___x_3174_ = v_a_3168_;
v_isShared_3175_ = v_isSharedCheck_3196_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_fst_3172_);
lean_dec(v_a_3168_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3196_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
if (lean_obj_tag(v_fst_3172_) == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
lean_del_object(v___x_3170_);
v___x_3176_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3177_ = l_Lean_MessageData_ofName(v___x_3161_);
lean_inc_ref(v___x_3177_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 7);
lean_ctor_set(v___x_3174_, 1, v___x_3177_);
lean_ctor_set(v___x_3174_, 0, v___x_3176_);
v___x_3179_ = v___x_3174_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3180_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3179_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3183_ = l_Lean_indentD(v___x_3182_);
v___x_3184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3181_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3184_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v___x_3177_);
v___x_3188_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3189_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3190_;
}
}
else
{
lean_object* v_val_3192_; lean_object* v___x_3194_; 
lean_del_object(v___x_3174_);
lean_dec(v___x_3161_);
lean_dec(v_stx_2407_);
v_val_3192_ = lean_ctor_get(v_fst_3172_, 0);
lean_inc(v_val_3192_);
lean_dec_ref_known(v_fst_3172_, 1);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v_val_3192_);
v___x_3194_ = v___x_3170_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_val_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec(v___x_3161_);
lean_dec(v_stx_2407_);
v_a_3199_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3167_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3167_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
v___y_2945_ = v_a_2408_;
v___y_2946_ = v_a_2409_;
v___y_2947_ = v_a_2410_;
v___y_2948_ = v_a_2411_;
v___y_2949_ = v_a_2412_;
v___y_2950_ = v_a_2413_;
goto v___jp_2944_;
}
}
else
{
lean_dec(v___x_3157_);
v___y_2945_ = v_a_2408_;
v___y_2946_ = v_a_2409_;
v___y_2947_ = v_a_2410_;
v___y_2948_ = v_a_2411_;
v___y_2949_ = v_a_2412_;
v___y_2950_ = v_a_2413_;
goto v___jp_2944_;
}
v___jp_2944_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2951_ = lean_unsigned_to_nat(4u);
v___x_2952_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2951_);
v___x_2953_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
lean_inc(v___x_2952_);
v___x_2954_ = l_Lean_Syntax_isOfKind(v___x_2952_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_env_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
lean_dec(v___x_2952_);
lean_inc_n(v_stx_2407_, 2);
v___x_2955_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_2956_ = lean_st_ref_get(v___y_2950_);
v_env_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_ref(v_env_2957_);
lean_dec(v___x_2956_);
v___x_2958_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2959_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2958_, v_env_2957_, v___x_2955_);
v___x_2960_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2961_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_2959_, v___x_2960_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___x_2959_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2992_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2992_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2992_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v_fst_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2990_; 
v_fst_2966_ = lean_ctor_get(v_a_2962_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_a_2962_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v_a_2962_, 1);
lean_dec(v_unused_2991_);
v___x_2968_ = v_a_2962_;
v_isShared_2969_ = v_isSharedCheck_2990_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_fst_2966_);
lean_dec(v_a_2962_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2990_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
if (lean_obj_tag(v_fst_2966_) == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
lean_del_object(v___x_2964_);
v___x_2970_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2971_ = l_Lean_MessageData_ofName(v___x_2955_);
lean_inc_ref(v___x_2971_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set_tag(v___x_2968_, 7);
lean_ctor_set(v___x_2968_, 1, v___x_2971_);
lean_ctor_set(v___x_2968_, 0, v___x_2970_);
v___x_2973_ = v___x_2968_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2974_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2973_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_2977_ = l_Lean_indentD(v___x_2976_);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2975_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2978_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set(v___x_2981_, 1, v___x_2971_);
v___x_2982_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2981_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2983_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_2984_;
}
}
else
{
lean_object* v_val_2986_; lean_object* v___x_2988_; 
lean_del_object(v___x_2968_);
lean_dec(v___x_2955_);
lean_dec(v_stx_2407_);
v_val_2986_ = lean_ctor_get(v_fst_2966_, 0);
lean_inc(v_val_2986_);
lean_dec_ref_known(v_fst_2966_, 1);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v_val_2986_);
v___x_2988_ = v___x_2964_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_val_2986_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v___x_2955_);
lean_dec(v_stx_2407_);
v_a_2993_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2961_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2961_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; size_t v_sz_3003_; size_t v___x_3004_; lean_object* v___x_3005_; 
v___x_3001_ = l_Lean_Syntax_getArg(v___x_2952_, v___x_2942_);
v___x_3002_ = l_Lean_Syntax_getArgs(v___x_3001_);
lean_dec(v___x_3001_);
v_sz_3003_ = lean_array_size(v___x_3002_);
v___x_3004_ = ((size_t)0ULL);
v___x_3005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_2839_, v_sz_3003_, v___x_3004_, v___x_3002_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v_env_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec(v___x_2952_);
lean_inc_n(v_stx_2407_, 2);
v___x_3006_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3007_ = lean_st_ref_get(v___y_2950_);
v_env_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc_ref(v_env_3008_);
lean_dec(v___x_3007_);
v___x_3009_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3010_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3009_, v_env_3008_, v___x_3006_);
v___x_3011_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3012_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3010_, v___x_3011_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___x_3010_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3043_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3043_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3043_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_fst_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3041_; 
v_fst_3017_ = lean_ctor_get(v_a_3013_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_a_3013_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v_a_3013_, 1);
lean_dec(v_unused_3042_);
v___x_3019_ = v_a_3013_;
v_isShared_3020_ = v_isSharedCheck_3041_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_fst_3017_);
lean_dec(v_a_3013_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3041_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
if (lean_obj_tag(v_fst_3017_) == 0)
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_del_object(v___x_3015_);
v___x_3021_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3022_ = l_Lean_MessageData_ofName(v___x_3006_);
lean_inc_ref(v___x_3022_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set_tag(v___x_3019_, 7);
lean_ctor_set(v___x_3019_, 1, v___x_3022_);
lean_ctor_set(v___x_3019_, 0, v___x_3021_);
v___x_3024_ = v___x_3019_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3025_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3028_ = l_Lean_indentD(v___x_3027_);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3026_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v___x_3022_);
v___x_3033_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3034_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_3035_;
}
}
else
{
lean_object* v_val_3037_; lean_object* v___x_3039_; 
lean_del_object(v___x_3019_);
lean_dec(v___x_3006_);
lean_dec(v_stx_2407_);
v_val_3037_ = lean_ctor_get(v_fst_3017_, 0);
lean_inc(v_val_3037_);
lean_dec_ref_known(v_fst_3017_, 1);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v_val_3037_);
v___x_3039_ = v___x_3015_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_val_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v___x_3006_);
lean_dec(v_stx_2407_);
v_a_3044_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3012_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3012_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v_val_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v_val_3052_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_val_3052_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3053_ = l_Lean_Syntax_getArg(v___x_2952_, v___x_2943_);
lean_dec(v___x_2952_);
v___x_3054_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_3053_);
v___x_3055_ = l_Lean_Syntax_isOfKind(v___x_3053_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v_env_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec(v___x_3053_);
lean_dec(v_val_3052_);
lean_inc_n(v_stx_2407_, 2);
v___x_3056_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3057_ = lean_st_ref_get(v___y_2950_);
v_env_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc_ref(v_env_3058_);
lean_dec(v___x_3057_);
v___x_3059_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3060_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3059_, v_env_3058_, v___x_3056_);
v___x_3061_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3062_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3060_, v___x_3061_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___x_3060_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3093_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3065_ = v___x_3062_;
v_isShared_3066_ = v_isSharedCheck_3093_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3062_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3093_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v_fst_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3091_; 
v_fst_3067_ = lean_ctor_get(v_a_3063_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_a_3063_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v_a_3063_, 1);
lean_dec(v_unused_3092_);
v___x_3069_ = v_a_3063_;
v_isShared_3070_ = v_isSharedCheck_3091_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_fst_3067_);
lean_dec(v_a_3063_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3091_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
if (lean_obj_tag(v_fst_3067_) == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
lean_del_object(v___x_3065_);
v___x_3071_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3072_ = l_Lean_MessageData_ofName(v___x_3056_);
lean_inc_ref(v___x_3072_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set_tag(v___x_3069_, 7);
lean_ctor_set(v___x_3069_, 1, v___x_3072_);
lean_ctor_set(v___x_3069_, 0, v___x_3071_);
v___x_3074_ = v___x_3069_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3075_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3078_ = l_Lean_indentD(v___x_3077_);
v___x_3079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3076_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3072_);
v___x_3083_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3084_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_3085_;
}
}
else
{
lean_object* v_val_3087_; lean_object* v___x_3089_; 
lean_del_object(v___x_3069_);
lean_dec(v___x_3056_);
lean_dec(v_stx_2407_);
v_val_3087_ = lean_ctor_get(v_fst_3067_, 0);
lean_inc(v_val_3087_);
lean_dec_ref_known(v_fst_3067_, 1);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v_val_3087_);
v___x_3089_ = v___x_3065_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_val_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v___x_3056_);
lean_dec(v_stx_2407_);
v_a_3094_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3062_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3062_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3102_ = l_Lean_Syntax_getArg(v___x_3053_, v___x_2943_);
v___x_3103_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_3104_ = l_Lean_Syntax_isOfKind(v___x_3102_, v___x_3103_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v_env_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_dec(v___x_3053_);
lean_dec(v_val_3052_);
lean_inc_n(v_stx_2407_, 2);
v___x_3105_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3106_ = lean_st_ref_get(v___y_2950_);
v_env_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc_ref(v_env_3107_);
lean_dec(v___x_3106_);
v___x_3108_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3109_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3108_, v_env_3107_, v___x_3105_);
v___x_3110_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3111_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3109_, v___x_3110_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___x_3109_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3142_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3142_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3142_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v_fst_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3140_; 
v_fst_3116_ = lean_ctor_get(v_a_3112_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_a_3112_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v_a_3112_, 1);
lean_dec(v_unused_3141_);
v___x_3118_ = v_a_3112_;
v_isShared_3119_ = v_isSharedCheck_3140_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_fst_3116_);
lean_dec(v_a_3112_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3140_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
if (lean_obj_tag(v_fst_3116_) == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3123_; 
lean_del_object(v___x_3114_);
v___x_3120_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3121_ = l_Lean_MessageData_ofName(v___x_3105_);
lean_inc_ref(v___x_3121_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set_tag(v___x_3118_, 7);
lean_ctor_set(v___x_3118_, 1, v___x_3121_);
lean_ctor_set(v___x_3118_, 0, v___x_3120_);
v___x_3123_ = v___x_3118_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3124_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3123_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3127_ = l_Lean_indentD(v___x_3126_);
v___x_3128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3125_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3128_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
lean_ctor_set(v___x_3131_, 1, v___x_3121_);
v___x_3132_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3131_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
v___x_3134_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3133_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_3134_;
}
}
else
{
lean_object* v_val_3136_; lean_object* v___x_3138_; 
lean_del_object(v___x_3118_);
lean_dec(v___x_3105_);
lean_dec(v_stx_2407_);
v_val_3136_ = lean_ctor_get(v_fst_3116_, 0);
lean_inc(v_val_3136_);
lean_dec_ref_known(v_fst_3116_, 1);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v_val_3136_);
v___x_3138_ = v___x_3114_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_val_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v___x_3105_);
lean_dec(v_stx_2407_);
v_a_3143_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3111_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3111_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_dec(v_stx_2407_);
v___x_3151_ = lean_unsigned_to_nat(3u);
v___x_3152_ = l_Lean_Syntax_getArg(v___x_3053_, v___x_3151_);
lean_dec(v___x_3053_);
v___x_3153_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3152_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; size_t v_sz_3155_; lean_object* v___x_3156_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v_sz_3155_ = lean_array_size(v_val_3052_);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_3052_, v_sz_3155_, v___x_3004_, v_a_3154_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v_val_3052_);
return v___x_3156_;
}
else
{
lean_dec(v_val_3052_);
return v___x_3153_;
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
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_dec(v_stx_2407_);
v___x_3207_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
return v___x_3208_;
}
}
else
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec(v_stx_2407_);
v___x_3209_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
return v___x_3210_;
}
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_dec(v_stx_2407_);
v___x_3211_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_dec(v_stx_2407_);
v___x_3213_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
else
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_dec(v_stx_2407_);
v___x_3215_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
return v___x_3216_;
}
}
else
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; size_t v_sz_3220_; size_t v___x_3221_; lean_object* v___x_3222_; 
v___x_3217_ = lean_unsigned_to_nat(2u);
v___x_3218_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3217_);
v___x_3219_ = l_Lean_Syntax_getArgs(v___x_3218_);
lean_dec(v___x_3218_);
v_sz_3220_ = lean_array_size(v___x_3219_);
v___x_3221_ = ((size_t)0ULL);
v___x_3222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3220_, v___x_3221_, v___x_3219_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v_env_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_inc_n(v_stx_2407_, 2);
v___x_3223_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3224_ = lean_st_ref_get(v_a_2413_);
v_env_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc_ref(v_env_3225_);
lean_dec(v___x_3224_);
v___x_3226_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3227_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3226_, v_env_3225_, v___x_3223_);
v___x_3228_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3229_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3227_, v___x_3228_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3227_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3260_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3260_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3260_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v_fst_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3258_; 
v_fst_3234_ = lean_ctor_get(v_a_3230_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_a_3230_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v_a_3230_, 1);
lean_dec(v_unused_3259_);
v___x_3236_ = v_a_3230_;
v_isShared_3237_ = v_isSharedCheck_3258_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_fst_3234_);
lean_dec(v_a_3230_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3258_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
if (lean_obj_tag(v_fst_3234_) == 0)
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
lean_del_object(v___x_3232_);
v___x_3238_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3239_ = l_Lean_MessageData_ofName(v___x_3223_);
lean_inc_ref(v___x_3239_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set_tag(v___x_3236_, 7);
lean_ctor_set(v___x_3236_, 1, v___x_3239_);
lean_ctor_set(v___x_3236_, 0, v___x_3238_);
v___x_3241_ = v___x_3236_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3242_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3245_ = l_Lean_indentD(v___x_3244_);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3243_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v___x_3239_);
v___x_3250_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3251_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3252_;
}
}
else
{
lean_object* v_val_3254_; lean_object* v___x_3256_; 
lean_del_object(v___x_3236_);
lean_dec(v___x_3223_);
lean_dec(v_stx_2407_);
v_val_3254_ = lean_ctor_get(v_fst_3234_, 0);
lean_inc(v_val_3254_);
lean_dec_ref_known(v_fst_3234_, 1);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v_val_3254_);
v___x_3256_ = v___x_3232_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_val_3254_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec(v___x_3223_);
lean_dec(v_stx_2407_);
v_a_3261_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3229_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3229_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
else
{
lean_object* v_val_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3403_; 
v_val_3269_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3271_ = v___x_3222_;
v_isShared_3272_ = v_isSharedCheck_3403_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_val_3269_);
lean_dec(v___x_3222_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3403_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v_finSeq_x3f_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3273_ = lean_unsigned_to_nat(1u);
v___x_3274_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3273_);
v___x_3298_ = lean_unsigned_to_nat(3u);
v___x_3299_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3298_);
v___x_3300_ = l_Lean_Syntax_isNone(v___x_3299_);
if (v___x_3300_ == 0)
{
uint8_t v___x_3301_; 
lean_inc(v___x_3299_);
v___x_3301_ = l_Lean_Syntax_matchesNull(v___x_3299_, v___x_3273_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v_env_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
lean_dec(v___x_3299_);
lean_dec(v___x_3274_);
lean_del_object(v___x_3271_);
lean_dec(v_val_3269_);
lean_inc_n(v_stx_2407_, 2);
v___x_3302_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3303_ = lean_st_ref_get(v_a_2413_);
v_env_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc_ref(v_env_3304_);
lean_dec(v___x_3303_);
v___x_3305_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3306_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3305_, v_env_3304_, v___x_3302_);
v___x_3307_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3308_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3306_, v___x_3307_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3306_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3339_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3339_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3339_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v_fst_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3337_; 
v_fst_3313_ = lean_ctor_get(v_a_3309_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_a_3309_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v_a_3309_, 1);
lean_dec(v_unused_3338_);
v___x_3315_ = v_a_3309_;
v_isShared_3316_ = v_isSharedCheck_3337_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_fst_3313_);
lean_dec(v_a_3309_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3337_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
if (lean_obj_tag(v_fst_3313_) == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
lean_del_object(v___x_3311_);
v___x_3317_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3318_ = l_Lean_MessageData_ofName(v___x_3302_);
lean_inc_ref(v___x_3318_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set_tag(v___x_3315_, 7);
lean_ctor_set(v___x_3315_, 1, v___x_3318_);
lean_ctor_set(v___x_3315_, 0, v___x_3317_);
v___x_3320_ = v___x_3315_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3332_, 1, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3321_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3324_ = l_Lean_indentD(v___x_3323_);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3322_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
lean_ctor_set(v___x_3328_, 1, v___x_3318_);
v___x_3329_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3330_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3331_;
}
}
else
{
lean_object* v_val_3333_; lean_object* v___x_3335_; 
lean_del_object(v___x_3315_);
lean_dec(v___x_3302_);
lean_dec(v_stx_2407_);
v_val_3333_ = lean_ctor_get(v_fst_3313_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v_fst_3313_, 1);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v_val_3333_);
v___x_3335_ = v___x_3311_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_val_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec(v___x_3302_);
lean_dec(v_stx_2407_);
v_a_3340_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3308_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3308_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3348_ = lean_unsigned_to_nat(0u);
v___x_3349_ = l_Lean_Syntax_getArg(v___x_3299_, v___x_3348_);
lean_dec(v___x_3299_);
v___x_3350_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
lean_inc(v___x_3349_);
v___x_3351_ = l_Lean_Syntax_isOfKind(v___x_3349_, v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v_env_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec(v___x_3349_);
lean_dec(v___x_3274_);
lean_del_object(v___x_3271_);
lean_dec(v_val_3269_);
lean_inc_n(v_stx_2407_, 2);
v___x_3352_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3353_ = lean_st_ref_get(v_a_2413_);
v_env_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc_ref(v_env_3354_);
lean_dec(v___x_3353_);
v___x_3355_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3356_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3355_, v_env_3354_, v___x_3352_);
v___x_3357_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3358_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3356_, v___x_3357_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3356_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3389_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3361_ = v___x_3358_;
v_isShared_3362_ = v_isSharedCheck_3389_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3389_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v_fst_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3387_; 
v_fst_3363_ = lean_ctor_get(v_a_3359_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_a_3359_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v_a_3359_, 1);
lean_dec(v_unused_3388_);
v___x_3365_ = v_a_3359_;
v_isShared_3366_ = v_isSharedCheck_3387_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_fst_3363_);
lean_dec(v_a_3359_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3387_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
if (lean_obj_tag(v_fst_3363_) == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
lean_del_object(v___x_3361_);
v___x_3367_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3368_ = l_Lean_MessageData_ofName(v___x_3352_);
lean_inc_ref(v___x_3368_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set_tag(v___x_3365_, 7);
lean_ctor_set(v___x_3365_, 1, v___x_3368_);
lean_ctor_set(v___x_3365_, 0, v___x_3367_);
v___x_3370_ = v___x_3365_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3371_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3370_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3374_ = l_Lean_indentD(v___x_3373_);
v___x_3375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3372_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
lean_ctor_set(v___x_3378_, 1, v___x_3368_);
v___x_3379_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3380_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3381_;
}
}
else
{
lean_object* v_val_3383_; lean_object* v___x_3385_; 
lean_del_object(v___x_3365_);
lean_dec(v___x_3352_);
lean_dec(v_stx_2407_);
v_val_3383_ = lean_ctor_get(v_fst_3363_, 0);
lean_inc(v_val_3383_);
lean_dec_ref_known(v_fst_3363_, 1);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v_val_3383_);
v___x_3385_ = v___x_3361_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_val_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v___x_3352_);
lean_dec(v_stx_2407_);
v_a_3390_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3358_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3358_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3400_; 
lean_dec(v_stx_2407_);
v___x_3398_ = l_Lean_Syntax_getArg(v___x_3349_, v___x_3273_);
lean_dec(v___x_3349_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v___x_3398_);
v___x_3400_ = v___x_3271_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
v_finSeq_x3f_3276_ = v___x_3400_;
v___y_3277_ = v_a_2408_;
v___y_3278_ = v_a_2409_;
v___y_3279_ = v_a_2410_;
v___y_3280_ = v_a_2411_;
v___y_3281_ = v_a_2412_;
v___y_3282_ = v_a_2413_;
goto v___jp_3275_;
}
}
}
}
else
{
lean_object* v___x_3402_; 
lean_dec(v___x_3299_);
lean_del_object(v___x_3271_);
lean_dec(v_stx_2407_);
v___x_3402_ = lean_box(0);
v_finSeq_x3f_3276_ = v___x_3402_;
v___y_3277_ = v_a_2408_;
v___y_3278_ = v_a_2409_;
v___y_3279_ = v_a_2410_;
v___y_3280_ = v_a_2411_;
v___y_3281_ = v_a_2412_;
v___y_3282_ = v_a_2413_;
goto v___jp_3275_;
}
v___jp_3275_:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3274_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; size_t v_sz_3285_; lean_object* v___x_3286_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref_known(v___x_3283_, 1);
v_sz_3285_ = lean_array_size(v_val_3269_);
v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3269_, v_sz_3285_, v___x_3221_, v_a_3284_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v_val_3269_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3288_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3297_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3297_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3297_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3287_, v_a_3289_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3293_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
else
{
lean_dec(v_a_3287_);
return v___x_3288_;
}
}
else
{
lean_dec(v_finSeq_x3f_3276_);
return v___x_3286_;
}
}
else
{
lean_dec(v_finSeq_x3f_3276_);
lean_dec(v_val_3269_);
return v___x_3283_;
}
}
}
}
}
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_unsigned_to_nat(1u);
v___x_3528_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3405_);
v___x_3529_ = l_Lean_Syntax_isNone(v___x_3528_);
if (v___x_3529_ == 0)
{
uint8_t v___x_3530_; 
lean_inc(v___x_3528_);
v___x_3530_ = l_Lean_Syntax_matchesNull(v___x_3528_, v___x_3405_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v_env_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec(v___x_3528_);
lean_inc_n(v_stx_2407_, 2);
v___x_3531_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3532_ = lean_st_ref_get(v_a_2413_);
v_env_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc_ref(v_env_3533_);
lean_dec(v___x_3532_);
v___x_3534_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3535_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3534_, v_env_3533_, v___x_3531_);
v___x_3536_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3537_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3535_, v___x_3536_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3535_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3568_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3540_ = v___x_3537_;
v_isShared_3541_ = v_isSharedCheck_3568_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3537_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3568_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v_fst_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3566_; 
v_fst_3542_ = lean_ctor_get(v_a_3538_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_a_3538_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v_a_3538_, 1);
lean_dec(v_unused_3567_);
v___x_3544_ = v_a_3538_;
v_isShared_3545_ = v_isSharedCheck_3566_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_fst_3542_);
lean_dec(v_a_3538_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3566_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
if (lean_obj_tag(v_fst_3542_) == 0)
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3549_; 
lean_del_object(v___x_3540_);
v___x_3546_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3547_ = l_Lean_MessageData_ofName(v___x_3531_);
lean_inc_ref(v___x_3547_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set_tag(v___x_3544_, 7);
lean_ctor_set(v___x_3544_, 1, v___x_3547_);
lean_ctor_set(v___x_3544_, 0, v___x_3546_);
v___x_3549_ = v___x_3544_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3550_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3553_ = l_Lean_indentD(v___x_3552_);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3551_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3554_);
lean_ctor_set(v___x_3556_, 1, v___x_3555_);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v___x_3547_);
v___x_3558_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3557_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3559_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3560_;
}
}
else
{
lean_object* v_val_3562_; lean_object* v___x_3564_; 
lean_del_object(v___x_3544_);
lean_dec(v___x_3531_);
lean_dec(v_stx_2407_);
v_val_3562_ = lean_ctor_get(v_fst_3542_, 0);
lean_inc(v_val_3562_);
lean_dec_ref_known(v_fst_3542_, 1);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v_val_3562_);
v___x_3564_ = v___x_3540_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_val_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v___x_3531_);
lean_dec(v_stx_2407_);
v_a_3569_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3537_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3537_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
if (v___x_3529_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v___x_3577_ = l_Lean_Syntax_getArg(v___x_3528_, v___x_3404_);
lean_dec(v___x_3528_);
v___x_3578_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3579_ = l_Lean_Syntax_isOfKind(v___x_3577_, v___x_3578_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v_env_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_inc_n(v_stx_2407_, 2);
v___x_3580_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3581_ = lean_st_ref_get(v_a_2413_);
v_env_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc_ref(v_env_3582_);
lean_dec(v___x_3581_);
v___x_3583_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3584_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3583_, v_env_3582_, v___x_3580_);
v___x_3585_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3586_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3584_, v___x_3585_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3584_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3617_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3589_ = v___x_3586_;
v_isShared_3590_ = v_isSharedCheck_3617_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3617_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v_fst_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3615_; 
v_fst_3591_ = lean_ctor_get(v_a_3587_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_a_3587_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; 
v_unused_3616_ = lean_ctor_get(v_a_3587_, 1);
lean_dec(v_unused_3616_);
v___x_3593_ = v_a_3587_;
v_isShared_3594_ = v_isSharedCheck_3615_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_fst_3591_);
lean_dec(v_a_3587_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3615_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
if (lean_obj_tag(v_fst_3591_) == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3598_; 
lean_del_object(v___x_3589_);
v___x_3595_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3596_ = l_Lean_MessageData_ofName(v___x_3580_);
lean_inc_ref(v___x_3596_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set_tag(v___x_3593_, 7);
lean_ctor_set(v___x_3593_, 1, v___x_3596_);
lean_ctor_set(v___x_3593_, 0, v___x_3595_);
v___x_3598_ = v___x_3593_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3599_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3598_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3602_ = l_Lean_indentD(v___x_3601_);
v___x_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3600_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v___x_3596_);
v___x_3607_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3608_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3609_;
}
}
else
{
lean_object* v_val_3611_; lean_object* v___x_3613_; 
lean_del_object(v___x_3593_);
lean_dec(v___x_3580_);
lean_dec(v_stx_2407_);
v_val_3611_ = lean_ctor_get(v_fst_3591_, 0);
lean_inc(v_val_3611_);
lean_dec_ref_known(v_fst_3591_, 1);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v_val_3611_);
v___x_3613_ = v___x_3589_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_val_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec(v___x_3580_);
lean_dec(v_stx_2407_);
v_a_3618_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3586_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3586_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
v___y_3423_ = v_a_2408_;
v___y_3424_ = v_a_2409_;
v___y_3425_ = v_a_2410_;
v___y_3426_ = v_a_2411_;
v___y_3427_ = v_a_2412_;
v___y_3428_ = v_a_2413_;
goto v___jp_3422_;
}
}
else
{
lean_dec(v___x_3528_);
v___y_3423_ = v_a_2408_;
v___y_3424_ = v_a_2409_;
v___y_3425_ = v_a_2410_;
v___y_3426_ = v_a_2411_;
v___y_3427_ = v_a_2412_;
v___y_3428_ = v_a_2413_;
goto v___jp_3422_;
}
}
}
else
{
lean_dec(v___x_3528_);
v___y_3423_ = v_a_2408_;
v___y_3424_ = v_a_2409_;
v___y_3425_ = v_a_2410_;
v___y_3426_ = v_a_2411_;
v___y_3427_ = v_a_2412_;
v___y_3428_ = v_a_2413_;
goto v___jp_3422_;
}
v___jp_3406_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_unsigned_to_nat(3u);
v___x_3414_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3413_);
lean_dec(v_stx_2407_);
v___x_3415_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3414_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; uint8_t v_breaks_3417_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3415_, 1);
v_breaks_3417_ = lean_ctor_get_uint8(v_a_3416_, sizeof(void*)*2);
if (v_breaks_3417_ == 0)
{
uint8_t v_returnsEarly_3418_; lean_object* v_reassigns_3419_; 
v_returnsEarly_3418_ = lean_ctor_get_uint8(v_a_3416_, sizeof(void*)*2 + 2);
v_reassigns_3419_ = lean_ctor_get(v_a_3416_, 1);
lean_inc(v_reassigns_3419_);
lean_dec(v_a_3416_);
v___y_2820_ = v_returnsEarly_3418_;
v___y_2821_ = v___x_3404_;
v___y_2822_ = v_reassigns_3419_;
v___y_2823_ = v___x_2827_;
goto v___jp_2819_;
}
else
{
uint8_t v_returnsEarly_3420_; lean_object* v_reassigns_3421_; 
v_returnsEarly_3420_ = lean_ctor_get_uint8(v_a_3416_, sizeof(void*)*2 + 2);
v_reassigns_3421_ = lean_ctor_get(v_a_3416_, 1);
lean_inc(v_reassigns_3421_);
lean_dec(v_a_3416_);
v___y_2820_ = v_returnsEarly_3420_;
v___y_2821_ = v___x_3405_;
v___y_2822_ = v_reassigns_3421_;
v___y_2823_ = v___x_2818_;
goto v___jp_2819_;
}
}
else
{
return v___x_3415_;
}
}
v___jp_3422_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; 
v___x_3429_ = lean_unsigned_to_nat(2u);
v___x_3430_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3429_);
v___x_3431_ = l_Lean_Syntax_isNone(v___x_3430_);
if (v___x_3431_ == 0)
{
uint8_t v___x_3432_; 
lean_inc(v___x_3430_);
v___x_3432_ = l_Lean_Syntax_matchesNull(v___x_3430_, v___x_3405_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v_env_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_dec(v___x_3430_);
lean_inc_n(v_stx_2407_, 2);
v___x_3433_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3434_ = lean_st_ref_get(v___y_3428_);
v_env_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc_ref(v_env_3435_);
lean_dec(v___x_3434_);
v___x_3436_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3437_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3436_, v_env_3435_, v___x_3433_);
v___x_3438_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3439_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3437_, v___x_3438_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___x_3437_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3470_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3470_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3470_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v_fst_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3468_; 
v_fst_3444_ = lean_ctor_get(v_a_3440_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_a_3440_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v_a_3440_, 1);
lean_dec(v_unused_3469_);
v___x_3446_ = v_a_3440_;
v_isShared_3447_ = v_isSharedCheck_3468_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_fst_3444_);
lean_dec(v_a_3440_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3468_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
if (lean_obj_tag(v_fst_3444_) == 0)
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3451_; 
lean_del_object(v___x_3442_);
v___x_3448_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3449_ = l_Lean_MessageData_ofName(v___x_3433_);
lean_inc_ref(v___x_3449_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set_tag(v___x_3446_, 7);
lean_ctor_set(v___x_3446_, 1, v___x_3449_);
lean_ctor_set(v___x_3446_, 0, v___x_3448_);
v___x_3451_ = v___x_3446_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3452_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3455_ = l_Lean_indentD(v___x_3454_);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3453_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v___x_3449_);
v___x_3460_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3459_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3461_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
return v___x_3462_;
}
}
else
{
lean_object* v_val_3464_; lean_object* v___x_3466_; 
lean_del_object(v___x_3446_);
lean_dec(v___x_3433_);
lean_dec(v_stx_2407_);
v_val_3464_ = lean_ctor_get(v_fst_3444_, 0);
lean_inc(v_val_3464_);
lean_dec_ref_known(v_fst_3444_, 1);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v_val_3464_);
v___x_3466_ = v___x_3442_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_val_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v___x_3433_);
lean_dec(v_stx_2407_);
v_a_3471_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3439_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3439_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
if (v___x_3431_ == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3479_ = l_Lean_Syntax_getArg(v___x_3430_, v___x_3404_);
lean_dec(v___x_3430_);
v___x_3480_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3481_ = l_Lean_Syntax_isOfKind(v___x_3479_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v_env_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_inc_n(v_stx_2407_, 2);
v___x_3482_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3483_ = lean_st_ref_get(v___y_3428_);
v_env_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc_ref(v_env_3484_);
lean_dec(v___x_3483_);
v___x_3485_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3486_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3485_, v_env_3484_, v___x_3482_);
v___x_3487_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3488_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3486_, v___x_3487_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___x_3486_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3519_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3519_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3519_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v_fst_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3517_; 
v_fst_3493_ = lean_ctor_get(v_a_3489_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_a_3489_);
if (v_isSharedCheck_3517_ == 0)
{
lean_object* v_unused_3518_; 
v_unused_3518_ = lean_ctor_get(v_a_3489_, 1);
lean_dec(v_unused_3518_);
v___x_3495_ = v_a_3489_;
v_isShared_3496_ = v_isSharedCheck_3517_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_fst_3493_);
lean_dec(v_a_3489_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3517_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
if (lean_obj_tag(v_fst_3493_) == 0)
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
lean_del_object(v___x_3491_);
v___x_3497_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3498_ = l_Lean_MessageData_ofName(v___x_3482_);
lean_inc_ref(v___x_3498_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set_tag(v___x_3495_, 7);
lean_ctor_set(v___x_3495_, 1, v___x_3498_);
lean_ctor_set(v___x_3495_, 0, v___x_3497_);
v___x_3500_ = v___x_3495_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3501_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3504_ = l_Lean_indentD(v___x_3503_);
v___x_3505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3502_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3505_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
lean_ctor_set(v___x_3508_, 1, v___x_3498_);
v___x_3509_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3508_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
v___x_3511_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3510_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
return v___x_3511_;
}
}
else
{
lean_object* v_val_3513_; lean_object* v___x_3515_; 
lean_del_object(v___x_3495_);
lean_dec(v___x_3482_);
lean_dec(v_stx_2407_);
v_val_3513_ = lean_ctor_get(v_fst_3493_, 0);
lean_inc(v_val_3513_);
lean_dec_ref_known(v_fst_3493_, 1);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v_val_3513_);
v___x_3515_ = v___x_3491_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_val_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec(v___x_3482_);
lean_dec(v_stx_2407_);
v_a_3520_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3488_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3488_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
v___y_3407_ = v___y_3423_;
v___y_3408_ = v___y_3424_;
v___y_3409_ = v___y_3425_;
v___y_3410_ = v___y_3426_;
v___y_3411_ = v___y_3427_;
v___y_3412_ = v___y_3428_;
goto v___jp_3406_;
}
}
else
{
lean_dec(v___x_3430_);
v___y_3407_ = v___y_3423_;
v___y_3408_ = v___y_3424_;
v___y_3409_ = v___y_3425_;
v___y_3410_ = v___y_3426_;
v___y_3411_ = v___y_3427_;
v___y_3412_ = v___y_3428_;
goto v___jp_3406_;
}
}
}
else
{
lean_dec(v___x_3430_);
v___y_3407_ = v___y_3423_;
v___y_3408_ = v___y_3424_;
v___y_3409_ = v___y_3425_;
v___y_3410_ = v___y_3426_;
v___y_3411_ = v___y_3427_;
v___y_3412_ = v___y_3428_;
goto v___jp_3406_;
}
}
}
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3763_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v___x_3626_ = lean_unsigned_to_nat(0u);
v___x_3627_ = lean_unsigned_to_nat(1u);
v___x_3912_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3627_);
v___x_3913_ = l_Lean_Syntax_getArgs(v___x_3912_);
lean_dec(v___x_3912_);
v___x_3914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3915_ = lean_array_get_size(v___x_3913_);
v___x_3916_ = lean_nat_dec_lt(v___x_3626_, v___x_3915_);
if (v___x_3916_ == 0)
{
lean_dec_ref(v___x_3913_);
v___y_3763_ = v___x_3914_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; size_t v___x_3919_; size_t v___x_3920_; lean_object* v___x_3921_; lean_object* v_snd_3922_; 
v___x_3917_ = lean_box(v___x_3916_);
v___x_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
lean_ctor_set(v___x_3918_, 1, v___x_3914_);
v___x_3919_ = ((size_t)0ULL);
v___x_3920_ = lean_usize_of_nat(v___x_3915_);
v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2818_, v___x_2816_, v___x_3913_, v___x_3919_, v___x_3920_, v___x_3918_);
lean_dec_ref(v___x_3913_);
v_snd_3922_ = lean_ctor_get(v___x_3921_, 1);
lean_inc(v_snd_3922_);
lean_dec_ref(v___x_3921_);
v___y_3763_ = v_snd_3922_;
goto v___jp_3762_;
}
v___jp_3628_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3635_ = lean_unsigned_to_nat(5u);
v___x_3636_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3635_);
lean_dec(v_stx_2407_);
v___x_3637_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3636_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3655_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3655_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3655_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
uint8_t v_returnsEarly_3642_; lean_object* v_reassigns_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3653_; 
v_returnsEarly_3642_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*2 + 2);
v_reassigns_3643_ = lean_ctor_get(v_a_3638_, 1);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_a_3638_);
if (v_isSharedCheck_3653_ == 0)
{
lean_object* v_unused_3654_; 
v_unused_3654_ = lean_ctor_get(v_a_3638_, 0);
lean_dec(v_unused_3654_);
v___x_3645_ = v_a_3638_;
v_isShared_3646_ = v_isSharedCheck_3653_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_reassigns_3643_);
lean_dec(v_a_3638_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3653_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3627_);
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_reassigns_3643_);
lean_ctor_set_uint8(v_reuseFailAlloc_3652_, sizeof(void*)*2 + 2, v_returnsEarly_3642_);
v___x_3648_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3650_; 
lean_ctor_set_uint8(v___x_3648_, sizeof(void*)*2, v___x_2816_);
lean_ctor_set_uint8(v___x_3648_, sizeof(void*)*2 + 1, v___x_2816_);
lean_ctor_set_uint8(v___x_3648_, sizeof(void*)*2 + 3, v___x_2816_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3648_);
v___x_3650_ = v___x_3640_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
else
{
return v___x_3637_;
}
}
v___jp_3656_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3663_ = lean_unsigned_to_nat(3u);
v___x_3664_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3663_);
v___x_3665_ = l_Lean_Syntax_isNone(v___x_3664_);
if (v___x_3665_ == 0)
{
uint8_t v___x_3666_; 
lean_inc(v___x_3664_);
v___x_3666_ = l_Lean_Syntax_matchesNull(v___x_3664_, v___x_3627_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v_env_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_dec(v___x_3664_);
lean_inc_n(v_stx_2407_, 2);
v___x_3667_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3668_ = lean_st_ref_get(v___y_3662_);
v_env_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc_ref(v_env_3669_);
lean_dec(v___x_3668_);
v___x_3670_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3671_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3670_, v_env_3669_, v___x_3667_);
v___x_3672_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3673_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3671_, v___x_3672_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
lean_dec(v___x_3671_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3704_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3704_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3704_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_fst_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3702_; 
v_fst_3678_ = lean_ctor_get(v_a_3674_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_a_3674_);
if (v_isSharedCheck_3702_ == 0)
{
lean_object* v_unused_3703_; 
v_unused_3703_ = lean_ctor_get(v_a_3674_, 1);
lean_dec(v_unused_3703_);
v___x_3680_ = v_a_3674_;
v_isShared_3681_ = v_isSharedCheck_3702_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_fst_3678_);
lean_dec(v_a_3674_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3702_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
if (lean_obj_tag(v_fst_3678_) == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
lean_del_object(v___x_3676_);
v___x_3682_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3683_ = l_Lean_MessageData_ofName(v___x_3667_);
lean_inc_ref(v___x_3683_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 7);
lean_ctor_set(v___x_3680_, 1, v___x_3683_);
lean_ctor_set(v___x_3680_, 0, v___x_3682_);
v___x_3685_ = v___x_3680_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3686_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3685_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3689_ = l_Lean_indentD(v___x_3688_);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3687_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v___x_3683_);
v___x_3694_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3695_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
return v___x_3696_;
}
}
else
{
lean_object* v_val_3698_; lean_object* v___x_3700_; 
lean_del_object(v___x_3680_);
lean_dec(v___x_3667_);
lean_dec(v_stx_2407_);
v_val_3698_ = lean_ctor_get(v_fst_3678_, 0);
lean_inc(v_val_3698_);
lean_dec_ref_known(v_fst_3678_, 1);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v_val_3698_);
v___x_3700_ = v___x_3676_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_val_3698_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
else
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_dec(v___x_3667_);
lean_dec(v_stx_2407_);
v_a_3705_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3673_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3673_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
else
{
if (v___x_3665_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3713_ = l_Lean_Syntax_getArg(v___x_3664_, v___x_3626_);
lean_dec(v___x_3664_);
v___x_3714_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3715_ = l_Lean_Syntax_isOfKind(v___x_3713_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v_env_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
lean_inc_n(v_stx_2407_, 2);
v___x_3716_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3717_ = lean_st_ref_get(v___y_3662_);
v_env_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc_ref(v_env_3718_);
lean_dec(v___x_3717_);
v___x_3719_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3720_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3719_, v_env_3718_, v___x_3716_);
v___x_3721_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3722_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3720_, v___x_3721_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
lean_dec(v___x_3720_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3753_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3725_ = v___x_3722_;
v_isShared_3726_ = v_isSharedCheck_3753_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3722_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3753_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v_fst_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3751_; 
v_fst_3727_ = lean_ctor_get(v_a_3723_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_a_3723_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; 
v_unused_3752_ = lean_ctor_get(v_a_3723_, 1);
lean_dec(v_unused_3752_);
v___x_3729_ = v_a_3723_;
v_isShared_3730_ = v_isSharedCheck_3751_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_fst_3727_);
lean_dec(v_a_3723_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3751_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
if (lean_obj_tag(v_fst_3727_) == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3734_; 
lean_del_object(v___x_3725_);
v___x_3731_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3732_ = l_Lean_MessageData_ofName(v___x_3716_);
lean_inc_ref(v___x_3732_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set_tag(v___x_3729_, 7);
lean_ctor_set(v___x_3729_, 1, v___x_3732_);
lean_ctor_set(v___x_3729_, 0, v___x_3731_);
v___x_3734_ = v___x_3729_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v___x_3732_);
v___x_3734_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3735_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3738_ = l_Lean_indentD(v___x_3737_);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3736_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
lean_ctor_set(v___x_3742_, 1, v___x_3732_);
v___x_3743_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3742_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3744_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
return v___x_3745_;
}
}
else
{
lean_object* v_val_3747_; lean_object* v___x_3749_; 
lean_del_object(v___x_3729_);
lean_dec(v___x_3716_);
lean_dec(v_stx_2407_);
v_val_3747_ = lean_ctor_get(v_fst_3727_, 0);
lean_inc(v_val_3747_);
lean_dec_ref_known(v_fst_3727_, 1);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v_val_3747_);
v___x_3749_ = v___x_3725_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_val_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec(v___x_3716_);
lean_dec(v_stx_2407_);
v_a_3754_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3722_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3722_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
v___y_3629_ = v___y_3657_;
v___y_3630_ = v___y_3658_;
v___y_3631_ = v___y_3659_;
v___y_3632_ = v___y_3660_;
v___y_3633_ = v___y_3661_;
v___y_3634_ = v___y_3662_;
goto v___jp_3628_;
}
}
else
{
lean_dec(v___x_3664_);
v___y_3629_ = v___y_3657_;
v___y_3630_ = v___y_3658_;
v___y_3631_ = v___y_3659_;
v___y_3632_ = v___y_3660_;
v___y_3633_ = v___y_3661_;
v___y_3634_ = v___y_3662_;
goto v___jp_3628_;
}
}
}
else
{
lean_dec(v___x_3664_);
v___y_3629_ = v___y_3657_;
v___y_3630_ = v___y_3658_;
v___y_3631_ = v___y_3659_;
v___y_3632_ = v___y_3660_;
v___y_3633_ = v___y_3661_;
v___y_3634_ = v___y_3662_;
goto v___jp_3628_;
}
}
v___jp_3762_:
{
size_t v_sz_3764_; size_t v___x_3765_; lean_object* v___x_3766_; 
v_sz_3764_ = lean_array_size(v___y_3763_);
v___x_3765_ = ((size_t)0ULL);
v___x_3766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3764_, v___x_3765_, v___y_3763_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v_env_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
lean_inc_n(v_stx_2407_, 2);
v___x_3767_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3768_ = lean_st_ref_get(v_a_2413_);
v_env_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc_ref(v_env_3769_);
lean_dec(v___x_3768_);
v___x_3770_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3771_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3770_, v_env_3769_, v___x_3767_);
v___x_3772_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3773_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3771_, v___x_3772_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3771_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3804_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3776_ = v___x_3773_;
v_isShared_3777_ = v_isSharedCheck_3804_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3773_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3804_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v_fst_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3802_; 
v_fst_3778_ = lean_ctor_get(v_a_3774_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v_a_3774_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; 
v_unused_3803_ = lean_ctor_get(v_a_3774_, 1);
lean_dec(v_unused_3803_);
v___x_3780_ = v_a_3774_;
v_isShared_3781_ = v_isSharedCheck_3802_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_fst_3778_);
lean_dec(v_a_3774_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3802_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
if (lean_obj_tag(v_fst_3778_) == 0)
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3785_; 
lean_del_object(v___x_3776_);
v___x_3782_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3783_ = l_Lean_MessageData_ofName(v___x_3767_);
lean_inc_ref(v___x_3783_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set_tag(v___x_3780_, 7);
lean_ctor_set(v___x_3780_, 1, v___x_3783_);
lean_ctor_set(v___x_3780_, 0, v___x_3782_);
v___x_3785_ = v___x_3780_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3786_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3789_ = l_Lean_indentD(v___x_3788_);
v___x_3790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3787_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
lean_ctor_set(v___x_3793_, 1, v___x_3783_);
v___x_3794_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3795_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3796_;
}
}
else
{
lean_object* v_val_3798_; lean_object* v___x_3800_; 
lean_del_object(v___x_3780_);
lean_dec(v___x_3767_);
lean_dec(v_stx_2407_);
v_val_3798_ = lean_ctor_get(v_fst_3778_, 0);
lean_inc(v_val_3798_);
lean_dec_ref_known(v_fst_3778_, 1);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 0, v_val_3798_);
v___x_3800_ = v___x_3776_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_val_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec(v___x_3767_);
lean_dec(v_stx_2407_);
v_a_3805_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3773_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3773_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
lean_dec_ref_known(v___x_3766_, 1);
v___x_3813_ = lean_unsigned_to_nat(2u);
v___x_3814_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3813_);
v___x_3815_ = l_Lean_Syntax_isNone(v___x_3814_);
if (v___x_3815_ == 0)
{
uint8_t v___x_3816_; 
lean_inc(v___x_3814_);
v___x_3816_ = l_Lean_Syntax_matchesNull(v___x_3814_, v___x_3627_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v_env_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
lean_dec(v___x_3814_);
lean_inc_n(v_stx_2407_, 2);
v___x_3817_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3818_ = lean_st_ref_get(v_a_2413_);
v_env_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc_ref(v_env_3819_);
lean_dec(v___x_3818_);
v___x_3820_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3821_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3820_, v_env_3819_, v___x_3817_);
v___x_3822_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3823_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3821_, v___x_3822_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3821_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3854_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3826_ = v___x_3823_;
v_isShared_3827_ = v_isSharedCheck_3854_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3854_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v_fst_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3852_; 
v_fst_3828_ = lean_ctor_get(v_a_3824_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_a_3824_);
if (v_isSharedCheck_3852_ == 0)
{
lean_object* v_unused_3853_; 
v_unused_3853_ = lean_ctor_get(v_a_3824_, 1);
lean_dec(v_unused_3853_);
v___x_3830_ = v_a_3824_;
v_isShared_3831_ = v_isSharedCheck_3852_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_fst_3828_);
lean_dec(v_a_3824_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3852_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
if (lean_obj_tag(v_fst_3828_) == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3835_; 
lean_del_object(v___x_3826_);
v___x_3832_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3833_ = l_Lean_MessageData_ofName(v___x_3817_);
lean_inc_ref(v___x_3833_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set_tag(v___x_3830_, 7);
lean_ctor_set(v___x_3830_, 1, v___x_3833_);
lean_ctor_set(v___x_3830_, 0, v___x_3832_);
v___x_3835_ = v___x_3830_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3833_);
v___x_3835_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3836_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3835_);
lean_ctor_set(v___x_3837_, 1, v___x_3836_);
v___x_3838_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3839_ = l_Lean_indentD(v___x_3838_);
v___x_3840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3837_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
lean_ctor_set(v___x_3843_, 1, v___x_3833_);
v___x_3844_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3843_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3845_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3846_;
}
}
else
{
lean_object* v_val_3848_; lean_object* v___x_3850_; 
lean_del_object(v___x_3830_);
lean_dec(v___x_3817_);
lean_dec(v_stx_2407_);
v_val_3848_ = lean_ctor_get(v_fst_3828_, 0);
lean_inc(v_val_3848_);
lean_dec_ref_known(v_fst_3828_, 1);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v_val_3848_);
v___x_3850_ = v___x_3826_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_val_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v___x_3817_);
lean_dec(v_stx_2407_);
v_a_3855_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3823_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3823_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
else
{
if (v___x_3815_ == 0)
{
lean_object* v___x_3863_; lean_object* v___x_3864_; uint8_t v___x_3865_; 
v___x_3863_ = l_Lean_Syntax_getArg(v___x_3814_, v___x_3626_);
lean_dec(v___x_3814_);
v___x_3864_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3865_ = l_Lean_Syntax_isOfKind(v___x_3863_, v___x_3864_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v_env_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
lean_inc_n(v_stx_2407_, 2);
v___x_3866_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3867_ = lean_st_ref_get(v_a_2413_);
v_env_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc_ref(v_env_3868_);
lean_dec(v___x_3867_);
v___x_3869_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3870_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3869_, v_env_3868_, v___x_3866_);
v___x_3871_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3872_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3870_, v___x_3871_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3870_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3903_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3875_ = v___x_3872_;
v_isShared_3876_ = v_isSharedCheck_3903_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3872_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3903_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v_fst_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3901_; 
v_fst_3877_ = lean_ctor_get(v_a_3873_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_a_3873_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; 
v_unused_3902_ = lean_ctor_get(v_a_3873_, 1);
lean_dec(v_unused_3902_);
v___x_3879_ = v_a_3873_;
v_isShared_3880_ = v_isSharedCheck_3901_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_fst_3877_);
lean_dec(v_a_3873_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3901_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
if (lean_obj_tag(v_fst_3877_) == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3884_; 
lean_del_object(v___x_3875_);
v___x_3881_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3882_ = l_Lean_MessageData_ofName(v___x_3866_);
lean_inc_ref(v___x_3882_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set_tag(v___x_3879_, 7);
lean_ctor_set(v___x_3879_, 1, v___x_3882_);
lean_ctor_set(v___x_3879_, 0, v___x_3881_);
v___x_3884_ = v___x_3879_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3881_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3885_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3884_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3888_ = l_Lean_indentD(v___x_3887_);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3886_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
lean_ctor_set(v___x_3892_, 1, v___x_3882_);
v___x_3893_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3894_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3895_;
}
}
else
{
lean_object* v_val_3897_; lean_object* v___x_3899_; 
lean_del_object(v___x_3879_);
lean_dec(v___x_3866_);
lean_dec(v_stx_2407_);
v_val_3897_ = lean_ctor_get(v_fst_3877_, 0);
lean_inc(v_val_3897_);
lean_dec_ref_known(v_fst_3877_, 1);
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 0, v_val_3897_);
v___x_3899_ = v___x_3875_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_val_3897_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
}
else
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_dec(v___x_3866_);
lean_dec(v_stx_2407_);
v_a_3904_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3872_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3872_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
else
{
v___y_3657_ = v_a_2408_;
v___y_3658_ = v_a_2409_;
v___y_3659_ = v_a_2410_;
v___y_3660_ = v_a_2411_;
v___y_3661_ = v_a_2412_;
v___y_3662_ = v_a_2413_;
goto v___jp_3656_;
}
}
else
{
lean_dec(v___x_3814_);
v___y_3657_ = v_a_2408_;
v___y_3658_ = v_a_2409_;
v___y_3659_ = v_a_2410_;
v___y_3660_ = v_a_2411_;
v___y_3661_ = v_a_2412_;
v___y_3662_ = v_a_2413_;
goto v___jp_3656_;
}
}
}
else
{
lean_dec(v___x_3814_);
v___y_3657_ = v_a_2408_;
v___y_3658_ = v_a_2409_;
v___y_3659_ = v_a_2410_;
v___y_3660_ = v_a_2411_;
v___y_3661_ = v_a_2412_;
v___y_3662_ = v_a_2413_;
goto v___jp_3656_;
}
}
}
}
v___jp_2819_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2824_, 0, v___y_2821_);
lean_ctor_set(v___x_2824_, 1, v___y_2822_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*2, v___x_2818_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*2 + 1, v___x_2818_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*2 + 2, v___y_2820_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*2 + 3, v___y_2823_);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3923_ = lean_unsigned_to_nat(1u);
v___x_3924_ = lean_unsigned_to_nat(3u);
v___x_3925_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3924_);
lean_dec(v_stx_2407_);
v___x_3926_ = l_Lean_NameSet_empty;
v___x_3927_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3927_, 0, v___x_3923_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
lean_ctor_set_uint8(v___x_3927_, sizeof(void*)*2, v___x_2814_);
lean_ctor_set_uint8(v___x_3927_, sizeof(void*)*2 + 1, v___x_2814_);
lean_ctor_set_uint8(v___x_3927_, sizeof(void*)*2 + 2, v___x_2814_);
lean_ctor_set_uint8(v___x_3927_, sizeof(void*)*2 + 3, v___x_2814_);
v___x_3928_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3925_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3937_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3937_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3937_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3933_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3927_, v_a_3929_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3933_);
v___x_3935_ = v___x_3931_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
else
{
lean_dec_ref_known(v___x_3927_, 2);
return v___x_3928_;
}
}
}
else
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; size_t v_sz_3941_; size_t v___x_3942_; lean_object* v___x_3943_; 
v___x_3938_ = lean_unsigned_to_nat(4u);
v___x_3939_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3938_);
v___x_3940_ = l_Lean_Syntax_getArgs(v___x_3939_);
lean_dec(v___x_3939_);
v_sz_3941_ = lean_array_size(v___x_3940_);
v___x_3942_ = ((size_t)0ULL);
v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3941_, v___x_3942_, v___x_3940_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v_env_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
lean_inc_n(v_stx_2407_, 2);
v___x_3944_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_3945_ = lean_st_ref_get(v_a_2413_);
v_env_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc_ref(v_env_3946_);
lean_dec(v___x_3945_);
v___x_3947_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3948_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3947_, v_env_3946_, v___x_3944_);
v___x_3949_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3950_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_3948_, v___x_3949_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_3948_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3981_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3953_ = v___x_3950_;
v_isShared_3954_ = v_isSharedCheck_3981_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3950_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3981_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v_fst_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3979_; 
v_fst_3955_ = lean_ctor_get(v_a_3951_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v_a_3951_);
if (v_isSharedCheck_3979_ == 0)
{
lean_object* v_unused_3980_; 
v_unused_3980_ = lean_ctor_get(v_a_3951_, 1);
lean_dec(v_unused_3980_);
v___x_3957_ = v_a_3951_;
v_isShared_3958_ = v_isSharedCheck_3979_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_fst_3955_);
lean_dec(v_a_3951_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3979_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
if (lean_obj_tag(v_fst_3955_) == 0)
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3962_; 
lean_del_object(v___x_3953_);
v___x_3959_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3960_ = l_Lean_MessageData_ofName(v___x_3944_);
lean_inc_ref(v___x_3960_);
if (v_isShared_3958_ == 0)
{
lean_ctor_set_tag(v___x_3957_, 7);
lean_ctor_set(v___x_3957_, 1, v___x_3960_);
lean_ctor_set(v___x_3957_, 0, v___x_3959_);
v___x_3962_ = v___x_3957_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3963_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3962_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_3966_ = l_Lean_indentD(v___x_3965_);
v___x_3967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3964_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
lean_ctor_set(v___x_3970_, 1, v___x_3960_);
v___x_3971_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3970_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3972_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_3973_;
}
}
else
{
lean_object* v_val_3975_; lean_object* v___x_3977_; 
lean_del_object(v___x_3957_);
lean_dec(v___x_3944_);
lean_dec(v_stx_2407_);
v_val_3975_ = lean_ctor_get(v_fst_3955_, 0);
lean_inc(v_val_3975_);
lean_dec_ref_known(v_fst_3955_, 1);
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 0, v_val_3975_);
v___x_3977_ = v___x_3953_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_val_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec(v___x_3944_);
lean_dec(v_stx_2407_);
v_a_3982_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3950_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3950_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
else
{
lean_object* v_val_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4077_; 
v_val_3990_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_3992_ = v___x_3943_;
v_isShared_3993_ = v_isSharedCheck_4077_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_val_3990_);
lean_dec(v___x_3943_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4077_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v_elseSeq_x3f_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___x_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; 
v___x_3994_ = lean_unsigned_to_nat(3u);
v___x_3995_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_3994_);
v___x_4020_ = lean_unsigned_to_nat(5u);
v___x_4021_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4020_);
v___x_4022_ = l_Lean_Syntax_isNone(v___x_4021_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; uint8_t v___x_4024_; 
v___x_4023_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4021_);
v___x_4024_ = l_Lean_Syntax_matchesNull(v___x_4021_, v___x_4023_);
if (v___x_4024_ == 0)
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v_env_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
lean_dec(v___x_4021_);
lean_dec(v___x_3995_);
lean_del_object(v___x_3992_);
lean_dec(v_val_3990_);
lean_inc_n(v_stx_2407_, 2);
v___x_4025_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4026_ = lean_st_ref_get(v_a_2413_);
v_env_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc_ref(v_env_4027_);
lean_dec(v___x_4026_);
v___x_4028_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4029_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4028_, v_env_4027_, v___x_4025_);
v___x_4030_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4031_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4029_, v___x_4030_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4029_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4062_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4034_ = v___x_4031_;
v_isShared_4035_ = v_isSharedCheck_4062_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4031_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4062_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v_fst_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4060_; 
v_fst_4036_ = lean_ctor_get(v_a_4032_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_a_4032_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v_a_4032_, 1);
lean_dec(v_unused_4061_);
v___x_4038_ = v_a_4032_;
v_isShared_4039_ = v_isSharedCheck_4060_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_fst_4036_);
lean_dec(v_a_4032_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4060_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
if (lean_obj_tag(v_fst_4036_) == 0)
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4043_; 
lean_del_object(v___x_4034_);
v___x_4040_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4041_ = l_Lean_MessageData_ofName(v___x_4025_);
lean_inc_ref(v___x_4041_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set_tag(v___x_4038_, 7);
lean_ctor_set(v___x_4038_, 1, v___x_4041_);
lean_ctor_set(v___x_4038_, 0, v___x_4040_);
v___x_4043_ = v___x_4038_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4040_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v___x_4041_);
v___x_4043_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4044_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4047_ = l_Lean_indentD(v___x_4046_);
v___x_4048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4045_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
v___x_4049_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4048_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
v___x_4051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
lean_ctor_set(v___x_4051_, 1, v___x_4041_);
v___x_4052_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4053_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4054_;
}
}
else
{
lean_object* v_val_4056_; lean_object* v___x_4058_; 
lean_del_object(v___x_4038_);
lean_dec(v___x_4025_);
lean_dec(v_stx_2407_);
v_val_4056_ = lean_ctor_get(v_fst_4036_, 0);
lean_inc(v_val_4056_);
lean_dec_ref_known(v_fst_4036_, 1);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v_val_4056_);
v___x_4058_ = v___x_4034_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_val_4056_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec(v___x_4025_);
lean_dec(v_stx_2407_);
v_a_4063_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4031_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4031_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
else
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
lean_dec(v_stx_2407_);
v___x_4071_ = lean_unsigned_to_nat(1u);
v___x_4072_ = l_Lean_Syntax_getArg(v___x_4021_, v___x_4071_);
lean_dec(v___x_4021_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_4072_);
v___x_4074_ = v___x_3992_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
v_elseSeq_x3f_3997_ = v___x_4074_;
v___y_3998_ = v_a_2408_;
v___y_3999_ = v_a_2409_;
v___y_4000_ = v_a_2410_;
v___y_4001_ = v_a_2411_;
v___y_4002_ = v_a_2412_;
v___y_4003_ = v_a_2413_;
goto v___jp_3996_;
}
}
}
else
{
lean_object* v___x_4076_; 
lean_dec(v___x_4021_);
lean_del_object(v___x_3992_);
lean_dec(v_stx_2407_);
v___x_4076_ = lean_box(0);
v_elseSeq_x3f_3997_ = v___x_4076_;
v___y_3998_ = v_a_2408_;
v___y_3999_ = v_a_2409_;
v___y_4000_ = v_a_2410_;
v___y_4001_ = v_a_2411_;
v___y_4002_ = v_a_2412_;
v___y_4003_ = v_a_2413_;
goto v___jp_3996_;
}
v___jp_3996_:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4006_; size_t v_sz_4007_; lean_object* v___x_4008_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v___x_4006_ = l_Array_reverse___redArg(v_val_3990_);
v_sz_4007_ = lean_array_size(v___x_4006_);
v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_4006_, v_sz_4007_, v___x_3942_, v_a_4005_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec_ref(v___x_4006_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3995_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4019_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4013_ = v___x_4010_;
v_isShared_4014_ = v_isSharedCheck_4019_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4010_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4019_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4015_; lean_object* v___x_4017_; 
v___x_4015_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_4011_, v_a_4009_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4015_);
v___x_4017_ = v___x_4013_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4015_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
else
{
lean_dec(v_a_4009_);
return v___x_4010_;
}
}
else
{
lean_dec(v___x_3995_);
return v___x_4008_;
}
}
else
{
lean_dec(v___x_3995_);
lean_dec(v_val_3990_);
return v___x_4004_;
}
}
}
}
}
}
else
{
lean_object* v___x_4078_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___x_4142_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___x_4249_; uint8_t v___x_4250_; 
v___x_4078_ = lean_unsigned_to_nat(0u);
v___x_4142_ = lean_unsigned_to_nat(1u);
v___x_4249_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4142_);
v___x_4250_ = l_Lean_Syntax_isNone(v___x_4249_);
if (v___x_4250_ == 0)
{
uint8_t v___x_4251_; 
lean_inc(v___x_4249_);
v___x_4251_ = l_Lean_Syntax_matchesNull(v___x_4249_, v___x_4142_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v_env_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
lean_dec(v___x_4249_);
lean_inc_n(v_stx_2407_, 2);
v___x_4252_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4253_ = lean_st_ref_get(v_a_2413_);
v_env_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc_ref(v_env_4254_);
lean_dec(v___x_4253_);
v___x_4255_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4256_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4255_, v_env_4254_, v___x_4252_);
v___x_4257_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4258_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4256_, v___x_4257_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4256_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4289_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4261_ = v___x_4258_;
v_isShared_4262_ = v_isSharedCheck_4289_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4258_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4289_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v_fst_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4287_; 
v_fst_4263_ = lean_ctor_get(v_a_4259_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v_a_4259_);
if (v_isSharedCheck_4287_ == 0)
{
lean_object* v_unused_4288_; 
v_unused_4288_ = lean_ctor_get(v_a_4259_, 1);
lean_dec(v_unused_4288_);
v___x_4265_ = v_a_4259_;
v_isShared_4266_ = v_isSharedCheck_4287_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_fst_4263_);
lean_dec(v_a_4259_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4287_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
if (lean_obj_tag(v_fst_4263_) == 0)
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4270_; 
lean_del_object(v___x_4261_);
v___x_4267_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4268_ = l_Lean_MessageData_ofName(v___x_4252_);
lean_inc_ref(v___x_4268_);
if (v_isShared_4266_ == 0)
{
lean_ctor_set_tag(v___x_4265_, 7);
lean_ctor_set(v___x_4265_, 1, v___x_4268_);
lean_ctor_set(v___x_4265_, 0, v___x_4267_);
v___x_4270_ = v___x_4265_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4267_);
lean_ctor_set(v_reuseFailAlloc_4282_, 1, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4271_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4274_ = l_Lean_indentD(v___x_4273_);
v___x_4275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4272_);
lean_ctor_set(v___x_4275_, 1, v___x_4274_);
v___x_4276_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4275_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
lean_ctor_set(v___x_4278_, 1, v___x_4268_);
v___x_4279_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4278_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
v___x_4281_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4280_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4281_;
}
}
else
{
lean_object* v_val_4283_; lean_object* v___x_4285_; 
lean_del_object(v___x_4265_);
lean_dec(v___x_4252_);
lean_dec(v_stx_2407_);
v_val_4283_ = lean_ctor_get(v_fst_4263_, 0);
lean_inc(v_val_4283_);
lean_dec_ref_known(v_fst_4263_, 1);
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 0, v_val_4283_);
v___x_4285_ = v___x_4261_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_val_4283_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
lean_dec(v___x_4252_);
lean_dec(v_stx_2407_);
v_a_4290_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4258_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4258_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
else
{
lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4298_ = l_Lean_Syntax_getArg(v___x_4249_, v___x_4078_);
lean_dec(v___x_4249_);
v___x_4299_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4300_ = l_Lean_Syntax_isOfKind(v___x_4298_, v___x_4299_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v_env_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
lean_inc_n(v_stx_2407_, 2);
v___x_4301_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4302_ = lean_st_ref_get(v_a_2413_);
v_env_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc_ref(v_env_4303_);
lean_dec(v___x_4302_);
v___x_4304_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4305_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4304_, v_env_4303_, v___x_4301_);
v___x_4306_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4307_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4305_, v___x_4306_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4305_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4338_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4310_ = v___x_4307_;
v_isShared_4311_ = v_isSharedCheck_4338_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4307_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4338_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v_fst_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4336_; 
v_fst_4312_ = lean_ctor_get(v_a_4308_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v_a_4308_);
if (v_isSharedCheck_4336_ == 0)
{
lean_object* v_unused_4337_; 
v_unused_4337_ = lean_ctor_get(v_a_4308_, 1);
lean_dec(v_unused_4337_);
v___x_4314_ = v_a_4308_;
v_isShared_4315_ = v_isSharedCheck_4336_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_fst_4312_);
lean_dec(v_a_4308_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4336_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
if (lean_obj_tag(v_fst_4312_) == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
lean_del_object(v___x_4310_);
v___x_4316_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4317_ = l_Lean_MessageData_ofName(v___x_4301_);
lean_inc_ref(v___x_4317_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 7);
lean_ctor_set(v___x_4314_, 1, v___x_4317_);
lean_ctor_set(v___x_4314_, 0, v___x_4316_);
v___x_4319_ = v___x_4314_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4316_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4320_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
v___x_4322_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4323_ = l_Lean_indentD(v___x_4322_);
v___x_4324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4321_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4324_);
lean_ctor_set(v___x_4326_, 1, v___x_4325_);
v___x_4327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
lean_ctor_set(v___x_4327_, 1, v___x_4317_);
v___x_4328_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4329_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4330_;
}
}
else
{
lean_object* v_val_4332_; lean_object* v___x_4334_; 
lean_del_object(v___x_4314_);
lean_dec(v___x_4301_);
lean_dec(v_stx_2407_);
v_val_4332_ = lean_ctor_get(v_fst_4312_, 0);
lean_inc(v_val_4332_);
lean_dec_ref_known(v_fst_4312_, 1);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 0, v_val_4332_);
v___x_4334_ = v___x_4310_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_val_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v___x_4301_);
lean_dec(v_stx_2407_);
v_a_4339_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4307_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4307_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
v___y_4144_ = v_a_2408_;
v___y_4145_ = v_a_2409_;
v___y_4146_ = v_a_2410_;
v___y_4147_ = v_a_2411_;
v___y_4148_ = v_a_2412_;
v___y_4149_ = v_a_2413_;
goto v___jp_4143_;
}
}
}
else
{
lean_dec(v___x_4249_);
v___y_4144_ = v_a_2408_;
v___y_4145_ = v_a_2409_;
v___y_4146_ = v_a_2410_;
v___y_4147_ = v_a_2411_;
v___y_4148_ = v_a_2412_;
v___y_4149_ = v_a_2413_;
goto v___jp_4143_;
}
v___jp_4079_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; 
v___x_4086_ = lean_unsigned_to_nat(6u);
v___x_4087_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4086_);
v___x_4088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_4087_);
v___x_4089_ = l_Lean_Syntax_isOfKind(v___x_4087_, v___x_4088_);
if (v___x_4089_ == 0)
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v_env_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_dec(v___x_4087_);
lean_inc_n(v_stx_2407_, 2);
v___x_4090_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4091_ = lean_st_ref_get(v___y_4085_);
v_env_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc_ref(v_env_4092_);
lean_dec(v___x_4091_);
v___x_4093_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4094_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4093_, v_env_4092_, v___x_4090_);
v___x_4095_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4096_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4094_, v___x_4095_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___x_4094_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4127_; 
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4099_ = v___x_4096_;
v_isShared_4100_ = v_isSharedCheck_4127_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4096_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4127_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v_fst_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4125_; 
v_fst_4101_ = lean_ctor_get(v_a_4097_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_a_4097_);
if (v_isSharedCheck_4125_ == 0)
{
lean_object* v_unused_4126_; 
v_unused_4126_ = lean_ctor_get(v_a_4097_, 1);
lean_dec(v_unused_4126_);
v___x_4103_ = v_a_4097_;
v_isShared_4104_ = v_isSharedCheck_4125_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_fst_4101_);
lean_dec(v_a_4097_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4125_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
if (lean_obj_tag(v_fst_4101_) == 0)
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
lean_del_object(v___x_4099_);
v___x_4105_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4106_ = l_Lean_MessageData_ofName(v___x_4090_);
lean_inc_ref(v___x_4106_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set_tag(v___x_4103_, 7);
lean_ctor_set(v___x_4103_, 1, v___x_4106_);
lean_ctor_set(v___x_4103_, 0, v___x_4105_);
v___x_4108_ = v___x_4103_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4105_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4109_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4112_ = l_Lean_indentD(v___x_4111_);
v___x_4113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4110_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4113_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
lean_ctor_set(v___x_4116_, 1, v___x_4106_);
v___x_4117_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4116_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4118_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
return v___x_4119_;
}
}
else
{
lean_object* v_val_4121_; lean_object* v___x_4123_; 
lean_del_object(v___x_4103_);
lean_dec(v___x_4090_);
lean_dec(v_stx_2407_);
v_val_4121_ = lean_ctor_get(v_fst_4101_, 0);
lean_inc(v_val_4121_);
lean_dec_ref_known(v_fst_4101_, 1);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v_val_4121_);
v___x_4123_ = v___x_4099_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_val_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
else
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
lean_dec(v___x_4090_);
lean_dec(v_stx_2407_);
v_a_4128_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_4096_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4096_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; size_t v_sz_4139_; size_t v___x_4140_; lean_object* v___x_4141_; 
lean_dec(v_stx_2407_);
v___x_4136_ = l_Lean_Syntax_getArg(v___x_4087_, v___x_4078_);
lean_dec(v___x_4087_);
v___x_4137_ = l_Lean_Syntax_getArgs(v___x_4136_);
lean_dec(v___x_4136_);
v___x_4138_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_4139_ = lean_array_size(v___x_4137_);
v___x_4140_ = ((size_t)0ULL);
v___x_4141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2810_, v___x_4137_, v_sz_4139_, v___x_4140_, v___x_4138_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec_ref(v___x_4137_);
return v___x_4141_;
}
}
v___jp_4143_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; uint8_t v___x_4152_; 
v___x_4150_ = lean_unsigned_to_nat(2u);
v___x_4151_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4150_);
v___x_4152_ = l_Lean_Syntax_isNone(v___x_4151_);
if (v___x_4152_ == 0)
{
uint8_t v___x_4153_; 
lean_inc(v___x_4151_);
v___x_4153_ = l_Lean_Syntax_matchesNull(v___x_4151_, v___x_4142_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v_env_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_dec(v___x_4151_);
lean_inc_n(v_stx_2407_, 2);
v___x_4154_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4155_ = lean_st_ref_get(v___y_4149_);
v_env_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc_ref(v_env_4156_);
lean_dec(v___x_4155_);
v___x_4157_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4158_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4157_, v_env_4156_, v___x_4154_);
v___x_4159_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4160_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4158_, v___x_4159_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___x_4158_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4191_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4163_ = v___x_4160_;
v_isShared_4164_ = v_isSharedCheck_4191_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4191_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v_fst_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4189_; 
v_fst_4165_ = lean_ctor_get(v_a_4161_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_a_4161_);
if (v_isSharedCheck_4189_ == 0)
{
lean_object* v_unused_4190_; 
v_unused_4190_ = lean_ctor_get(v_a_4161_, 1);
lean_dec(v_unused_4190_);
v___x_4167_ = v_a_4161_;
v_isShared_4168_ = v_isSharedCheck_4189_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_fst_4165_);
lean_dec(v_a_4161_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4189_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
if (lean_obj_tag(v_fst_4165_) == 0)
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4172_; 
lean_del_object(v___x_4163_);
v___x_4169_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4170_ = l_Lean_MessageData_ofName(v___x_4154_);
lean_inc_ref(v___x_4170_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set_tag(v___x_4167_, 7);
lean_ctor_set(v___x_4167_, 1, v___x_4170_);
lean_ctor_set(v___x_4167_, 0, v___x_4169_);
v___x_4172_ = v___x_4167_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4169_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4173_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4172_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
v___x_4175_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4176_ = l_Lean_indentD(v___x_4175_);
v___x_4177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4174_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4177_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set(v___x_4180_, 1, v___x_4170_);
v___x_4181_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4180_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
v___x_4183_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4182_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4183_;
}
}
else
{
lean_object* v_val_4185_; lean_object* v___x_4187_; 
lean_del_object(v___x_4167_);
lean_dec(v___x_4154_);
lean_dec(v_stx_2407_);
v_val_4185_ = lean_ctor_get(v_fst_4165_, 0);
lean_inc(v_val_4185_);
lean_dec_ref_known(v_fst_4165_, 1);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v_val_4185_);
v___x_4187_ = v___x_4163_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_val_4185_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec(v___x_4154_);
lean_dec(v_stx_2407_);
v_a_4192_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4160_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4160_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v___x_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; 
v___x_4200_ = l_Lean_Syntax_getArg(v___x_4151_, v___x_4078_);
lean_dec(v___x_4151_);
v___x_4201_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
v___x_4202_ = l_Lean_Syntax_isOfKind(v___x_4200_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v_env_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
lean_inc_n(v_stx_2407_, 2);
v___x_4203_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4204_ = lean_st_ref_get(v___y_4149_);
v_env_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc_ref(v_env_4205_);
lean_dec(v___x_4204_);
v___x_4206_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4207_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4206_, v_env_4205_, v___x_4203_);
v___x_4208_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4209_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4207_, v___x_4208_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___x_4207_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4240_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4212_ = v___x_4209_;
v_isShared_4213_ = v_isSharedCheck_4240_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4209_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4240_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v_fst_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4238_; 
v_fst_4214_ = lean_ctor_get(v_a_4210_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v_a_4210_);
if (v_isSharedCheck_4238_ == 0)
{
lean_object* v_unused_4239_; 
v_unused_4239_ = lean_ctor_get(v_a_4210_, 1);
lean_dec(v_unused_4239_);
v___x_4216_ = v_a_4210_;
v_isShared_4217_ = v_isSharedCheck_4238_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_fst_4214_);
lean_dec(v_a_4210_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4238_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
if (lean_obj_tag(v_fst_4214_) == 0)
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4221_; 
lean_del_object(v___x_4212_);
v___x_4218_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4219_ = l_Lean_MessageData_ofName(v___x_4203_);
lean_inc_ref(v___x_4219_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set_tag(v___x_4216_, 7);
lean_ctor_set(v___x_4216_, 1, v___x_4219_);
lean_ctor_set(v___x_4216_, 0, v___x_4218_);
v___x_4221_ = v___x_4216_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4218_);
lean_ctor_set(v_reuseFailAlloc_4233_, 1, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4222_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4221_);
lean_ctor_set(v___x_4223_, 1, v___x_4222_);
v___x_4224_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4225_ = l_Lean_indentD(v___x_4224_);
v___x_4226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4223_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4226_);
lean_ctor_set(v___x_4228_, 1, v___x_4227_);
v___x_4229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4228_);
lean_ctor_set(v___x_4229_, 1, v___x_4219_);
v___x_4230_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4229_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
v___x_4232_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4231_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4232_;
}
}
else
{
lean_object* v_val_4234_; lean_object* v___x_4236_; 
lean_del_object(v___x_4216_);
lean_dec(v___x_4203_);
lean_dec(v_stx_2407_);
v_val_4234_ = lean_ctor_get(v_fst_4214_, 0);
lean_inc(v_val_4234_);
lean_dec_ref_known(v_fst_4214_, 1);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v_val_4234_);
v___x_4236_ = v___x_4212_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_val_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec(v___x_4203_);
lean_dec(v_stx_2407_);
v_a_4241_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4209_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4209_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
else
{
v___y_4080_ = v___y_4144_;
v___y_4081_ = v___y_4145_;
v___y_4082_ = v___y_4146_;
v___y_4083_ = v___y_4147_;
v___y_4084_ = v___y_4148_;
v___y_4085_ = v___y_4149_;
goto v___jp_4079_;
}
}
}
else
{
lean_dec(v___x_4151_);
v___y_4080_ = v___y_4144_;
v___y_4081_ = v___y_4145_;
v___y_4082_ = v___y_4146_;
v___y_4083_ = v___y_4147_;
v___y_4084_ = v___y_4148_;
v___y_4085_ = v___y_4149_;
goto v___jp_4079_;
}
}
}
}
else
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4347_ = lean_unsigned_to_nat(0u);
v___x_4348_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4347_);
if (v___x_2808_ == 0)
{
lean_object* v___x_4349_; uint8_t v___x_4350_; 
v___x_4349_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_4348_);
v___x_4350_ = l_Lean_Syntax_isOfKind(v___x_4348_, v___x_4349_);
if (v___x_4350_ == 0)
{
if (v___x_2808_ == 0)
{
lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4351_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_4348_);
v___x_4352_ = l_Lean_Syntax_isOfKind(v___x_4348_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v_env_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
lean_dec(v___x_4348_);
lean_inc_n(v_stx_2407_, 2);
v___x_4353_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4354_ = lean_st_ref_get(v_a_2413_);
v_env_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc_ref(v_env_4355_);
lean_dec(v___x_4354_);
v___x_4356_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4357_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4356_, v_env_4355_, v___x_4353_);
v___x_4358_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4359_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4357_, v___x_4358_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4357_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4390_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4362_ = v___x_4359_;
v_isShared_4363_ = v_isSharedCheck_4390_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4359_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4390_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v_fst_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4388_; 
v_fst_4364_ = lean_ctor_get(v_a_4360_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_a_4360_);
if (v_isSharedCheck_4388_ == 0)
{
lean_object* v_unused_4389_; 
v_unused_4389_ = lean_ctor_get(v_a_4360_, 1);
lean_dec(v_unused_4389_);
v___x_4366_ = v_a_4360_;
v_isShared_4367_ = v_isSharedCheck_4388_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_fst_4364_);
lean_dec(v_a_4360_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4388_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
if (lean_obj_tag(v_fst_4364_) == 0)
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4371_; 
lean_del_object(v___x_4362_);
v___x_4368_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4369_ = l_Lean_MessageData_ofName(v___x_4353_);
lean_inc_ref(v___x_4369_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set_tag(v___x_4366_, 7);
lean_ctor_set(v___x_4366_, 1, v___x_4369_);
lean_ctor_set(v___x_4366_, 0, v___x_4368_);
v___x_4371_ = v___x_4366_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4368_);
lean_ctor_set(v_reuseFailAlloc_4383_, 1, v___x_4369_);
v___x_4371_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4372_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4371_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4375_ = l_Lean_indentD(v___x_4374_);
v___x_4376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4373_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
v___x_4377_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4376_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
lean_ctor_set(v___x_4379_, 1, v___x_4369_);
v___x_4380_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4379_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
v___x_4382_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4381_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4382_;
}
}
else
{
lean_object* v_val_4384_; lean_object* v___x_4386_; 
lean_del_object(v___x_4366_);
lean_dec(v___x_4353_);
lean_dec(v_stx_2407_);
v_val_4384_ = lean_ctor_get(v_fst_4364_, 0);
lean_inc(v_val_4384_);
lean_dec_ref_known(v_fst_4364_, 1);
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 0, v_val_4384_);
v___x_4386_ = v___x_4362_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_val_4384_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec(v___x_4353_);
lean_dec(v_stx_2407_);
v_a_4391_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4359_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4359_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
else
{
lean_object* v___x_4399_; 
lean_dec(v_stx_2407_);
v___x_4399_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2497_, v___x_4348_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4399_;
}
}
else
{
lean_object* v___x_4400_; 
lean_dec(v_stx_2407_);
v___x_4400_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2497_, v___x_4348_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4400_;
}
}
else
{
lean_object* v___x_4401_; 
lean_dec(v_stx_2407_);
v___x_4401_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2497_, v___x_4348_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4401_;
}
}
else
{
lean_object* v___x_4402_; 
lean_dec(v_stx_2407_);
v___x_4402_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2497_, v___x_4348_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4402_;
}
}
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_unsigned_to_nat(0u);
v___x_4404_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4403_);
if (v___x_2806_ == 0)
{
lean_object* v___x_4431_; uint8_t v___x_4432_; 
v___x_4431_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84));
lean_inc(v___x_4404_);
v___x_4432_ = l_Lean_Syntax_isOfKind(v___x_4404_, v___x_4431_);
if (v___x_4432_ == 0)
{
if (v___x_2806_ == 0)
{
lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4433_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86));
lean_inc(v___x_4404_);
v___x_4434_ = l_Lean_Syntax_isOfKind(v___x_4404_, v___x_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v_env_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_dec(v___x_4404_);
lean_inc_n(v_stx_2407_, 2);
v___x_4435_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4436_ = lean_st_ref_get(v_a_2413_);
v_env_4437_ = lean_ctor_get(v___x_4436_, 0);
lean_inc_ref(v_env_4437_);
lean_dec(v___x_4436_);
v___x_4438_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4439_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4438_, v_env_4437_, v___x_4435_);
v___x_4440_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4441_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4439_, v___x_4440_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4439_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4472_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4444_ = v___x_4441_;
v_isShared_4445_ = v_isSharedCheck_4472_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4441_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4472_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v_fst_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4470_; 
v_fst_4446_ = lean_ctor_get(v_a_4442_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v_a_4442_);
if (v_isSharedCheck_4470_ == 0)
{
lean_object* v_unused_4471_; 
v_unused_4471_ = lean_ctor_get(v_a_4442_, 1);
lean_dec(v_unused_4471_);
v___x_4448_ = v_a_4442_;
v_isShared_4449_ = v_isSharedCheck_4470_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_fst_4446_);
lean_dec(v_a_4442_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4470_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
if (lean_obj_tag(v_fst_4446_) == 0)
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4453_; 
lean_del_object(v___x_4444_);
v___x_4450_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4451_ = l_Lean_MessageData_ofName(v___x_4435_);
lean_inc_ref(v___x_4451_);
if (v_isShared_4449_ == 0)
{
lean_ctor_set_tag(v___x_4448_, 7);
lean_ctor_set(v___x_4448_, 1, v___x_4451_);
lean_ctor_set(v___x_4448_, 0, v___x_4450_);
v___x_4453_ = v___x_4448_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4450_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v___x_4451_);
v___x_4453_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4454_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4453_);
lean_ctor_set(v___x_4455_, 1, v___x_4454_);
v___x_4456_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4457_ = l_Lean_indentD(v___x_4456_);
v___x_4458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4455_);
lean_ctor_set(v___x_4458_, 1, v___x_4457_);
v___x_4459_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4458_);
lean_ctor_set(v___x_4460_, 1, v___x_4459_);
v___x_4461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
lean_ctor_set(v___x_4461_, 1, v___x_4451_);
v___x_4462_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4461_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
v___x_4464_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4463_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4464_;
}
}
else
{
lean_object* v_val_4466_; lean_object* v___x_4468_; 
lean_del_object(v___x_4448_);
lean_dec(v___x_4435_);
lean_dec(v_stx_2407_);
v_val_4466_ = lean_ctor_get(v_fst_4446_, 0);
lean_inc(v_val_4466_);
lean_dec_ref_known(v_fst_4446_, 1);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 0, v_val_4466_);
v___x_4468_ = v___x_4444_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_val_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec(v___x_4435_);
lean_dec(v_stx_2407_);
v_a_4473_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4441_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4441_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_4405_;
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_4405_;
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_4418_;
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_4418_;
}
v___jp_4405_:
{
lean_object* v___x_4406_; 
v___x_4406_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_4404_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4404_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
v___x_4408_ = lean_box(0);
v___x_4409_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4407_, v___x_4408_, v___x_4408_, v___x_4408_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4409_;
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
v_a_4410_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4406_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4406_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
v___jp_4418_:
{
lean_object* v___x_4419_; 
v___x_4419_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_4404_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4404_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4419_, 1);
v___x_4421_ = lean_box(0);
v___x_4422_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4420_, v___x_4421_, v___x_4421_, v___x_4421_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4422_;
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
v_a_4423_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4419_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4419_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
}
else
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; uint8_t v___x_4484_; 
v___x_4481_ = lean_unsigned_to_nat(0u);
v___x_4482_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4481_);
v___x_4483_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88));
lean_inc(v___x_4482_);
v___x_4484_ = l_Lean_Syntax_isOfKind(v___x_4482_, v___x_4483_);
if (v___x_4484_ == 0)
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v_env_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
lean_dec(v___x_4482_);
lean_inc_n(v_stx_2407_, 2);
v___x_4485_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4486_ = lean_st_ref_get(v_a_2413_);
v_env_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc_ref(v_env_4487_);
lean_dec(v___x_4486_);
v___x_4488_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4489_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4488_, v_env_4487_, v___x_4485_);
v___x_4490_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4491_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4489_, v___x_4490_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4489_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4522_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4494_ = v___x_4491_;
v_isShared_4495_ = v_isSharedCheck_4522_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4491_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4522_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v_fst_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4520_; 
v_fst_4496_ = lean_ctor_get(v_a_4492_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_a_4492_);
if (v_isSharedCheck_4520_ == 0)
{
lean_object* v_unused_4521_; 
v_unused_4521_ = lean_ctor_get(v_a_4492_, 1);
lean_dec(v_unused_4521_);
v___x_4498_ = v_a_4492_;
v_isShared_4499_ = v_isSharedCheck_4520_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_fst_4496_);
lean_dec(v_a_4492_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4520_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
if (lean_obj_tag(v_fst_4496_) == 0)
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4503_; 
lean_del_object(v___x_4494_);
v___x_4500_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4501_ = l_Lean_MessageData_ofName(v___x_4485_);
lean_inc_ref(v___x_4501_);
if (v_isShared_4499_ == 0)
{
lean_ctor_set_tag(v___x_4498_, 7);
lean_ctor_set(v___x_4498_, 1, v___x_4501_);
lean_ctor_set(v___x_4498_, 0, v___x_4500_);
v___x_4503_ = v___x_4498_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4500_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4504_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4503_);
lean_ctor_set(v___x_4505_, 1, v___x_4504_);
v___x_4506_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4507_ = l_Lean_indentD(v___x_4506_);
v___x_4508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4505_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
v___x_4509_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
lean_ctor_set(v___x_4511_, 1, v___x_4501_);
v___x_4512_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4511_);
lean_ctor_set(v___x_4513_, 1, v___x_4512_);
v___x_4514_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4513_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4514_;
}
}
else
{
lean_object* v_val_4516_; lean_object* v___x_4518_; 
lean_del_object(v___x_4498_);
lean_dec(v___x_4485_);
lean_dec(v_stx_2407_);
v_val_4516_ = lean_ctor_get(v_fst_4496_, 0);
lean_inc(v_val_4516_);
lean_dec_ref_known(v_fst_4496_, 1);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v_val_4516_);
v___x_4518_ = v___x_4494_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_val_4516_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_dec(v___x_4485_);
lean_dec(v_stx_2407_);
v_a_4523_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4491_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4491_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
else
{
lean_object* v___x_4531_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___x_4637_; uint8_t v___x_4638_; 
v___x_4531_ = lean_unsigned_to_nat(1u);
v___x_4637_ = l_Lean_Syntax_getArg(v___x_4482_, v___x_4531_);
lean_dec(v___x_4482_);
v___x_4638_ = l_Lean_Syntax_isNone(v___x_4637_);
if (v___x_4638_ == 0)
{
uint8_t v___x_4639_; 
v___x_4639_ = l_Lean_Syntax_matchesNull(v___x_4637_, v___x_4531_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v_env_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
lean_inc_n(v_stx_2407_, 2);
v___x_4640_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4641_ = lean_st_ref_get(v_a_2413_);
v_env_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc_ref(v_env_4642_);
lean_dec(v___x_4641_);
v___x_4643_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4644_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4643_, v_env_4642_, v___x_4640_);
v___x_4645_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4646_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4644_, v___x_4645_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4644_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4677_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4649_ = v___x_4646_;
v_isShared_4650_ = v_isSharedCheck_4677_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4646_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4677_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v_fst_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4675_; 
v_fst_4651_ = lean_ctor_get(v_a_4647_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v_a_4647_);
if (v_isSharedCheck_4675_ == 0)
{
lean_object* v_unused_4676_; 
v_unused_4676_ = lean_ctor_get(v_a_4647_, 1);
lean_dec(v_unused_4676_);
v___x_4653_ = v_a_4647_;
v_isShared_4654_ = v_isSharedCheck_4675_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_fst_4651_);
lean_dec(v_a_4647_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4675_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
if (lean_obj_tag(v_fst_4651_) == 0)
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4658_; 
lean_del_object(v___x_4649_);
v___x_4655_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4656_ = l_Lean_MessageData_ofName(v___x_4640_);
lean_inc_ref(v___x_4656_);
if (v_isShared_4654_ == 0)
{
lean_ctor_set_tag(v___x_4653_, 7);
lean_ctor_set(v___x_4653_, 1, v___x_4656_);
lean_ctor_set(v___x_4653_, 0, v___x_4655_);
v___x_4658_ = v___x_4653_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4670_, 1, v___x_4656_);
v___x_4658_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4659_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4658_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
v___x_4661_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4662_ = l_Lean_indentD(v___x_4661_);
v___x_4663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4660_);
lean_ctor_set(v___x_4663_, 1, v___x_4662_);
v___x_4664_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4663_);
lean_ctor_set(v___x_4665_, 1, v___x_4664_);
v___x_4666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
lean_ctor_set(v___x_4666_, 1, v___x_4656_);
v___x_4667_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4666_);
lean_ctor_set(v___x_4668_, 1, v___x_4667_);
v___x_4669_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4668_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4669_;
}
}
else
{
lean_object* v_val_4671_; lean_object* v___x_4673_; 
lean_del_object(v___x_4653_);
lean_dec(v___x_4640_);
lean_dec(v_stx_2407_);
v_val_4671_ = lean_ctor_get(v_fst_4651_, 0);
lean_inc(v_val_4671_);
lean_dec_ref_known(v_fst_4651_, 1);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 0, v_val_4671_);
v___x_4673_ = v___x_4649_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_val_4671_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
lean_dec(v___x_4640_);
lean_dec(v_stx_2407_);
v_a_4678_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4646_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4646_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
else
{
v___y_4533_ = v_a_2408_;
v___y_4534_ = v_a_2409_;
v___y_4535_ = v_a_2410_;
v___y_4536_ = v_a_2411_;
v___y_4537_ = v_a_2412_;
v___y_4538_ = v_a_2413_;
goto v___jp_4532_;
}
}
else
{
lean_dec(v___x_4637_);
v___y_4533_ = v_a_2408_;
v___y_4534_ = v_a_2409_;
v___y_4535_ = v_a_2410_;
v___y_4536_ = v_a_2411_;
v___y_4537_ = v_a_2412_;
v___y_4538_ = v_a_2413_;
goto v___jp_4532_;
}
v___jp_4532_:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
v___x_4539_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4531_);
v___x_4540_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90));
lean_inc(v___x_4539_);
v___x_4541_ = l_Lean_Syntax_isOfKind(v___x_4539_, v___x_4540_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v_env_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
lean_dec(v___x_4539_);
lean_inc_n(v_stx_2407_, 2);
v___x_4542_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4543_ = lean_st_ref_get(v___y_4538_);
v_env_4544_ = lean_ctor_get(v___x_4543_, 0);
lean_inc_ref(v_env_4544_);
lean_dec(v___x_4543_);
v___x_4545_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4546_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4545_, v_env_4544_, v___x_4542_);
v___x_4547_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4548_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4546_, v___x_4547_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___x_4546_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4579_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4579_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4579_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v_fst_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4577_; 
v_fst_4553_ = lean_ctor_get(v_a_4549_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_a_4549_);
if (v_isSharedCheck_4577_ == 0)
{
lean_object* v_unused_4578_; 
v_unused_4578_ = lean_ctor_get(v_a_4549_, 1);
lean_dec(v_unused_4578_);
v___x_4555_ = v_a_4549_;
v_isShared_4556_ = v_isSharedCheck_4577_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_fst_4553_);
lean_dec(v_a_4549_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4577_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
if (lean_obj_tag(v_fst_4553_) == 0)
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4560_; 
lean_del_object(v___x_4551_);
v___x_4557_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4558_ = l_Lean_MessageData_ofName(v___x_4542_);
lean_inc_ref(v___x_4558_);
if (v_isShared_4556_ == 0)
{
lean_ctor_set_tag(v___x_4555_, 7);
lean_ctor_set(v___x_4555_, 1, v___x_4558_);
lean_ctor_set(v___x_4555_, 0, v___x_4557_);
v___x_4560_ = v___x_4555_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4557_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v___x_4558_);
v___x_4560_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4561_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4560_);
lean_ctor_set(v___x_4562_, 1, v___x_4561_);
v___x_4563_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4564_ = l_Lean_indentD(v___x_4563_);
v___x_4565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4562_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
v___x_4566_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4565_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
lean_ctor_set(v___x_4568_, 1, v___x_4558_);
v___x_4569_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4568_);
lean_ctor_set(v___x_4570_, 1, v___x_4569_);
v___x_4571_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4570_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
return v___x_4571_;
}
}
else
{
lean_object* v_val_4573_; lean_object* v___x_4575_; 
lean_del_object(v___x_4555_);
lean_dec(v___x_4542_);
lean_dec(v_stx_2407_);
v_val_4573_ = lean_ctor_get(v_fst_4553_, 0);
lean_inc(v_val_4573_);
lean_dec_ref_known(v_fst_4553_, 1);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v_val_4573_);
v___x_4575_ = v___x_4551_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_val_4573_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v___x_4542_);
lean_dec(v_stx_2407_);
v_a_4580_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4548_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4548_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
else
{
lean_object* v___x_4588_; uint8_t v___x_4589_; 
v___x_4588_ = l_Lean_Syntax_getArg(v___x_4539_, v___x_4531_);
lean_dec(v___x_4539_);
v___x_4589_ = l_Lean_Syntax_isNone(v___x_4588_);
if (v___x_4589_ == 0)
{
uint8_t v___x_4590_; 
v___x_4590_ = l_Lean_Syntax_matchesNull(v___x_4588_, v___x_4531_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v_env_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
lean_inc_n(v_stx_2407_, 2);
v___x_4591_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4592_ = lean_st_ref_get(v___y_4538_);
v_env_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc_ref(v_env_4593_);
lean_dec(v___x_4592_);
v___x_4594_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4595_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4594_, v_env_4593_, v___x_4591_);
v___x_4596_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4597_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4595_, v___x_4596_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___x_4595_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4628_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4600_ = v___x_4597_;
v_isShared_4601_ = v_isSharedCheck_4628_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4628_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v_fst_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4626_; 
v_fst_4602_ = lean_ctor_get(v_a_4598_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_a_4598_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; 
v_unused_4627_ = lean_ctor_get(v_a_4598_, 1);
lean_dec(v_unused_4627_);
v___x_4604_ = v_a_4598_;
v_isShared_4605_ = v_isSharedCheck_4626_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_fst_4602_);
lean_dec(v_a_4598_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4626_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
if (lean_obj_tag(v_fst_4602_) == 0)
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4609_; 
lean_del_object(v___x_4600_);
v___x_4606_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4607_ = l_Lean_MessageData_ofName(v___x_4591_);
lean_inc_ref(v___x_4607_);
if (v_isShared_4605_ == 0)
{
lean_ctor_set_tag(v___x_4604_, 7);
lean_ctor_set(v___x_4604_, 1, v___x_4607_);
lean_ctor_set(v___x_4604_, 0, v___x_4606_);
v___x_4609_ = v___x_4604_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4606_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v___x_4607_);
v___x_4609_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4610_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4609_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
v___x_4612_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4613_ = l_Lean_indentD(v___x_4612_);
v___x_4614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4611_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
v___x_4615_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4614_);
lean_ctor_set(v___x_4616_, 1, v___x_4615_);
v___x_4617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
lean_ctor_set(v___x_4617_, 1, v___x_4607_);
v___x_4618_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4617_);
lean_ctor_set(v___x_4619_, 1, v___x_4618_);
v___x_4620_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4619_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
return v___x_4620_;
}
}
else
{
lean_object* v_val_4622_; lean_object* v___x_4624_; 
lean_del_object(v___x_4604_);
lean_dec(v___x_4591_);
lean_dec(v_stx_2407_);
v_val_4622_ = lean_ctor_get(v_fst_4602_, 0);
lean_inc(v_val_4622_);
lean_dec_ref_known(v_fst_4602_, 1);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v_val_4622_);
v___x_4624_ = v___x_4600_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_val_4622_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
lean_dec(v___x_4591_);
lean_dec(v_stx_2407_);
v_a_4629_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4597_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4597_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_2457_;
}
}
else
{
lean_dec(v___x_4588_);
lean_dec(v_stx_2407_);
goto v___jp_2457_;
}
}
}
}
}
}
else
{
lean_object* v___x_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; 
v___x_4686_ = lean_unsigned_to_nat(1u);
v___x_4687_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4686_);
v___x_4688_ = l_Lean_Syntax_isNone(v___x_4687_);
if (v___x_4688_ == 0)
{
uint8_t v___x_4689_; 
v___x_4689_ = l_Lean_Syntax_matchesNull(v___x_4687_, v___x_4686_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v_env_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
lean_inc_n(v_stx_2407_, 2);
v___x_4690_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4691_ = lean_st_ref_get(v_a_2413_);
v_env_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc_ref(v_env_4692_);
lean_dec(v___x_4691_);
v___x_4693_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4694_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4693_, v_env_4692_, v___x_4690_);
v___x_4695_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4696_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4694_, v___x_4695_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4694_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4727_; 
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4699_ = v___x_4696_;
v_isShared_4700_ = v_isSharedCheck_4727_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4696_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4727_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v_fst_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4725_; 
v_fst_4701_ = lean_ctor_get(v_a_4697_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v_a_4697_);
if (v_isSharedCheck_4725_ == 0)
{
lean_object* v_unused_4726_; 
v_unused_4726_ = lean_ctor_get(v_a_4697_, 1);
lean_dec(v_unused_4726_);
v___x_4703_ = v_a_4697_;
v_isShared_4704_ = v_isSharedCheck_4725_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_fst_4701_);
lean_dec(v_a_4697_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4725_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
if (lean_obj_tag(v_fst_4701_) == 0)
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4708_; 
lean_del_object(v___x_4699_);
v___x_4705_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4706_ = l_Lean_MessageData_ofName(v___x_4690_);
lean_inc_ref(v___x_4706_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set_tag(v___x_4703_, 7);
lean_ctor_set(v___x_4703_, 1, v___x_4706_);
lean_ctor_set(v___x_4703_, 0, v___x_4705_);
v___x_4708_ = v___x_4703_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4705_);
lean_ctor_set(v_reuseFailAlloc_4720_, 1, v___x_4706_);
v___x_4708_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4709_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4708_);
lean_ctor_set(v___x_4710_, 1, v___x_4709_);
v___x_4711_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4712_ = l_Lean_indentD(v___x_4711_);
v___x_4713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4710_);
lean_ctor_set(v___x_4713_, 1, v___x_4712_);
v___x_4714_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4713_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
v___x_4716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
lean_ctor_set(v___x_4716_, 1, v___x_4706_);
v___x_4717_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4716_);
lean_ctor_set(v___x_4718_, 1, v___x_4717_);
v___x_4719_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4718_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4719_;
}
}
else
{
lean_object* v_val_4721_; lean_object* v___x_4723_; 
lean_del_object(v___x_4703_);
lean_dec(v___x_4690_);
lean_dec(v_stx_2407_);
v_val_4721_ = lean_ctor_get(v_fst_4701_, 0);
lean_inc(v_val_4721_);
lean_dec_ref_known(v_fst_4701_, 1);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 0, v_val_4721_);
v___x_4723_ = v___x_4699_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_val_4721_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
lean_dec(v___x_4690_);
lean_dec(v_stx_2407_);
v_a_4728_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4730_ = v___x_4696_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4696_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
}
else
{
v___y_2747_ = v_a_2408_;
v___y_2748_ = v_a_2409_;
v___y_2749_ = v_a_2410_;
v___y_2750_ = v_a_2411_;
v___y_2751_ = v_a_2412_;
v___y_2752_ = v_a_2413_;
goto v___jp_2746_;
}
}
else
{
lean_dec(v___x_4687_);
v___y_2747_ = v_a_2408_;
v___y_2748_ = v_a_2409_;
v___y_2749_ = v_a_2410_;
v___y_2750_ = v_a_2411_;
v___y_2751_ = v_a_2412_;
v___y_2752_ = v_a_2413_;
goto v___jp_2746_;
}
}
}
else
{
lean_object* v___x_4736_; lean_object* v___x_4737_; uint8_t v___x_4738_; 
v___x_4736_ = lean_unsigned_to_nat(1u);
v___x_4737_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4736_);
v___x_4738_ = l_Lean_Syntax_isNone(v___x_4737_);
if (v___x_4738_ == 0)
{
uint8_t v___x_4739_; 
v___x_4739_ = l_Lean_Syntax_matchesNull(v___x_4737_, v___x_4736_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v_env_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
lean_inc_n(v_stx_2407_, 2);
v___x_4740_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4741_ = lean_st_ref_get(v_a_2413_);
v_env_4742_ = lean_ctor_get(v___x_4741_, 0);
lean_inc_ref(v_env_4742_);
lean_dec(v___x_4741_);
v___x_4743_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4744_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4743_, v_env_4742_, v___x_4740_);
v___x_4745_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4746_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4744_, v___x_4745_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4744_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4777_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4749_ = v___x_4746_;
v_isShared_4750_ = v_isSharedCheck_4777_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4746_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4777_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v_fst_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4775_; 
v_fst_4751_ = lean_ctor_get(v_a_4747_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v_a_4747_);
if (v_isSharedCheck_4775_ == 0)
{
lean_object* v_unused_4776_; 
v_unused_4776_ = lean_ctor_get(v_a_4747_, 1);
lean_dec(v_unused_4776_);
v___x_4753_ = v_a_4747_;
v_isShared_4754_ = v_isSharedCheck_4775_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_fst_4751_);
lean_dec(v_a_4747_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4775_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
if (lean_obj_tag(v_fst_4751_) == 0)
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4758_; 
lean_del_object(v___x_4749_);
v___x_4755_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4756_ = l_Lean_MessageData_ofName(v___x_4740_);
lean_inc_ref(v___x_4756_);
if (v_isShared_4754_ == 0)
{
lean_ctor_set_tag(v___x_4753_, 7);
lean_ctor_set(v___x_4753_, 1, v___x_4756_);
lean_ctor_set(v___x_4753_, 0, v___x_4755_);
v___x_4758_ = v___x_4753_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4770_, 1, v___x_4756_);
v___x_4758_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4759_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4758_);
lean_ctor_set(v___x_4760_, 1, v___x_4759_);
v___x_4761_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4762_ = l_Lean_indentD(v___x_4761_);
v___x_4763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4760_);
lean_ctor_set(v___x_4763_, 1, v___x_4762_);
v___x_4764_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4763_);
lean_ctor_set(v___x_4765_, 1, v___x_4764_);
v___x_4766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
lean_ctor_set(v___x_4766_, 1, v___x_4756_);
v___x_4767_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4768_, 0, v___x_4766_);
lean_ctor_set(v___x_4768_, 1, v___x_4767_);
v___x_4769_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4768_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4769_;
}
}
else
{
lean_object* v_val_4771_; lean_object* v___x_4773_; 
lean_del_object(v___x_4753_);
lean_dec(v___x_4740_);
lean_dec(v_stx_2407_);
v_val_4771_ = lean_ctor_get(v_fst_4751_, 0);
lean_inc(v_val_4771_);
lean_dec_ref_known(v_fst_4751_, 1);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 0, v_val_4771_);
v___x_4773_ = v___x_4749_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_val_4771_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
lean_dec(v___x_4740_);
lean_dec(v_stx_2407_);
v_a_4778_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4746_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4746_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
else
{
v___y_2678_ = v_a_2408_;
v___y_2679_ = v_a_2409_;
v___y_2680_ = v_a_2410_;
v___y_2681_ = v_a_2411_;
v___y_2682_ = v_a_2412_;
v___y_2683_ = v_a_2413_;
goto v___jp_2677_;
}
}
else
{
lean_dec(v___x_4737_);
v___y_2678_ = v_a_2408_;
v___y_2679_ = v_a_2409_;
v___y_2680_ = v_a_2410_;
v___y_2681_ = v_a_2411_;
v___y_2682_ = v_a_2412_;
v___y_2683_ = v_a_2413_;
goto v___jp_2677_;
}
}
v___jp_2736_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = lean_unsigned_to_nat(3u);
v___x_2744_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2743_);
lean_dec(v_stx_2407_);
v___x_2745_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2735_, v___x_2744_, v___y_2742_, v___y_2740_, v___y_2739_, v___y_2741_, v___y_2738_, v___y_2737_);
return v___x_2745_;
}
v___jp_2746_:
{
if (v___x_2735_ == 0)
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2753_ = lean_unsigned_to_nat(2u);
v___x_2754_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2753_);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2756_ = l_Lean_Syntax_isOfKind(v___x_2754_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v_env_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_inc_n(v_stx_2407_, 2);
v___x_2757_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_2758_ = lean_st_ref_get(v___y_2752_);
v_env_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc_ref(v_env_2759_);
lean_dec(v___x_2758_);
v___x_2760_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2761_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2760_, v_env_2759_, v___x_2757_);
v___x_2762_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2763_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_2761_, v___x_2762_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___x_2761_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2794_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2794_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2794_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_fst_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2792_; 
v_fst_2768_ = lean_ctor_get(v_a_2764_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_a_2764_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; 
v_unused_2793_ = lean_ctor_get(v_a_2764_, 1);
lean_dec(v_unused_2793_);
v___x_2770_ = v_a_2764_;
v_isShared_2771_ = v_isSharedCheck_2792_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_fst_2768_);
lean_dec(v_a_2764_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2792_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
if (lean_obj_tag(v_fst_2768_) == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_del_object(v___x_2766_);
v___x_2772_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2773_ = l_Lean_MessageData_ofName(v___x_2757_);
lean_inc_ref(v___x_2773_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 7);
lean_ctor_set(v___x_2770_, 1, v___x_2773_);
lean_ctor_set(v___x_2770_, 0, v___x_2772_);
v___x_2775_ = v___x_2770_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2776_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_2779_ = l_Lean_indentD(v___x_2778_);
v___x_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2777_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2773_);
v___x_2784_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2785_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
return v___x_2786_;
}
}
else
{
lean_object* v_val_2788_; lean_object* v___x_2790_; 
lean_del_object(v___x_2770_);
lean_dec(v___x_2757_);
lean_dec(v_stx_2407_);
v_val_2788_ = lean_ctor_get(v_fst_2768_, 0);
lean_inc(v_val_2788_);
lean_dec_ref_known(v_fst_2768_, 1);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v_val_2788_);
v___x_2790_ = v___x_2766_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_val_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v___x_2757_);
lean_dec(v_stx_2407_);
v_a_2795_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2763_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2763_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
else
{
v___y_2737_ = v___y_2752_;
v___y_2738_ = v___y_2751_;
v___y_2739_ = v___y_2749_;
v___y_2740_ = v___y_2748_;
v___y_2741_ = v___y_2750_;
v___y_2742_ = v___y_2747_;
goto v___jp_2736_;
}
}
else
{
v___y_2737_ = v___y_2752_;
v___y_2738_ = v___y_2751_;
v___y_2739_ = v___y_2749_;
v___y_2740_ = v___y_2748_;
v___y_2741_ = v___y_2750_;
v___y_2742_ = v___y_2747_;
goto v___jp_2736_;
}
}
}
else
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4786_ = lean_unsigned_to_nat(0u);
v___x_4787_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4786_);
v___x_4788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4789_ = l_Lean_Syntax_isOfKind(v___x_4787_, v___x_4788_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v_env_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_del_object(v___x_2471_);
lean_inc_n(v_stx_2407_, 2);
v___x_4790_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4791_ = lean_st_ref_get(v_a_2413_);
v_env_4792_ = lean_ctor_get(v___x_4791_, 0);
lean_inc_ref(v_env_4792_);
lean_dec(v___x_4791_);
v___x_4793_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4794_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4793_, v_env_4792_, v___x_4790_);
v___x_4795_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4796_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4794_, v___x_4795_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4794_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4827_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4799_ = v___x_4796_;
v_isShared_4800_ = v_isSharedCheck_4827_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4796_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4827_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v_fst_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4825_; 
v_fst_4801_ = lean_ctor_get(v_a_4797_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v_a_4797_);
if (v_isSharedCheck_4825_ == 0)
{
lean_object* v_unused_4826_; 
v_unused_4826_ = lean_ctor_get(v_a_4797_, 1);
lean_dec(v_unused_4826_);
v___x_4803_ = v_a_4797_;
v_isShared_4804_ = v_isSharedCheck_4825_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_fst_4801_);
lean_dec(v_a_4797_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4825_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
if (lean_obj_tag(v_fst_4801_) == 0)
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
lean_del_object(v___x_4799_);
v___x_4805_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4806_ = l_Lean_MessageData_ofName(v___x_4790_);
lean_inc_ref(v___x_4806_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set_tag(v___x_4803_, 7);
lean_ctor_set(v___x_4803_, 1, v___x_4806_);
lean_ctor_set(v___x_4803_, 0, v___x_4805_);
v___x_4808_ = v___x_4803_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4809_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4810_, 0, v___x_4808_);
lean_ctor_set(v___x_4810_, 1, v___x_4809_);
v___x_4811_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4812_ = l_Lean_indentD(v___x_4811_);
v___x_4813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4810_);
lean_ctor_set(v___x_4813_, 1, v___x_4812_);
v___x_4814_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4813_);
lean_ctor_set(v___x_4815_, 1, v___x_4814_);
v___x_4816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
lean_ctor_set(v___x_4816_, 1, v___x_4806_);
v___x_4817_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4816_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4818_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4819_;
}
}
else
{
lean_object* v_val_4821_; lean_object* v___x_4823_; 
lean_del_object(v___x_4803_);
lean_dec(v___x_4790_);
lean_dec(v_stx_2407_);
v_val_4821_ = lean_ctor_get(v_fst_4801_, 0);
lean_inc(v_val_4821_);
lean_dec_ref_known(v_fst_4801_, 1);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 0, v_val_4821_);
v___x_4823_ = v___x_4799_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_val_4821_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_dec(v___x_4790_);
lean_dec(v_stx_2407_);
v_a_4828_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4796_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4796_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
else
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; uint8_t v___x_4839_; 
v___x_4836_ = lean_unsigned_to_nat(1u);
v___x_4837_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4836_);
v___x_4838_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92));
lean_inc(v___x_4837_);
v___x_4839_ = l_Lean_Syntax_isOfKind(v___x_4837_, v___x_4838_);
if (v___x_4839_ == 0)
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v_env_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
lean_dec(v___x_4837_);
lean_del_object(v___x_2471_);
lean_inc_n(v_stx_2407_, 2);
v___x_4840_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4841_ = lean_st_ref_get(v_a_2413_);
v_env_4842_ = lean_ctor_get(v___x_4841_, 0);
lean_inc_ref(v_env_4842_);
lean_dec(v___x_4841_);
v___x_4843_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4844_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4843_, v_env_4842_, v___x_4840_);
v___x_4845_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4846_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4844_, v___x_4845_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4844_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4877_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4849_ = v___x_4846_;
v_isShared_4850_ = v_isSharedCheck_4877_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4846_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4877_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v_fst_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4875_; 
v_fst_4851_ = lean_ctor_get(v_a_4847_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v_a_4847_);
if (v_isSharedCheck_4875_ == 0)
{
lean_object* v_unused_4876_; 
v_unused_4876_ = lean_ctor_get(v_a_4847_, 1);
lean_dec(v_unused_4876_);
v___x_4853_ = v_a_4847_;
v_isShared_4854_ = v_isSharedCheck_4875_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_fst_4851_);
lean_dec(v_a_4847_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4875_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
if (lean_obj_tag(v_fst_4851_) == 0)
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4858_; 
lean_del_object(v___x_4849_);
v___x_4855_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4856_ = l_Lean_MessageData_ofName(v___x_4840_);
lean_inc_ref(v___x_4856_);
if (v_isShared_4854_ == 0)
{
lean_ctor_set_tag(v___x_4853_, 7);
lean_ctor_set(v___x_4853_, 1, v___x_4856_);
lean_ctor_set(v___x_4853_, 0, v___x_4855_);
v___x_4858_ = v___x_4853_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4855_);
lean_ctor_set(v_reuseFailAlloc_4870_, 1, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4859_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4858_);
lean_ctor_set(v___x_4860_, 1, v___x_4859_);
v___x_4861_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4862_ = l_Lean_indentD(v___x_4861_);
v___x_4863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4860_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
v___x_4864_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4863_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
v___x_4866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
lean_ctor_set(v___x_4866_, 1, v___x_4856_);
v___x_4867_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4866_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
v___x_4869_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4868_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4869_;
}
}
else
{
lean_object* v_val_4871_; lean_object* v___x_4873_; 
lean_del_object(v___x_4853_);
lean_dec(v___x_4840_);
lean_dec(v_stx_2407_);
v_val_4871_ = lean_ctor_get(v_fst_4851_, 0);
lean_inc(v_val_4871_);
lean_dec_ref_known(v_fst_4851_, 1);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v_val_4871_);
v___x_4873_ = v___x_4849_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_val_4871_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
else
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4885_; 
lean_dec(v___x_4840_);
lean_dec(v_stx_2407_);
v_a_4878_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4880_ = v___x_4846_;
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4846_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4883_; 
if (v_isShared_4881_ == 0)
{
v___x_4883_ = v___x_4880_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4878_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
}
else
{
lean_object* v___x_4886_; uint8_t v___x_4887_; 
v___x_4886_ = l_Lean_Syntax_getArg(v___x_4837_, v___x_4786_);
lean_dec(v___x_4837_);
lean_inc(v___x_4886_);
v___x_4887_ = l_Lean_Syntax_matchesNull(v___x_4886_, v___x_4836_);
if (v___x_4887_ == 0)
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v_env_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
lean_dec(v___x_4886_);
lean_del_object(v___x_2471_);
lean_inc_n(v_stx_2407_, 2);
v___x_4888_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4889_ = lean_st_ref_get(v_a_2413_);
v_env_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc_ref(v_env_4890_);
lean_dec(v___x_4889_);
v___x_4891_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4892_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4891_, v_env_4890_, v___x_4888_);
v___x_4893_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4894_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4892_, v___x_4893_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4892_);
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4925_; 
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4897_ = v___x_4894_;
v_isShared_4898_ = v_isSharedCheck_4925_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4894_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4925_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v_fst_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4923_; 
v_fst_4899_ = lean_ctor_get(v_a_4895_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_a_4895_);
if (v_isSharedCheck_4923_ == 0)
{
lean_object* v_unused_4924_; 
v_unused_4924_ = lean_ctor_get(v_a_4895_, 1);
lean_dec(v_unused_4924_);
v___x_4901_ = v_a_4895_;
v_isShared_4902_ = v_isSharedCheck_4923_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_fst_4899_);
lean_dec(v_a_4895_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4923_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
if (lean_obj_tag(v_fst_4899_) == 0)
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4906_; 
lean_del_object(v___x_4897_);
v___x_4903_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4904_ = l_Lean_MessageData_ofName(v___x_4888_);
lean_inc_ref(v___x_4904_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set_tag(v___x_4901_, 7);
lean_ctor_set(v___x_4901_, 1, v___x_4904_);
lean_ctor_set(v___x_4901_, 0, v___x_4903_);
v___x_4906_ = v___x_4901_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v___x_4903_);
lean_ctor_set(v_reuseFailAlloc_4918_, 1, v___x_4904_);
v___x_4906_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4907_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4906_);
lean_ctor_set(v___x_4908_, 1, v___x_4907_);
v___x_4909_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4910_ = l_Lean_indentD(v___x_4909_);
v___x_4911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4908_);
lean_ctor_set(v___x_4911_, 1, v___x_4910_);
v___x_4912_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4911_);
lean_ctor_set(v___x_4913_, 1, v___x_4912_);
v___x_4914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4913_);
lean_ctor_set(v___x_4914_, 1, v___x_4904_);
v___x_4915_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4914_);
lean_ctor_set(v___x_4916_, 1, v___x_4915_);
v___x_4917_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4916_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4917_;
}
}
else
{
lean_object* v_val_4919_; lean_object* v___x_4921_; 
lean_del_object(v___x_4901_);
lean_dec(v___x_4888_);
lean_dec(v_stx_2407_);
v_val_4919_ = lean_ctor_get(v_fst_4899_, 0);
lean_inc(v_val_4919_);
lean_dec_ref_known(v_fst_4899_, 1);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v_val_4919_);
v___x_4921_ = v___x_4897_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_val_4919_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
else
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4933_; 
lean_dec(v___x_4888_);
lean_dec(v_stx_2407_);
v_a_4926_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4928_ = v___x_4894_;
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4894_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
if (v_isShared_4929_ == 0)
{
v___x_4931_ = v___x_4928_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
}
else
{
if (v___x_2674_ == 0)
{
lean_object* v___x_4934_; lean_object* v___x_4935_; uint8_t v___x_4936_; 
v___x_4934_ = l_Lean_Syntax_getArg(v___x_4886_, v___x_4786_);
lean_dec(v___x_4886_);
v___x_4935_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94));
v___x_4936_ = l_Lean_Syntax_isOfKind(v___x_4934_, v___x_4935_);
if (v___x_4936_ == 0)
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v_env_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
lean_del_object(v___x_2471_);
lean_inc_n(v_stx_2407_, 2);
v___x_4937_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4938_ = lean_st_ref_get(v_a_2413_);
v_env_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc_ref(v_env_4939_);
lean_dec(v___x_4938_);
v___x_4940_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4941_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4940_, v_env_4939_, v___x_4937_);
v___x_4942_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4943_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4941_, v___x_4942_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4941_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4974_; 
v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4946_ = v___x_4943_;
v_isShared_4947_ = v_isSharedCheck_4974_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4943_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4974_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v_fst_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4972_; 
v_fst_4948_ = lean_ctor_get(v_a_4944_, 0);
v_isSharedCheck_4972_ = !lean_is_exclusive(v_a_4944_);
if (v_isSharedCheck_4972_ == 0)
{
lean_object* v_unused_4973_; 
v_unused_4973_ = lean_ctor_get(v_a_4944_, 1);
lean_dec(v_unused_4973_);
v___x_4950_ = v_a_4944_;
v_isShared_4951_ = v_isSharedCheck_4972_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_fst_4948_);
lean_dec(v_a_4944_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4972_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
if (lean_obj_tag(v_fst_4948_) == 0)
{
lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4955_; 
lean_del_object(v___x_4946_);
v___x_4952_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4953_ = l_Lean_MessageData_ofName(v___x_4937_);
lean_inc_ref(v___x_4953_);
if (v_isShared_4951_ == 0)
{
lean_ctor_set_tag(v___x_4950_, 7);
lean_ctor_set(v___x_4950_, 1, v___x_4953_);
lean_ctor_set(v___x_4950_, 0, v___x_4952_);
v___x_4955_ = v___x_4950_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4952_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v___x_4953_);
v___x_4955_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4956_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4955_);
lean_ctor_set(v___x_4957_, 1, v___x_4956_);
v___x_4958_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_4959_ = l_Lean_indentD(v___x_4958_);
v___x_4960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4957_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___x_4961_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4960_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4962_);
lean_ctor_set(v___x_4963_, 1, v___x_4953_);
v___x_4964_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4963_);
lean_ctor_set(v___x_4965_, 1, v___x_4964_);
v___x_4966_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4965_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_4966_;
}
}
else
{
lean_object* v_val_4968_; lean_object* v___x_4970_; 
lean_del_object(v___x_4950_);
lean_dec(v___x_4937_);
lean_dec(v_stx_2407_);
v_val_4968_ = lean_ctor_get(v_fst_4948_, 0);
lean_inc(v_val_4968_);
lean_dec_ref_known(v_fst_4948_, 1);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 0, v_val_4968_);
v___x_4970_ = v___x_4946_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_val_4968_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
}
else
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4982_; 
lean_dec(v___x_4937_);
lean_dec(v_stx_2407_);
v_a_4975_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4977_ = v___x_4943_;
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4943_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4980_; 
if (v_isShared_4978_ == 0)
{
v___x_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4975_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_2473_;
}
}
else
{
lean_dec(v___x_4886_);
lean_dec(v_stx_2407_);
goto v___jp_2473_;
}
}
}
}
}
v___jp_2677_:
{
if (v___x_2676_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2684_ = lean_unsigned_to_nat(2u);
v___x_2685_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2684_);
v___x_2686_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2687_ = l_Lean_Syntax_isOfKind(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v_env_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_inc_n(v_stx_2407_, 2);
v___x_2688_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_2689_ = lean_st_ref_get(v___y_2683_);
v_env_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc_ref(v_env_2690_);
lean_dec(v___x_2689_);
v___x_2691_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2692_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2691_, v_env_2690_, v___x_2688_);
v___x_2693_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2694_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_2692_, v___x_2693_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___x_2692_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2725_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2725_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2725_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_fst_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2723_; 
v_fst_2699_ = lean_ctor_get(v_a_2695_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_a_2695_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; 
v_unused_2724_ = lean_ctor_get(v_a_2695_, 1);
lean_dec(v_unused_2724_);
v___x_2701_ = v_a_2695_;
v_isShared_2702_ = v_isSharedCheck_2723_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_fst_2699_);
lean_dec(v_a_2695_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2723_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
if (lean_obj_tag(v_fst_2699_) == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
lean_del_object(v___x_2697_);
v___x_2703_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2704_ = l_Lean_MessageData_ofName(v___x_2688_);
lean_inc_ref(v___x_2704_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set_tag(v___x_2701_, 7);
lean_ctor_set(v___x_2701_, 1, v___x_2704_);
lean_ctor_set(v___x_2701_, 0, v___x_2703_);
v___x_2706_ = v___x_2701_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2707_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_2710_ = l_Lean_indentD(v___x_2709_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2708_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___x_2704_);
v___x_2715_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2716_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2717_;
}
}
else
{
lean_object* v_val_2719_; lean_object* v___x_2721_; 
lean_del_object(v___x_2701_);
lean_dec(v___x_2688_);
lean_dec(v_stx_2407_);
v_val_2719_ = lean_ctor_get(v_fst_2699_, 0);
lean_inc(v_val_2719_);
lean_dec_ref_known(v_fst_2699_, 1);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v_val_2719_);
v___x_2721_ = v___x_2697_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_val_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v___x_2688_);
lean_dec(v_stx_2407_);
v_a_2726_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2694_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2694_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
v___y_2434_ = v___y_2682_;
v___y_2435_ = v___y_2678_;
v___y_2436_ = v___y_2680_;
v___y_2437_ = v___y_2683_;
v___y_2438_ = v___y_2679_;
v___y_2439_ = v___y_2681_;
goto v___jp_2433_;
}
}
else
{
v___y_2434_ = v___y_2682_;
v___y_2435_ = v___y_2678_;
v___y_2436_ = v___y_2680_;
v___y_2437_ = v___y_2683_;
v___y_2438_ = v___y_2679_;
v___y_2439_ = v___y_2681_;
goto v___jp_2433_;
}
}
}
else
{
lean_del_object(v___x_2471_);
if (v___x_2621_ == 0)
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; uint8_t v___x_4986_; 
v___x_4983_ = lean_unsigned_to_nat(1u);
v___x_4984_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_4983_);
v___x_4985_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_4986_ = l_Lean_Syntax_isOfKind(v___x_4984_, v___x_4985_);
if (v___x_4986_ == 0)
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v_env_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
lean_inc_n(v_stx_2407_, 2);
v___x_4987_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_4988_ = lean_st_ref_get(v_a_2413_);
v_env_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc_ref(v_env_4989_);
lean_dec(v___x_4988_);
v___x_4990_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4991_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4990_, v_env_4989_, v___x_4987_);
v___x_4992_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4993_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_4991_, v___x_4992_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_4991_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5024_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_4996_ = v___x_4993_;
v_isShared_4997_ = v_isSharedCheck_5024_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4993_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5024_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v_fst_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5022_; 
v_fst_4998_ = lean_ctor_get(v_a_4994_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v_a_4994_);
if (v_isSharedCheck_5022_ == 0)
{
lean_object* v_unused_5023_; 
v_unused_5023_ = lean_ctor_get(v_a_4994_, 1);
lean_dec(v_unused_5023_);
v___x_5000_ = v_a_4994_;
v_isShared_5001_ = v_isSharedCheck_5022_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_fst_4998_);
lean_dec(v_a_4994_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5022_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
if (lean_obj_tag(v_fst_4998_) == 0)
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5005_; 
lean_del_object(v___x_4996_);
v___x_5002_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_5003_ = l_Lean_MessageData_ofName(v___x_4987_);
lean_inc_ref(v___x_5003_);
if (v_isShared_5001_ == 0)
{
lean_ctor_set_tag(v___x_5000_, 7);
lean_ctor_set(v___x_5000_, 1, v___x_5003_);
lean_ctor_set(v___x_5000_, 0, v___x_5002_);
v___x_5005_ = v___x_5000_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_5002_);
lean_ctor_set(v_reuseFailAlloc_5017_, 1, v___x_5003_);
v___x_5005_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5006_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_5007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5005_);
lean_ctor_set(v___x_5007_, 1, v___x_5006_);
v___x_5008_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_5009_ = l_Lean_indentD(v___x_5008_);
v___x_5010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5007_);
lean_ctor_set(v___x_5010_, 1, v___x_5009_);
v___x_5011_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_5012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5010_);
lean_ctor_set(v___x_5012_, 1, v___x_5011_);
v___x_5013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5013_, 0, v___x_5012_);
lean_ctor_set(v___x_5013_, 1, v___x_5003_);
v___x_5014_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_5015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5013_);
lean_ctor_set(v___x_5015_, 1, v___x_5014_);
v___x_5016_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5015_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_5016_;
}
}
else
{
lean_object* v_val_5018_; lean_object* v___x_5020_; 
lean_del_object(v___x_5000_);
lean_dec(v___x_4987_);
lean_dec(v_stx_2407_);
v_val_5018_ = lean_ctor_get(v_fst_4998_, 0);
lean_inc(v_val_5018_);
lean_dec_ref_known(v_fst_4998_, 1);
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 0, v_val_5018_);
v___x_5020_ = v___x_4996_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_val_5018_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
}
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5032_; 
lean_dec(v___x_4987_);
lean_dec(v_stx_2407_);
v_a_5025_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5027_ = v___x_4993_;
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_4993_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
if (v_isShared_5028_ == 0)
{
v___x_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5025_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
else
{
goto v___jp_2622_;
}
}
else
{
goto v___jp_2622_;
}
}
}
else
{
lean_object* v___x_5033_; lean_object* v___x_5034_; uint8_t v___x_5035_; 
lean_del_object(v___x_2471_);
v___x_5033_ = lean_unsigned_to_nat(1u);
v___x_5034_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_5033_);
v___x_5035_ = l_Lean_Syntax_isNone(v___x_5034_);
if (v___x_5035_ == 0)
{
uint8_t v___x_5036_; 
v___x_5036_ = l_Lean_Syntax_matchesNull(v___x_5034_, v___x_5033_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v_env_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
lean_inc_n(v_stx_2407_, 2);
v___x_5037_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_5038_ = lean_st_ref_get(v_a_2413_);
v_env_5039_ = lean_ctor_get(v___x_5038_, 0);
lean_inc_ref(v_env_5039_);
lean_dec(v___x_5038_);
v___x_5040_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_5041_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_5040_, v_env_5039_, v___x_5037_);
v___x_5042_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_5043_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_5041_, v___x_5042_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_5041_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5074_; 
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5046_ = v___x_5043_;
v_isShared_5047_ = v_isSharedCheck_5074_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_5043_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5074_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v_fst_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5072_; 
v_fst_5048_ = lean_ctor_get(v_a_5044_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v_a_5044_);
if (v_isSharedCheck_5072_ == 0)
{
lean_object* v_unused_5073_; 
v_unused_5073_ = lean_ctor_get(v_a_5044_, 1);
lean_dec(v_unused_5073_);
v___x_5050_ = v_a_5044_;
v_isShared_5051_ = v_isSharedCheck_5072_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_fst_5048_);
lean_dec(v_a_5044_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5072_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
if (lean_obj_tag(v_fst_5048_) == 0)
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5055_; 
lean_del_object(v___x_5046_);
v___x_5052_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_5053_ = l_Lean_MessageData_ofName(v___x_5037_);
lean_inc_ref(v___x_5053_);
if (v_isShared_5051_ == 0)
{
lean_ctor_set_tag(v___x_5050_, 7);
lean_ctor_set(v___x_5050_, 1, v___x_5053_);
lean_ctor_set(v___x_5050_, 0, v___x_5052_);
v___x_5055_ = v___x_5050_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v___x_5052_);
lean_ctor_set(v_reuseFailAlloc_5067_, 1, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5056_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_5057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5055_);
lean_ctor_set(v___x_5057_, 1, v___x_5056_);
v___x_5058_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_5059_ = l_Lean_indentD(v___x_5058_);
v___x_5060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5057_);
lean_ctor_set(v___x_5060_, 1, v___x_5059_);
v___x_5061_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_5062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5060_);
lean_ctor_set(v___x_5062_, 1, v___x_5061_);
v___x_5063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5062_);
lean_ctor_set(v___x_5063_, 1, v___x_5053_);
v___x_5064_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_5065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5063_);
lean_ctor_set(v___x_5065_, 1, v___x_5064_);
v___x_5066_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5065_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_5066_;
}
}
else
{
lean_object* v_val_5068_; lean_object* v___x_5070_; 
lean_del_object(v___x_5050_);
lean_dec(v___x_5037_);
lean_dec(v_stx_2407_);
v_val_5068_ = lean_ctor_get(v_fst_5048_, 0);
lean_inc(v_val_5068_);
lean_dec_ref_known(v_fst_5048_, 1);
if (v_isShared_5047_ == 0)
{
lean_ctor_set(v___x_5046_, 0, v_val_5068_);
v___x_5070_ = v___x_5046_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_val_5068_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
}
else
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
lean_dec(v___x_5037_);
lean_dec(v_stx_2407_);
v_a_5075_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_5043_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5043_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
else
{
v___y_2564_ = v_a_2408_;
v___y_2565_ = v_a_2409_;
v___y_2566_ = v_a_2410_;
v___y_2567_ = v_a_2411_;
v___y_2568_ = v_a_2412_;
v___y_2569_ = v_a_2413_;
goto v___jp_2563_;
}
}
else
{
lean_dec(v___x_5034_);
v___y_2564_ = v_a_2408_;
v___y_2565_ = v_a_2409_;
v___y_2566_ = v_a_2410_;
v___y_2567_ = v_a_2411_;
v___y_2568_ = v_a_2412_;
v___y_2569_ = v_a_2413_;
goto v___jp_2563_;
}
}
v___jp_2622_:
{
if (v___x_2621_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2623_ = lean_unsigned_to_nat(2u);
v___x_2624_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2623_);
v___x_2625_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2626_ = l_Lean_Syntax_isOfKind(v___x_2624_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v_env_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_inc_n(v_stx_2407_, 2);
v___x_2627_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_2628_ = lean_st_ref_get(v_a_2413_);
v_env_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc_ref(v_env_2629_);
lean_dec(v___x_2628_);
v___x_2630_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2631_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2630_, v_env_2629_, v___x_2627_);
v___x_2632_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2633_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_2631_, v___x_2632_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_2631_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2664_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2664_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2664_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v_fst_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2662_; 
v_fst_2638_ = lean_ctor_get(v_a_2634_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_a_2634_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; 
v_unused_2663_ = lean_ctor_get(v_a_2634_, 1);
lean_dec(v_unused_2663_);
v___x_2640_ = v_a_2634_;
v_isShared_2641_ = v_isSharedCheck_2662_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_fst_2638_);
lean_dec(v_a_2634_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2662_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
if (lean_obj_tag(v_fst_2638_) == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_del_object(v___x_2636_);
v___x_2642_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2643_ = l_Lean_MessageData_ofName(v___x_2627_);
lean_inc_ref(v___x_2643_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 7);
lean_ctor_set(v___x_2640_, 1, v___x_2643_);
lean_ctor_set(v___x_2640_, 0, v___x_2642_);
v___x_2645_ = v___x_2640_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2646_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_2649_ = l_Lean_indentD(v___x_2648_);
v___x_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2647_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2650_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
lean_ctor_set(v___x_2653_, 1, v___x_2643_);
v___x_2654_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2655_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2656_;
}
}
else
{
lean_object* v_val_2658_; lean_object* v___x_2660_; 
lean_del_object(v___x_2640_);
lean_dec(v___x_2627_);
lean_dec(v_stx_2407_);
v_val_2658_ = lean_ctor_get(v_fst_2638_, 0);
lean_inc(v_val_2658_);
lean_dec_ref_known(v_fst_2638_, 1);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v_val_2658_);
v___x_2660_ = v___x_2636_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_val_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v___x_2627_);
lean_dec(v_stx_2407_);
v_a_2665_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2633_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2633_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_2478_;
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_2478_;
}
}
}
else
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
lean_del_object(v___x_2471_);
v___x_5083_ = lean_unsigned_to_nat(1u);
v___x_5084_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_5083_);
lean_dec(v_stx_2407_);
v___x_5085_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_5084_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_5085_;
}
v___jp_2506_:
{
if (v___x_2505_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2513_ = lean_unsigned_to_nat(3u);
v___x_2514_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2513_);
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2516_ = l_Lean_Syntax_isOfKind(v___x_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_env_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_inc_n(v_stx_2407_, 2);
v___x_2517_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_2518_ = lean_st_ref_get(v___y_2507_);
v_env_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc_ref(v_env_2519_);
lean_dec(v___x_2518_);
v___x_2520_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2521_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2520_, v_env_2519_, v___x_2517_);
v___x_2522_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2523_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_2521_, v___x_2522_, v___y_2509_, v___y_2512_, v___y_2511_, v___y_2510_, v___y_2508_, v___y_2507_);
lean_dec(v___x_2521_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2554_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2554_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2554_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v_fst_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2552_; 
v_fst_2528_ = lean_ctor_get(v_a_2524_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_a_2524_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; 
v_unused_2553_ = lean_ctor_get(v_a_2524_, 1);
lean_dec(v_unused_2553_);
v___x_2530_ = v_a_2524_;
v_isShared_2531_ = v_isSharedCheck_2552_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_fst_2528_);
lean_dec(v_a_2524_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2552_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
if (lean_obj_tag(v_fst_2528_) == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
lean_del_object(v___x_2526_);
v___x_2532_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2533_ = l_Lean_MessageData_ofName(v___x_2517_);
lean_inc_ref(v___x_2533_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set_tag(v___x_2530_, 7);
lean_ctor_set(v___x_2530_, 1, v___x_2533_);
lean_ctor_set(v___x_2530_, 0, v___x_2532_);
v___x_2535_ = v___x_2530_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2536_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_2539_ = l_Lean_indentD(v___x_2538_);
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2537_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v___x_2533_);
v___x_2544_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2545_, v___y_2509_, v___y_2512_, v___y_2511_, v___y_2510_, v___y_2508_, v___y_2507_);
return v___x_2546_;
}
}
else
{
lean_object* v_val_2548_; lean_object* v___x_2550_; 
lean_del_object(v___x_2530_);
lean_dec(v___x_2517_);
lean_dec(v_stx_2407_);
v_val_2548_ = lean_ctor_get(v_fst_2528_, 0);
lean_inc(v_val_2548_);
lean_dec_ref_known(v_fst_2528_, 1);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v_val_2548_);
v___x_2550_ = v___x_2526_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_val_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v___x_2517_);
lean_dec(v_stx_2407_);
v_a_2555_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2523_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2523_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_2454_;
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_2454_;
}
}
v___jp_2563_:
{
if (v___x_2505_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2570_ = lean_unsigned_to_nat(2u);
v___x_2571_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2570_);
v___x_2572_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2573_ = l_Lean_Syntax_isOfKind(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v_env_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_inc_n(v_stx_2407_, 2);
v___x_2574_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_2575_ = lean_st_ref_get(v___y_2569_);
v_env_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc_ref(v_env_2576_);
lean_dec(v___x_2575_);
v___x_2577_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2578_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2577_, v_env_2576_, v___x_2574_);
v___x_2579_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2580_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_2578_, v___x_2579_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___x_2578_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2611_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2611_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2611_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v_fst_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2609_; 
v_fst_2585_ = lean_ctor_get(v_a_2581_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_a_2581_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; 
v_unused_2610_ = lean_ctor_get(v_a_2581_, 1);
lean_dec(v_unused_2610_);
v___x_2587_ = v_a_2581_;
v_isShared_2588_ = v_isSharedCheck_2609_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_fst_2585_);
lean_dec(v_a_2581_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2609_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
if (lean_obj_tag(v_fst_2585_) == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2592_; 
lean_del_object(v___x_2583_);
v___x_2589_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2590_ = l_Lean_MessageData_ofName(v___x_2574_);
lean_inc_ref(v___x_2590_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 7);
lean_ctor_set(v___x_2587_, 1, v___x_2590_);
lean_ctor_set(v___x_2587_, 0, v___x_2589_);
v___x_2592_ = v___x_2587_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2593_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_2596_ = l_Lean_indentD(v___x_2595_);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2594_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2590_);
v___x_2601_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2602_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2603_;
}
}
else
{
lean_object* v_val_2605_; lean_object* v___x_2607_; 
lean_del_object(v___x_2587_);
lean_dec(v___x_2574_);
lean_dec(v_stx_2407_);
v_val_2605_ = lean_ctor_get(v_fst_2585_, 0);
lean_inc(v_val_2605_);
lean_dec_ref_known(v_fst_2585_, 1);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v_val_2605_);
v___x_2607_ = v___x_2583_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_val_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v___x_2574_);
lean_dec(v_stx_2407_);
v_a_2612_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2580_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2580_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
v___y_2507_ = v___y_2569_;
v___y_2508_ = v___y_2568_;
v___y_2509_ = v___y_2564_;
v___y_2510_ = v___y_2567_;
v___y_2511_ = v___y_2566_;
v___y_2512_ = v___y_2565_;
goto v___jp_2506_;
}
}
else
{
v___y_2507_ = v___y_2569_;
v___y_2508_ = v___y_2568_;
v___y_2509_ = v___y_2564_;
v___y_2510_ = v___y_2567_;
v___y_2511_ = v___y_2566_;
v___y_2512_ = v___y_2565_;
goto v___jp_2506_;
}
}
}
else
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; 
lean_del_object(v___x_2471_);
v___x_5086_ = lean_unsigned_to_nat(0u);
v___x_5087_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_5086_);
lean_dec(v_stx_2407_);
v___x_5088_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_5087_);
if (lean_obj_tag(v___x_5088_) == 1)
{
lean_object* v_val_5089_; lean_object* v_snd_5090_; lean_object* v_body_5091_; lean_object* v___x_5092_; 
v_val_5089_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_val_5089_);
lean_dec_ref_known(v___x_5088_, 1);
v_snd_5090_ = lean_ctor_get(v_val_5089_, 1);
lean_inc(v_snd_5090_);
lean_dec(v_val_5089_);
v_body_5091_ = lean_ctor_get(v_snd_5090_, 1);
lean_inc(v_body_5091_);
lean_dec(v_snd_5090_);
v___x_5092_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_5091_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
if (lean_obj_tag(v___x_5092_) == 0)
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5113_; 
v_a_5093_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5095_ = v___x_5092_;
v_isShared_5096_ = v_isSharedCheck_5113_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5092_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5113_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
uint8_t v_breaks_5097_; uint8_t v_continues_5098_; uint8_t v_returnsEarly_5099_; lean_object* v_reassigns_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5111_; 
v_breaks_5097_ = lean_ctor_get_uint8(v_a_5093_, sizeof(void*)*2);
v_continues_5098_ = lean_ctor_get_uint8(v_a_5093_, sizeof(void*)*2 + 1);
v_returnsEarly_5099_ = lean_ctor_get_uint8(v_a_5093_, sizeof(void*)*2 + 2);
v_reassigns_5100_ = lean_ctor_get(v_a_5093_, 1);
v_isSharedCheck_5111_ = !lean_is_exclusive(v_a_5093_);
if (v_isSharedCheck_5111_ == 0)
{
lean_object* v_unused_5112_; 
v_unused_5112_ = lean_ctor_get(v_a_5093_, 0);
lean_dec(v_unused_5112_);
v___x_5102_ = v_a_5093_;
v_isShared_5103_ = v_isSharedCheck_5111_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_reassigns_5100_);
lean_dec(v_a_5093_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5111_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5104_; lean_object* v___x_5106_; 
v___x_5104_ = lean_unsigned_to_nat(1u);
if (v_isShared_5103_ == 0)
{
lean_ctor_set(v___x_5102_, 0, v___x_5104_);
v___x_5106_ = v___x_5102_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5104_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v_reassigns_5100_);
lean_ctor_set_uint8(v_reuseFailAlloc_5110_, sizeof(void*)*2, v_breaks_5097_);
lean_ctor_set_uint8(v_reuseFailAlloc_5110_, sizeof(void*)*2 + 1, v_continues_5098_);
lean_ctor_set_uint8(v_reuseFailAlloc_5110_, sizeof(void*)*2 + 2, v_returnsEarly_5099_);
v___x_5106_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
lean_object* v___x_5108_; 
lean_ctor_set_uint8(v___x_5106_, sizeof(void*)*2 + 3, v___x_2501_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 0, v___x_5106_);
v___x_5108_ = v___x_5095_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5106_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
}
else
{
return v___x_5092_;
}
}
else
{
lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_dec(v___x_5088_);
v___x_5114_ = lean_unsigned_to_nat(1u);
v___x_5115_ = l_Lean_NameSet_empty;
v___x_5116_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5116_, 0, v___x_5114_);
lean_ctor_set(v___x_5116_, 1, v___x_5115_);
lean_ctor_set_uint8(v___x_5116_, sizeof(void*)*2, v___x_2501_);
lean_ctor_set_uint8(v___x_5116_, sizeof(void*)*2 + 1, v___x_2501_);
lean_ctor_set_uint8(v___x_5116_, sizeof(void*)*2 + 2, v___x_2501_);
lean_ctor_set_uint8(v___x_5116_, sizeof(void*)*2 + 3, v___x_2501_);
v___x_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5117_, 0, v___x_5116_);
return v___x_5117_;
}
}
}
else
{
lean_object* v___x_5118_; lean_object* v___x_5123_; lean_object* v___x_5124_; uint8_t v___x_5125_; 
lean_del_object(v___x_2471_);
v___x_5118_ = lean_unsigned_to_nat(0u);
v___x_5123_ = lean_unsigned_to_nat(1u);
v___x_5124_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_5123_);
v___x_5125_ = l_Lean_Syntax_isNone(v___x_5124_);
if (v___x_5125_ == 0)
{
uint8_t v___x_5126_; 
v___x_5126_ = l_Lean_Syntax_matchesNull(v___x_5124_, v___x_5123_);
if (v___x_5126_ == 0)
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v_env_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; 
lean_inc_n(v_stx_2407_, 2);
v___x_5127_ = l_Lean_Syntax_getKind(v_stx_2407_);
v___x_5128_ = lean_st_ref_get(v_a_2413_);
v_env_5129_ = lean_ctor_get(v___x_5128_, 0);
lean_inc_ref(v_env_5129_);
lean_dec(v___x_5128_);
v___x_5130_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_5131_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_5130_, v_env_5129_, v___x_5127_);
v___x_5132_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_5133_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2407_, v___x_5131_, v___x_5132_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v___x_5131_);
if (lean_obj_tag(v___x_5133_) == 0)
{
lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5164_; 
v_a_5134_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5136_ = v___x_5133_;
v_isShared_5137_ = v_isSharedCheck_5164_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5133_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5164_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v_fst_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5162_; 
v_fst_5138_ = lean_ctor_get(v_a_5134_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v_a_5134_);
if (v_isSharedCheck_5162_ == 0)
{
lean_object* v_unused_5163_; 
v_unused_5163_ = lean_ctor_get(v_a_5134_, 1);
lean_dec(v_unused_5163_);
v___x_5140_ = v_a_5134_;
v_isShared_5141_ = v_isSharedCheck_5162_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_fst_5138_);
lean_dec(v_a_5134_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5162_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
if (lean_obj_tag(v_fst_5138_) == 0)
{
lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5145_; 
lean_del_object(v___x_5136_);
v___x_5142_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_5143_ = l_Lean_MessageData_ofName(v___x_5127_);
lean_inc_ref(v___x_5143_);
if (v_isShared_5141_ == 0)
{
lean_ctor_set_tag(v___x_5140_, 7);
lean_ctor_set(v___x_5140_, 1, v___x_5143_);
lean_ctor_set(v___x_5140_, 0, v___x_5142_);
v___x_5145_ = v___x_5140_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5142_);
lean_ctor_set(v_reuseFailAlloc_5157_, 1, v___x_5143_);
v___x_5145_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v___x_5146_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_5147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5147_, 0, v___x_5145_);
lean_ctor_set(v___x_5147_, 1, v___x_5146_);
v___x_5148_ = l_Lean_MessageData_ofSyntax(v_stx_2407_);
v___x_5149_ = l_Lean_indentD(v___x_5148_);
v___x_5150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5150_, 0, v___x_5147_);
lean_ctor_set(v___x_5150_, 1, v___x_5149_);
v___x_5151_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_5152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5152_, 0, v___x_5150_);
lean_ctor_set(v___x_5152_, 1, v___x_5151_);
v___x_5153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5152_);
lean_ctor_set(v___x_5153_, 1, v___x_5143_);
v___x_5154_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_5155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5153_);
lean_ctor_set(v___x_5155_, 1, v___x_5154_);
v___x_5156_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5155_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_5156_;
}
}
else
{
lean_object* v_val_5158_; lean_object* v___x_5160_; 
lean_del_object(v___x_5140_);
lean_dec(v___x_5127_);
lean_dec(v_stx_2407_);
v_val_5158_ = lean_ctor_get(v_fst_5138_, 0);
lean_inc(v_val_5158_);
lean_dec_ref_known(v_fst_5138_, 1);
if (v_isShared_5137_ == 0)
{
lean_ctor_set(v___x_5136_, 0, v_val_5158_);
v___x_5160_ = v___x_5136_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_val_5158_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_dec(v___x_5127_);
lean_dec(v_stx_2407_);
v_a_5165_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5133_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5133_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
}
}
else
{
lean_dec(v_stx_2407_);
goto v___jp_5119_;
}
}
else
{
lean_dec(v___x_5124_);
lean_dec(v_stx_2407_);
goto v___jp_5119_;
}
v___jp_5119_:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___x_5120_ = l_Lean_NameSet_empty;
v___x_5121_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5121_, 0, v___x_5118_);
lean_ctor_set(v___x_5121_, 1, v___x_5120_);
lean_ctor_set_uint8(v___x_5121_, sizeof(void*)*2, v___x_2499_);
lean_ctor_set_uint8(v___x_5121_, sizeof(void*)*2 + 1, v___x_2499_);
lean_ctor_set_uint8(v___x_5121_, sizeof(void*)*2 + 2, v___x_2497_);
lean_ctor_set_uint8(v___x_5121_, sizeof(void*)*2 + 3, v___x_2497_);
v___x_5122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5122_, 0, v___x_5121_);
return v___x_5122_;
}
}
}
else
{
lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; 
lean_del_object(v___x_2471_);
lean_dec(v_stx_2407_);
v___x_5173_ = lean_unsigned_to_nat(0u);
v___x_5174_ = l_Lean_NameSet_empty;
v___x_5175_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5175_, 0, v___x_5173_);
lean_ctor_set(v___x_5175_, 1, v___x_5174_);
lean_ctor_set_uint8(v___x_5175_, sizeof(void*)*2, v___x_2496_);
lean_ctor_set_uint8(v___x_5175_, sizeof(void*)*2 + 1, v___x_2497_);
lean_ctor_set_uint8(v___x_5175_, sizeof(void*)*2 + 2, v___x_2496_);
lean_ctor_set_uint8(v___x_5175_, sizeof(void*)*2 + 3, v___x_2497_);
v___x_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5175_);
return v___x_5176_;
}
}
else
{
lean_object* v___x_5177_; lean_object* v___x_5178_; 
lean_del_object(v___x_2471_);
lean_dec(v_stx_2407_);
v___x_5177_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95);
v___x_5178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5178_, 0, v___x_5177_);
return v___x_5178_;
}
}
v___jp_2473_:
{
lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2474_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2474_);
v___x_2476_ = v___x_2471_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
v___jp_2478_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
}
else
{
lean_object* v_a_5180_; lean_object* v___x_5182_; uint8_t v_isShared_5183_; uint8_t v_isSharedCheck_5187_; 
lean_dec(v_stx_2407_);
v_a_5180_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_5187_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_5187_ == 0)
{
v___x_5182_ = v___x_2468_;
v_isShared_5183_ = v_isSharedCheck_5187_;
goto v_resetjp_5181_;
}
else
{
lean_inc(v_a_5180_);
lean_dec(v___x_2468_);
v___x_5182_ = lean_box(0);
v_isShared_5183_ = v_isSharedCheck_5187_;
goto v_resetjp_5181_;
}
v_resetjp_5181_:
{
lean_object* v___x_5185_; 
if (v_isShared_5183_ == 0)
{
v___x_5185_ = v___x_5182_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5186_; 
v_reuseFailAlloc_5186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5186_, 0, v_a_5180_);
v___x_5185_ = v_reuseFailAlloc_5186_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
return v___x_5185_;
}
}
}
v___jp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2416_, v_bodyInfo_2417_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
v___jp_2420_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___y_2425_);
v___x_2432_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2429_, v___x_2430_, v___x_2431_, v___y_2428_, v___y_2423_, v___y_2426_, v___y_2422_, v___y_2427_, v___y_2421_, v___y_2424_);
return v___x_2432_;
}
v___jp_2433_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2440_ = lean_unsigned_to_nat(7u);
v___x_2441_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2440_);
v___x_2442_ = lean_unsigned_to_nat(8u);
v___x_2443_ = l_Lean_Syntax_getArg(v_stx_2407_, v___x_2442_);
lean_dec(v_stx_2407_);
v___x_2444_ = l_Lean_Syntax_getOptional_x3f(v___x_2443_);
lean_dec(v___x_2443_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_box(0);
v___y_2421_ = v___y_2434_;
v___y_2422_ = v___y_2436_;
v___y_2423_ = v___y_2435_;
v___y_2424_ = v___y_2437_;
v___y_2425_ = v___x_2441_;
v___y_2426_ = v___y_2438_;
v___y_2427_ = v___y_2439_;
v___y_2428_ = v___x_2445_;
goto v___jp_2420_;
}
else
{
lean_object* v_val_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
v_val_2446_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2444_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_val_2446_);
lean_dec(v___x_2444_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_val_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
v___y_2421_ = v___y_2434_;
v___y_2422_ = v___y_2436_;
v___y_2423_ = v___y_2435_;
v___y_2424_ = v___y_2437_;
v___y_2425_ = v___x_2441_;
v___y_2426_ = v___y_2438_;
v___y_2427_ = v___y_2439_;
v___y_2428_ = v___x_2451_;
goto v___jp_2420_;
}
}
}
}
v___jp_2454_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
v___jp_2457_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
return v___x_2459_;
}
v___jp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2461_, v_bodyInfo_2462_);
v___x_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_InferControlInfo_ofElem_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2407_ = stack[0].m_obj;
lean_object* v_a_2408_ = stack[1].m_obj;
lean_object* v_a_2409_ = stack[2].m_obj;
lean_object* v_a_2410_ = stack[3].m_obj;
lean_object* v_a_2411_ = stack[4].m_obj;
lean_object* v_a_2412_ = stack[5].m_obj;
lean_object* v_a_2413_ = stack[6].m_obj;
lean_object* v_res_5188_;
v_res_5188_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
stack->m_obj
 = v_res_5188_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_5189_, size_t v_sz_5190_, size_t v_i_5191_, lean_object* v_b_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
uint8_t v___x_5200_; 
v___x_5200_ = lean_usize_dec_lt(v_i_5191_, v_sz_5190_);
if (v___x_5200_ == 0)
{
lean_object* v___x_5201_; 
v___x_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5201_, 0, v_b_5192_);
return v___x_5201_;
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5203_; 
v_a_5202_ = lean_array_uget_borrowed(v_as_5189_, v_i_5191_);
lean_inc(v_a_5202_);
v___x_5203_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_5202_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
if (lean_obj_tag(v___x_5203_) == 0)
{
lean_object* v_a_5204_; lean_object* v___x_5205_; size_t v___x_5206_; size_t v___x_5207_; 
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
lean_inc(v_a_5204_);
lean_dec_ref_known(v___x_5203_, 1);
v___x_5205_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_5192_, v_a_5204_);
v___x_5206_ = ((size_t)1ULL);
v___x_5207_ = lean_usize_add(v_i_5191_, v___x_5206_);
v_i_5191_ = v___x_5207_;
v_b_5192_ = v___x_5205_;
goto _start;
}
else
{
lean_dec_ref(v_b_5192_);
return v___x_5203_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5189_ = stack[0].m_obj;
size_t v_sz_5190_ = stack[1].m_num;
size_t v_i_5191_ = stack[2].m_num;
lean_object* v_b_5192_ = stack[3].m_obj;
lean_object* v___y_5193_ = stack[4].m_obj;
lean_object* v___y_5194_ = stack[5].m_obj;
lean_object* v___y_5195_ = stack[6].m_obj;
lean_object* v___y_5196_ = stack[7].m_obj;
lean_object* v___y_5197_ = stack[8].m_obj;
lean_object* v___y_5198_ = stack[9].m_obj;
lean_object* v_res_5209_;
v_res_5209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_5189_, v_sz_5190_, v_i_5191_, v_b_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
stack->m_obj
 = v_res_5209_;
}
lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_){
_start:
{
lean_object* v_info_5218_; lean_object* v___x_5219_; size_t v_sz_5220_; size_t v___x_5221_; lean_object* v___x_5222_; 
v_info_5218_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_5219_ = l_Lean_Parser_Term_getDoElems(v_stx_5210_);
v_sz_5220_ = lean_array_size(v___x_5219_);
v___x_5221_ = ((size_t)0ULL);
v___x_5222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_5219_, v_sz_5220_, v___x_5221_, v_info_5218_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_);
lean_dec_ref(v___x_5219_);
return v___x_5222_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_InferControlInfo_ofSeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_5210_ = stack[0].m_obj;
lean_object* v_a_5211_ = stack[1].m_obj;
lean_object* v_a_5212_ = stack[2].m_obj;
lean_object* v_a_5213_ = stack[3].m_obj;
lean_object* v_a_5214_ = stack[4].m_obj;
lean_object* v_a_5215_ = stack[5].m_obj;
lean_object* v_a_5216_ = stack[6].m_obj;
lean_object* v_res_5223_;
v_res_5223_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_5210_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_);
stack->m_obj
 = v_res_5223_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_){
_start:
{
lean_object* v_res_5232_; 
v_res_5232_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_);
lean_dec(v_a_5230_);
lean_dec_ref(v_a_5229_);
lean_dec(v_a_5228_);
lean_dec_ref(v_a_5227_);
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
return v_res_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_5233_, v_a_5234_, v_a_5235_, v_a_5236_, v_a_5237_, v_a_5238_, v_a_5239_);
lean_dec(v_a_5239_);
lean_dec_ref(v_a_5238_);
lean_dec(v_a_5237_);
lean_dec_ref(v_a_5236_);
lean_dec(v_a_5235_);
lean_dec_ref(v_a_5234_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_5242_, lean_object* v_sz_5243_, lean_object* v_i_5244_, lean_object* v_b_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_){
_start:
{
size_t v_sz_boxed_5253_; size_t v_i_boxed_5254_; lean_object* v_res_5255_; 
v_sz_boxed_5253_ = lean_unbox_usize(v_sz_5243_);
lean_dec(v_sz_5243_);
v_i_boxed_5254_ = lean_unbox_usize(v_i_5244_);
lean_dec(v_i_5244_);
v_res_5255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_5242_, v_sz_boxed_5253_, v_i_boxed_5254_, v_b_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_);
lean_dec(v___y_5251_);
lean_dec_ref(v___y_5250_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec_ref(v_as_5242_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_5256_, lean_object* v_sz_5257_, lean_object* v_i_5258_, lean_object* v_b_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
size_t v_sz_boxed_5267_; size_t v_i_boxed_5268_; lean_object* v_res_5269_; 
v_sz_boxed_5267_ = lean_unbox_usize(v_sz_5257_);
lean_dec(v_sz_5257_);
v_i_boxed_5268_ = lean_unbox_usize(v_i_5258_);
lean_dec(v_i_5258_);
v_res_5269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_5256_, v_sz_boxed_5267_, v_i_boxed_5268_, v_b_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec_ref(v_as_5256_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_5270_, lean_object* v_as_5271_, lean_object* v_sz_5272_, lean_object* v_i_5273_, lean_object* v_b_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_){
_start:
{
uint8_t v___x_179481__boxed_5282_; size_t v_sz_boxed_5283_; size_t v_i_boxed_5284_; lean_object* v_res_5285_; 
v___x_179481__boxed_5282_ = lean_unbox(v___x_5270_);
v_sz_boxed_5283_ = lean_unbox_usize(v_sz_5272_);
lean_dec(v_sz_5272_);
v_i_boxed_5284_ = lean_unbox_usize(v_i_5273_);
lean_dec(v_i_5273_);
v_res_5285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_179481__boxed_5282_, v_as_5271_, v_sz_boxed_5283_, v_i_boxed_5284_, v_b_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec_ref(v___y_5277_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec_ref(v_as_5271_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_5286_, lean_object* v_as_5287_, lean_object* v_sz_5288_, lean_object* v_i_5289_, lean_object* v_b_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_){
_start:
{
uint8_t v___x_179528__boxed_5298_; size_t v_sz_boxed_5299_; size_t v_i_boxed_5300_; lean_object* v_res_5301_; 
v___x_179528__boxed_5298_ = lean_unbox(v___x_5286_);
v_sz_boxed_5299_ = lean_unbox_usize(v_sz_5288_);
lean_dec(v_sz_5288_);
v_i_boxed_5300_ = lean_unbox_usize(v_i_5289_);
lean_dec(v_i_5289_);
v_res_5301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_179528__boxed_5298_, v_as_5287_, v_sz_boxed_5299_, v_i_boxed_5300_, v_b_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
lean_dec(v___y_5296_);
lean_dec_ref(v___y_5295_);
lean_dec(v___y_5294_);
lean_dec_ref(v___y_5293_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec_ref(v_as_5287_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_5302_, lean_object* v_rhs_x3f_5303_, lean_object* v_otherwise_x3f_5304_, lean_object* v_body_x3f_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_){
_start:
{
lean_object* v_res_5313_; 
v_res_5313_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_5302_, v_rhs_x3f_5303_, v_otherwise_x3f_5304_, v_body_x3f_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_);
lean_dec(v_a_5311_);
lean_dec_ref(v_a_5310_);
lean_dec(v_a_5309_);
lean_dec_ref(v_a_5308_);
lean_dec(v_a_5307_);
lean_dec_ref(v_a_5306_);
return v_res_5313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_5314_, lean_object* v_sz_5315_, lean_object* v_i_5316_, lean_object* v_b_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
size_t v_sz_boxed_5325_; size_t v_i_boxed_5326_; lean_object* v_res_5327_; 
v_sz_boxed_5325_ = lean_unbox_usize(v_sz_5315_);
lean_dec(v_sz_5315_);
v_i_boxed_5326_ = lean_unbox_usize(v_i_5316_);
lean_dec(v_i_5316_);
v_res_5327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_5314_, v_sz_boxed_5325_, v_i_boxed_5326_, v_b_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
lean_dec(v___y_5323_);
lean_dec_ref(v___y_5322_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec_ref(v_as_5314_);
return v_res_5327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_5328_, lean_object* v_decl_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_){
_start:
{
uint8_t v_reassignment_boxed_5337_; lean_object* v_res_5338_; 
v_reassignment_boxed_5337_ = lean_unbox(v_reassignment_5328_);
v_res_5338_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_5337_, v_decl_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
lean_dec(v_a_5335_);
lean_dec_ref(v_a_5334_);
lean_dec(v_a_5333_);
lean_dec_ref(v_a_5332_);
lean_dec(v_a_5331_);
lean_dec_ref(v_a_5330_);
return v_res_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_);
lean_dec(v_a_5345_);
lean_dec_ref(v_a_5344_);
lean_dec(v_a_5343_);
lean_dec_ref(v_a_5342_);
lean_dec(v_a_5341_);
lean_dec_ref(v_a_5340_);
return v_res_5347_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object* v_00_u03b1_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_){
_start:
{
lean_object* v___x_5356_; 
v___x_5356_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_5356_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5349_ = stack[1].m_obj;
lean_object* v___y_5350_ = stack[2].m_obj;
lean_object* v___y_5351_ = stack[3].m_obj;
lean_object* v___y_5352_ = stack[4].m_obj;
lean_object* v___y_5353_ = stack[5].m_obj;
lean_object* v___y_5354_ = stack[6].m_obj;
lean_object* v_res_5357_;
v_res_5357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_box(0), v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
stack->m_obj
 = v_res_5357_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_00_u03b1_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_00_u03b1_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec(v___y_5360_);
lean_dec_ref(v___y_5359_);
return v_res_5366_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_5367_, lean_object* v_ref_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_){
_start:
{
lean_object* v___x_5376_; 
v___x_5376_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_5368_);
return v___x_5376_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_5368_ = stack[1].m_obj;
lean_object* v___y_5369_ = stack[2].m_obj;
lean_object* v___y_5370_ = stack[3].m_obj;
lean_object* v___y_5371_ = stack[4].m_obj;
lean_object* v___y_5372_ = stack[5].m_obj;
lean_object* v___y_5373_ = stack[6].m_obj;
lean_object* v___y_5374_ = stack[7].m_obj;
lean_object* v_res_5377_;
v_res_5377_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_box(0), v_ref_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
stack->m_obj
 = v_res_5377_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_5378_, lean_object* v_ref_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v_res_5387_; 
v_res_5387_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_5378_, v_ref_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
lean_dec_ref(v___y_5380_);
return v_res_5387_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_5388_, lean_object* v_x_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_){
_start:
{
lean_object* v___x_5397_; 
v___x_5397_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_);
return v___x_5397_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5389_ = stack[1].m_obj;
lean_object* v___y_5390_ = stack[2].m_obj;
lean_object* v___y_5391_ = stack[3].m_obj;
lean_object* v___y_5392_ = stack[4].m_obj;
lean_object* v___y_5393_ = stack[5].m_obj;
lean_object* v___y_5394_ = stack[6].m_obj;
lean_object* v___y_5395_ = stack[7].m_obj;
lean_object* v_res_5398_;
v_res_5398_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_box(0), v_x_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_);
stack->m_obj
 = v_res_5398_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_5399_, lean_object* v_x_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_){
_start:
{
lean_object* v_res_5408_; 
v_res_5408_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_5399_, v_x_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
lean_dec(v___y_5406_);
lean_dec_ref(v___y_5405_);
lean_dec(v___y_5404_);
lean_dec_ref(v___y_5403_);
lean_dec(v___y_5402_);
lean_dec_ref(v___y_5401_);
return v_res_5408_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_5409_, lean_object* v_as_5410_, lean_object* v_as_x27_5411_, lean_object* v_b_5412_, lean_object* v_a_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
lean_object* v___x_5421_; 
v___x_5421_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_5409_, v_as_x27_5411_, v_b_5412_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
return v___x_5421_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_5409_ = stack[0].m_obj;
lean_object* v_as_5410_ = stack[1].m_obj;
lean_object* v_as_x27_5411_ = stack[2].m_obj;
lean_object* v_b_5412_ = stack[3].m_obj;
lean_object* v___y_5414_ = stack[5].m_obj;
lean_object* v___y_5415_ = stack[6].m_obj;
lean_object* v___y_5416_ = stack[7].m_obj;
lean_object* v___y_5417_ = stack[8].m_obj;
lean_object* v___y_5418_ = stack[9].m_obj;
lean_object* v___y_5419_ = stack[10].m_obj;
lean_object* v_res_5422_;
v_res_5422_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_5409_, v_as_5410_, v_as_x27_5411_, v_b_5412_, lean_box(0), v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
stack->m_obj
 = v_res_5422_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_5423_, lean_object* v_as_5424_, lean_object* v_as_x27_5425_, lean_object* v_b_5426_, lean_object* v_a_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_){
_start:
{
lean_object* v_res_5435_; 
v_res_5435_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_5423_, v_as_5424_, v_as_x27_5425_, v_b_5426_, v_a_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
lean_dec(v___y_5433_);
lean_dec_ref(v___y_5432_);
lean_dec(v___y_5431_);
lean_dec_ref(v___y_5430_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v_as_x27_5425_);
lean_dec(v_as_5424_);
return v_res_5435_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_5436_, lean_object* v_msg_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_){
_start:
{
lean_object* v___x_5445_; 
v___x_5445_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_);
return v___x_5445_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_5437_ = stack[1].m_obj;
lean_object* v___y_5438_ = stack[2].m_obj;
lean_object* v___y_5439_ = stack[3].m_obj;
lean_object* v___y_5440_ = stack[4].m_obj;
lean_object* v___y_5441_ = stack[5].m_obj;
lean_object* v___y_5442_ = stack[6].m_obj;
lean_object* v___y_5443_ = stack[7].m_obj;
lean_object* v_res_5446_;
v_res_5446_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_box(0), v_msg_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_);
stack->m_obj
 = v_res_5446_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_5447_, lean_object* v_msg_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_){
_start:
{
lean_object* v_res_5456_; 
v_res_5456_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_5447_, v_msg_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_);
lean_dec(v___y_5454_);
lean_dec_ref(v___y_5453_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
return v_res_5456_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_5457_, lean_object* v_msg_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_){
_start:
{
lean_object* v___x_5466_; 
v___x_5466_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_5457_, v_msg_5458_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
return v___x_5466_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_5457_ = stack[0].m_obj;
lean_object* v_msg_5458_ = stack[1].m_obj;
lean_object* v___y_5459_ = stack[2].m_obj;
lean_object* v___y_5460_ = stack[3].m_obj;
lean_object* v___y_5461_ = stack[4].m_obj;
lean_object* v___y_5462_ = stack[5].m_obj;
lean_object* v___y_5463_ = stack[6].m_obj;
lean_object* v___y_5464_ = stack[7].m_obj;
lean_object* v_res_5467_;
v_res_5467_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_5457_, v_msg_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
stack->m_obj
 = v_res_5467_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_5468_, lean_object* v_msg_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v_res_5477_; 
v_res_5477_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_5468_, v_msg_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec_ref(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
return v_res_5477_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_5478_, lean_object* v_as_x27_5479_, lean_object* v_b_5480_, lean_object* v_a_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_){
_start:
{
lean_object* v___x_5489_; 
v___x_5489_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_5479_, v_b_5480_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_);
return v___x_5489_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5478_ = stack[0].m_obj;
lean_object* v_as_x27_5479_ = stack[1].m_obj;
lean_object* v_b_5480_ = stack[2].m_obj;
lean_object* v___y_5482_ = stack[4].m_obj;
lean_object* v___y_5483_ = stack[5].m_obj;
lean_object* v___y_5484_ = stack[6].m_obj;
lean_object* v___y_5485_ = stack[7].m_obj;
lean_object* v___y_5486_ = stack[8].m_obj;
lean_object* v___y_5487_ = stack[9].m_obj;
lean_object* v_res_5490_;
v_res_5490_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_5478_, v_as_x27_5479_, v_b_5480_, lean_box(0), v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_);
stack->m_obj
 = v_res_5490_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_5491_, lean_object* v_as_x27_5492_, lean_object* v_b_5493_, lean_object* v_a_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_){
_start:
{
lean_object* v_res_5502_; 
v_res_5502_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_5491_, v_as_x27_5492_, v_b_5493_, v_a_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_);
lean_dec(v___y_5500_);
lean_dec_ref(v___y_5499_);
lean_dec(v___y_5498_);
lean_dec_ref(v___y_5497_);
lean_dec(v___y_5496_);
lean_dec_ref(v___y_5495_);
lean_dec(v_as_x27_5492_);
lean_dec(v_as_5491_);
return v_res_5502_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_5503_, lean_object* v_ref_5504_, lean_object* v_msg_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_){
_start:
{
lean_object* v___x_5513_; 
v___x_5513_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_5504_, v_msg_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_);
return v___x_5513_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_5504_ = stack[1].m_obj;
lean_object* v_msg_5505_ = stack[2].m_obj;
lean_object* v___y_5506_ = stack[3].m_obj;
lean_object* v___y_5507_ = stack[4].m_obj;
lean_object* v___y_5508_ = stack[5].m_obj;
lean_object* v___y_5509_ = stack[6].m_obj;
lean_object* v___y_5510_ = stack[7].m_obj;
lean_object* v___y_5511_ = stack[8].m_obj;
lean_object* v_res_5514_;
v_res_5514_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_box(0), v_ref_5504_, v_msg_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_);
stack->m_obj
 = v_res_5514_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_5515_, lean_object* v_ref_5516_, lean_object* v_msg_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_){
_start:
{
lean_object* v_res_5525_; 
v_res_5525_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_5515_, v_ref_5516_, v_msg_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v_ref_5516_);
return v_res_5525_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_5526_, lean_object* v_macroStack_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_){
_start:
{
lean_object* v___x_5535_; 
v___x_5535_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_5526_, v_macroStack_5527_, v___y_5532_);
return v___x_5535_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_5526_ = stack[0].m_obj;
lean_object* v_macroStack_5527_ = stack[1].m_obj;
lean_object* v___y_5528_ = stack[2].m_obj;
lean_object* v___y_5529_ = stack[3].m_obj;
lean_object* v___y_5530_ = stack[4].m_obj;
lean_object* v___y_5531_ = stack[5].m_obj;
lean_object* v___y_5532_ = stack[6].m_obj;
lean_object* v___y_5533_ = stack[7].m_obj;
lean_object* v_res_5536_;
v_res_5536_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_5526_, v_macroStack_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_);
stack->m_obj
 = v_res_5536_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_5537_, lean_object* v_macroStack_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_){
_start:
{
lean_object* v_res_5546_; 
v_res_5546_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_5537_, v_macroStack_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec(v___y_5542_);
lean_dec_ref(v___y_5541_);
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
return v_res_5546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_5547_, lean_object* v_m_5548_, lean_object* v_a_5549_){
_start:
{
lean_object* v___x_5550_; 
v___x_5550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_5548_, v_a_5549_);
return v___x_5550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_5551_, lean_object* v_m_5552_, lean_object* v_a_5553_){
_start:
{
lean_object* v_res_5554_; 
v_res_5554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_5551_, v_m_5552_, v_a_5553_);
lean_dec(v_a_5553_);
lean_dec_ref(v_m_5552_);
return v_res_5554_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_5555_, lean_object* v_x_5556_, lean_object* v_x_5557_){
_start:
{
uint8_t v___x_5558_; 
v___x_5558_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_5556_, v_x_5557_);
return v___x_5558_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5556_ = stack[1].m_obj;
lean_object* v_x_5557_ = stack[2].m_obj;
uint8_t v_res_5559_;
v_res_5559_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_box(0), v_x_5556_, v_x_5557_);
stack->m_num = v_res_5559_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_5560_, lean_object* v_x_5561_, lean_object* v_x_5562_){
_start:
{
uint8_t v_res_5563_; lean_object* v_r_5564_; 
v_res_5563_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_5560_, v_x_5561_, v_x_5562_);
lean_dec_ref(v_x_5562_);
lean_dec_ref(v_x_5561_);
v_r_5564_ = lean_box(v_res_5563_);
return v_r_5564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_5565_, lean_object* v_a_5566_, lean_object* v_x_5567_){
_start:
{
lean_object* v___x_5568_; 
v___x_5568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_5566_, v_x_5567_);
return v___x_5568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_5569_, lean_object* v_a_5570_, lean_object* v_x_5571_){
_start:
{
lean_object* v_res_5572_; 
v_res_5572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_5569_, v_a_5570_, v_x_5571_);
lean_dec(v_x_5571_);
lean_dec(v_a_5570_);
return v_res_5572_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_5573_, lean_object* v_x_5574_, size_t v_x_5575_, lean_object* v_x_5576_){
_start:
{
uint8_t v___x_5577_; 
v___x_5577_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_5574_, v_x_5575_, v_x_5576_);
return v___x_5577_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5574_ = stack[1].m_obj;
size_t v_x_5575_ = stack[2].m_num;
lean_object* v_x_5576_ = stack[3].m_obj;
uint8_t v_res_5578_;
v_res_5578_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_box(0), v_x_5574_, v_x_5575_, v_x_5576_);
stack->m_num = v_res_5578_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_5579_, lean_object* v_x_5580_, lean_object* v_x_5581_, lean_object* v_x_5582_){
_start:
{
size_t v_x_190314__boxed_5583_; uint8_t v_res_5584_; lean_object* v_r_5585_; 
v_x_190314__boxed_5583_ = lean_unbox_usize(v_x_5581_);
lean_dec(v_x_5581_);
v_res_5584_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_5579_, v_x_5580_, v_x_190314__boxed_5583_, v_x_5582_);
lean_dec_ref(v_x_5582_);
lean_dec_ref(v_x_5580_);
v_r_5585_ = lean_box(v_res_5584_);
return v_r_5585_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_5586_, lean_object* v_keys_5587_, lean_object* v_vals_5588_, lean_object* v_heq_5589_, lean_object* v_i_5590_, lean_object* v_k_5591_){
_start:
{
uint8_t v___x_5592_; 
v___x_5592_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_5587_, v_i_5590_, v_k_5591_);
return v___x_5592_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_5587_ = stack[1].m_obj;
lean_object* v_vals_5588_ = stack[2].m_obj;
lean_object* v_i_5590_ = stack[4].m_obj;
lean_object* v_k_5591_ = stack[5].m_obj;
uint8_t v_res_5593_;
v_res_5593_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_box(0), v_keys_5587_, v_vals_5588_, lean_box(0), v_i_5590_, v_k_5591_);
stack->m_num = v_res_5593_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_5594_, lean_object* v_keys_5595_, lean_object* v_vals_5596_, lean_object* v_heq_5597_, lean_object* v_i_5598_, lean_object* v_k_5599_){
_start:
{
uint8_t v_res_5600_; lean_object* v_r_5601_; 
v_res_5600_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_5594_, v_keys_5595_, v_vals_5596_, v_heq_5597_, v_i_5598_, v_k_5599_);
lean_dec_ref(v_k_5599_);
lean_dec_ref(v_vals_5596_);
lean_dec_ref(v_keys_5595_);
v_r_5601_ = lean_box(v_res_5600_);
return v_r_5601_;
}
}
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_){
_start:
{
lean_object* v___x_5610_; 
v___x_5610_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_5602_, v_a_5603_, v_a_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_);
return v___x_5610_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_inferControlInfoSeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_doSeq_5602_ = stack[0].m_obj;
lean_object* v_a_5603_ = stack[1].m_obj;
lean_object* v_a_5604_ = stack[2].m_obj;
lean_object* v_a_5605_ = stack[3].m_obj;
lean_object* v_a_5606_ = stack[4].m_obj;
lean_object* v_a_5607_ = stack[5].m_obj;
lean_object* v_a_5608_ = stack[6].m_obj;
lean_object* v_res_5611_;
v_res_5611_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_5602_, v_a_5603_, v_a_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_);
stack->m_obj
 = v_res_5611_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_){
_start:
{
lean_object* v_res_5620_; 
v_res_5620_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_5612_, v_a_5613_, v_a_5614_, v_a_5615_, v_a_5616_, v_a_5617_, v_a_5618_);
lean_dec(v_a_5618_);
lean_dec_ref(v_a_5617_);
lean_dec(v_a_5616_);
lean_dec_ref(v_a_5615_);
lean_dec(v_a_5614_);
lean_dec_ref(v_a_5613_);
return v_res_5620_;
}
}
lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_){
_start:
{
lean_object* v___x_5629_; 
v___x_5629_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_);
return v___x_5629_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_inferControlInfoElem_0interp(lean_interpreter_value* stack)
{
lean_object* v_doElem_5621_ = stack[0].m_obj;
lean_object* v_a_5622_ = stack[1].m_obj;
lean_object* v_a_5623_ = stack[2].m_obj;
lean_object* v_a_5624_ = stack[3].m_obj;
lean_object* v_a_5625_ = stack[4].m_obj;
lean_object* v_a_5626_ = stack[5].m_obj;
lean_object* v_a_5627_ = stack[6].m_obj;
lean_object* v_res_5630_;
v_res_5630_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_);
stack->m_obj
 = v_res_5630_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_);
lean_dec(v_a_5637_);
lean_dec_ref(v_a_5636_);
lean_dec(v_a_5635_);
lean_dec_ref(v_a_5634_);
lean_dec(v_a_5633_);
lean_dec_ref(v_a_5632_);
return v_res_5639_;
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
