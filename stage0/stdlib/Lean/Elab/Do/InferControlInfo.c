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
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 239, .m_capacity = 239, .m_length = 236, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `DoElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`.\n"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(118) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(125) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(125) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doSkip"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalSyntax"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(117, 4, 119, 3, 13, 160, 149, 47)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_3),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value),LEAN_SCALAR_PTR_LITERAL(125, 157, 182, 149, 109, 63, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doAssertion"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value),LEAN_SCALAR_PTR_LITERAL(144, 179, 243, 245, 156, 230, 227, 142)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "doForInvariant"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value),LEAN_SCALAR_PTR_LITERAL(21, 233, 74, 150, 27, 16, 165, 242)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87;
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_25_; lean_object* v___y_26_; uint8_t v___y_27_; uint8_t v___y_28_; uint8_t v___y_29_; uint8_t v___y_30_; uint8_t v___y_36_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_45_; uint8_t v___y_46_; uint8_t v___y_49_; 
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
v___x_31_ = l_Lean_NameSet_append(v_reassigns_20_, v___y_26_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_31_);
lean_ctor_set(v___x_22_, 0, v___y_25_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___y_25_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2, v___y_28_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 1, v___y_29_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 2, v___y_27_);
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
v___y_25_ = v_numRegularExits_39_;
v___y_26_ = v_reassigns_41_;
v___y_27_ = v___y_38_;
v___y_28_ = v___y_36_;
v___y_29_ = v___y_37_;
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
v___y_25_ = v_numRegularExits_42_;
v___y_26_ = v_reassigns_43_;
v___y_27_ = v___y_38_;
v___y_28_ = v___y_36_;
v___y_29_ = v___y_37_;
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
v___y_36_ = v___y_45_;
v___y_37_ = v___y_46_;
v___y_38_ = v_returnsEarly_47_;
goto v___jp_35_;
}
else
{
v___y_36_ = v___y_45_;
v___y_37_ = v___y_46_;
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
uint8_t v___y_57_; uint8_t v___y_58_; uint8_t v___y_59_; lean_object* v___y_60_; lean_object* v___y_61_; lean_object* v___y_62_; uint8_t v___y_63_; uint8_t v_breaks_66_; uint8_t v_continues_67_; uint8_t v_returnsEarly_68_; lean_object* v_numRegularExits_69_; uint8_t v_noFallthrough_70_; lean_object* v_reassigns_71_; uint8_t v___y_73_; uint8_t v___y_74_; uint8_t v___y_75_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_85_; 
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
v___x_64_ = l_Lean_NameSet_append(v___y_60_, v___y_61_);
v___x_65_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_65_, 0, v___y_62_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___y_59_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 1, v___y_58_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 2, v___y_57_);
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
v___y_57_ = v___y_75_;
v___y_58_ = v___y_73_;
v___y_59_ = v___y_74_;
v___y_60_ = v_reassigns_71_;
v___y_61_ = v_reassigns_78_;
v___y_62_ = v___x_79_;
v___y_63_ = v_noFallthrough_70_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___y_75_;
v___y_58_ = v___y_73_;
v___y_59_ = v___y_74_;
v___y_60_ = v_reassigns_71_;
v___y_61_ = v_reassigns_78_;
v___y_62_ = v___x_79_;
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
lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v___x_290_; lean_object* v_mctx_291_; lean_object* v_lctx_292_; lean_object* v_options_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = lean_st_ref_get(v___y_284_);
v_mctx_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_mctx_291_);
lean_dec(v___x_290_);
v_lctx_292_ = lean_ctor_get(v___y_283_, 2);
v_options_293_ = lean_ctor_get(v___y_285_, 2);
lean_inc_ref(v_options_293_);
lean_inc_ref(v_lctx_292_);
v___x_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_294_, 0, v_env_289_);
lean_ctor_set(v___x_294_, 1, v_mctx_291_);
lean_ctor_set(v___x_294_, 2, v_lctx_292_);
lean_ctor_set(v___x_294_, 3, v_options_293_);
v___x_295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_msgData_282_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_box(1);
v___x_305_ = l_Lean_MessageData_ofFormat(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_310_ = l_Lean_MessageData_ofFormat(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_312_) == 0)
{
return v_x_311_;
}
else
{
lean_object* v_head_313_; lean_object* v_tail_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_336_; 
v_head_313_ = lean_ctor_get(v_x_312_, 0);
v_tail_314_ = lean_ctor_get(v_x_312_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_312_);
if (v_isSharedCheck_336_ == 0)
{
v___x_316_ = v_x_312_;
v_isShared_317_ = v_isSharedCheck_336_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_tail_314_);
lean_inc(v_head_313_);
lean_dec(v_x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_336_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_before_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_334_; 
v_before_318_ = lean_ctor_get(v_head_313_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_head_313_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_head_313_, 1);
lean_dec(v_unused_335_);
v___x_320_ = v_head_313_;
v_isShared_321_ = v_isSharedCheck_334_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_before_318_);
lean_dec(v_head_313_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_334_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 7);
lean_ctor_set(v___x_320_, 1, v___x_322_);
lean_ctor_set(v___x_320_, 0, v_x_311_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_x_311_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_333_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 7);
lean_ctor_set(v___x_316_, 1, v___x_325_);
lean_ctor_set(v___x_316_, 0, v___x_324_);
v___x_327_ = v___x_316_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_332_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = l_Lean_MessageData_ofSyntax(v_before_318_);
v___x_329_ = l_Lean_indentD(v___x_328_);
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_327_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v_x_311_ = v___x_330_;
v_x_312_ = v_tail_314_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_337_, lean_object* v_opt_338_){
_start:
{
lean_object* v_name_339_; lean_object* v_defValue_340_; lean_object* v_map_341_; lean_object* v___x_342_; 
v_name_339_ = lean_ctor_get(v_opt_338_, 0);
v_defValue_340_ = lean_ctor_get(v_opt_338_, 1);
v_map_341_ = lean_ctor_get(v_opts_337_, 0);
v___x_342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_341_, v_name_339_);
if (lean_obj_tag(v___x_342_) == 0)
{
uint8_t v___x_343_; 
v___x_343_ = lean_unbox(v_defValue_340_);
return v___x_343_;
}
else
{
lean_object* v_val_344_; 
v_val_344_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_val_344_);
lean_dec_ref_known(v___x_342_, 1);
if (lean_obj_tag(v_val_344_) == 1)
{
uint8_t v_v_345_; 
v_v_345_ = lean_ctor_get_uint8(v_val_344_, 0);
lean_dec_ref_known(v_val_344_, 0);
return v_v_345_;
}
else
{
uint8_t v___x_346_; 
lean_dec(v_val_344_);
v___x_346_ = lean_unbox(v_defValue_340_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_347_, lean_object* v_opt_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_347_, v_opt_348_);
lean_dec_ref(v_opt_348_);
lean_dec_ref(v_opts_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_355_ = l_Lean_MessageData_ofFormat(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_356_, lean_object* v_macroStack_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_options_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_options_360_ = lean_ctor_get(v___y_358_, 2);
v___x_361_ = l_Lean_Elab_pp_macroStack;
v___x_362_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_options_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v_macroStack_357_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_msgData_356_);
return v___x_363_;
}
else
{
if (lean_obj_tag(v_macroStack_357_) == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_msgData_356_);
return v___x_364_;
}
else
{
lean_object* v_head_365_; lean_object* v_after_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_381_; 
v_head_365_ = lean_ctor_get(v_macroStack_357_, 0);
lean_inc(v_head_365_);
v_after_366_ = lean_ctor_get(v_head_365_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_head_365_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_head_365_, 0);
lean_dec(v_unused_382_);
v___x_368_ = v_head_365_;
v_isShared_369_ = v_isSharedCheck_381_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_after_366_);
lean_dec(v_head_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_381_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 7);
lean_ctor_set(v___x_368_, 1, v___x_370_);
lean_ctor_set(v___x_368_, 0, v_msgData_356_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_msgData_356_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_380_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_msgData_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_373_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_Lean_MessageData_ofSyntax(v_after_366_);
v___x_376_ = l_Lean_indentD(v___x_375_);
v_msgData_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_377_, 0, v___x_374_);
lean_ctor_set(v_msgData_377_, 1, v___x_376_);
v___x_378_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_377_, v_macroStack_357_);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_383_, lean_object* v_macroStack_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_383_, v_macroStack_384_, v___y_385_);
lean_dec_ref(v___y_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v_a_398_; lean_object* v_macroStack_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_ref_396_ = lean_ctor_get(v___y_393_, 5);
v___x_397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_388_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v___x_397_);
v_macroStack_399_ = lean_ctor_get(v___y_389_, 1);
v___x_400_ = l_Lean_Elab_getBetterRef(v_ref_396_, v_macroStack_399_);
lean_inc(v_macroStack_399_);
v___x_401_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_398_, v_macroStack_399_, v___y_393_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_400_);
lean_ctor_set(v___x_406_, 1, v_a_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_420_, size_t v_i_421_, size_t v_stop_422_, lean_object* v_b_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_eq(v_i_421_, v_stop_422_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; 
v___x_425_ = lean_array_uget_borrowed(v_as_420_, v_i_421_);
lean_inc(v___x_425_);
v___x_426_ = l_Lean_NameSet_insert(v_b_423_, v___x_425_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_421_, v___x_427_);
v_i_421_ = v___x_428_;
v_b_423_ = v___x_426_;
goto _start;
}
else
{
return v_b_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_430_, lean_object* v_i_431_, lean_object* v_stop_432_, lean_object* v_b_433_){
_start:
{
size_t v_i_boxed_434_; size_t v_stop_boxed_435_; lean_object* v_res_436_; 
v_i_boxed_434_ = lean_unbox_usize(v_i_431_);
lean_dec(v_i_431_);
v_stop_boxed_435_ = lean_unbox_usize(v_stop_432_);
lean_dec(v_stop_432_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_430_, v_i_boxed_434_, v_stop_boxed_435_, v_b_433_);
lean_dec_ref(v_as_430_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_437_, size_t v_i_438_, lean_object* v_bs_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_438_, v_sz_437_);
if (v___x_440_ == 0)
{
return v_bs_439_;
}
else
{
lean_object* v_v_441_; lean_object* v___x_442_; lean_object* v_bs_x27_443_; lean_object* v___x_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v_v_441_ = lean_array_uget(v_bs_439_, v_i_438_);
v___x_442_ = lean_unsigned_to_nat(0u);
v_bs_x27_443_ = lean_array_uset(v_bs_439_, v_i_438_, v___x_442_);
v___x_444_ = l_Lean_TSyntax_getId(v_v_441_);
lean_dec(v_v_441_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_438_, v___x_445_);
v___x_447_ = lean_array_uset(v_bs_x27_443_, v_i_438_, v___x_444_);
v_i_438_ = v___x_446_;
v_bs_439_ = v___x_447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_449_, lean_object* v_i_450_, lean_object* v_bs_451_){
_start:
{
size_t v_sz_boxed_452_; size_t v_i_boxed_453_; lean_object* v_res_454_; 
v_sz_boxed_452_ = lean_unbox_usize(v_sz_449_);
lean_dec(v_sz_449_);
v_i_boxed_453_ = lean_unbox_usize(v_i_450_);
lean_dec(v_i_450_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_452_, v_i_boxed_453_, v_bs_451_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_box(0);
v___x_456_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg(){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t v_sz_463_, size_t v_i_464_, lean_object* v_bs_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_usize_dec_lt(v_i_464_, v_sz_463_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v_bs_465_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v_bs_x27_469_; lean_object* v___x_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v_bs_x27_469_ = lean_array_uset(v_bs_465_, v_i_464_, v___x_468_);
v___x_470_ = lean_box(0);
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_add(v_i_464_, v___x_471_);
v___x_473_ = lean_array_uset(v_bs_x27_469_, v_i_464_, v___x_470_);
v_i_464_ = v___x_472_;
v_bs_465_ = v___x_473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_bs_477_){
_start:
{
size_t v_sz_boxed_478_; size_t v_i_boxed_479_; lean_object* v_res_480_; 
v_sz_boxed_478_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_479_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_boxed_478_, v_i_boxed_479_, v_bs_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_481_, uint8_t v___x_482_, lean_object* v_as_483_, size_t v_i_484_, size_t v_stop_485_, lean_object* v_b_486_){
_start:
{
lean_object* v___y_488_; uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_eq(v_i_484_, v_stop_485_);
if (v___x_492_ == 0)
{
lean_object* v_fst_493_; uint8_t v___x_494_; 
v_fst_493_ = lean_ctor_get(v_b_486_, 0);
v___x_494_ = lean_unbox(v_fst_493_);
if (v___x_494_ == 0)
{
lean_object* v_snd_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_snd_495_ = lean_ctor_get(v_b_486_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_b_486_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_b_486_, 0);
lean_dec(v_unused_504_);
v___x_497_ = v_b_486_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_snd_495_);
lean_dec(v_b_486_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_box(v___x_481_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_499_);
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_snd_495_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
v___y_488_ = v___x_501_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v_snd_505_ = lean_ctor_get(v_b_486_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_b_486_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_b_486_, 0);
lean_dec(v_unused_516_);
v___x_507_ = v_b_486_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_dec(v_b_486_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_509_ = lean_array_uget_borrowed(v_as_483_, v_i_484_);
lean_inc(v___x_509_);
v___x_510_ = lean_array_push(v_snd_505_, v___x_509_);
v___x_511_ = lean_box(v___x_482_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_510_);
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_510_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v___y_488_ = v___x_513_;
goto v___jp_487_;
}
}
}
}
else
{
return v_b_486_;
}
v___jp_487_:
{
size_t v___x_489_; size_t v___x_490_; 
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_484_, v___x_489_);
v_i_484_ = v___x_490_;
v_b_486_ = v___y_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v_as_519_, lean_object* v_i_520_, lean_object* v_stop_521_, lean_object* v_b_522_){
_start:
{
uint8_t v___x_298184__boxed_523_; uint8_t v___x_298185__boxed_524_; size_t v_i_boxed_525_; size_t v_stop_boxed_526_; lean_object* v_res_527_; 
v___x_298184__boxed_523_ = lean_unbox(v___x_517_);
v___x_298185__boxed_524_ = lean_unbox(v___x_518_);
v_i_boxed_525_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_521_);
lean_dec(v_stop_521_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_298184__boxed_523_, v___x_298185__boxed_524_, v_as_519_, v_i_boxed_525_, v_stop_boxed_526_, v_b_522_);
lean_dec_ref(v_as_519_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_528_, lean_object* v_declName_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___x_532_; lean_object* v_env_533_; lean_object* v___x_534_; uint8_t v___x_535_; uint8_t v___x_536_; 
v___x_532_ = 0;
v_env_533_ = l_Lean_Environment_setExporting(v_env_528_, v___x_532_);
lean_inc(v_declName_529_);
v___x_534_ = l_Lean_mkPrivateName(v_env_533_, v_declName_529_);
v___x_535_ = 1;
lean_inc_ref(v_env_533_);
v___x_536_ = l_Lean_Environment_contains(v_env_533_, v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = l_Lean_privateToUserName(v_declName_529_);
v___x_538_ = l_Lean_Environment_contains(v_env_533_, v___x_537_, v___x_535_);
v___x_539_ = lean_box(v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___y_531_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec_ref(v_env_533_);
lean_dec(v_declName_529_);
v___x_541_ = lean_box(v___x_536_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___y_531_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_543_, lean_object* v_declName_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_543_, v_declName_544_, v___y_545_, v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_547_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = l_Lean_maxRecDepthErrorMessage;
v___x_554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_556_ = l_Lean_MessageData_ofFormat(v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_558_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_559_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_560_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_ref_560_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_570_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_a_570_);
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v_a_570_);
lean_ctor_set(v___x_571_, 1, v___y_569_);
return v___x_571_;
}
else
{
lean_object* v_a_572_; lean_object* v___x_573_; 
v_a_572_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_a_572_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_a_572_);
lean_ctor_set(v___x_573_, 1, v___y_569_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_574_, v___y_575_);
lean_dec_ref(v_x_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_577_, lean_object* v_stx_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_577_, v_stx_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
if (lean_obj_tag(v_a_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_591_; 
v_a_583_ = lean_ctor_get(v___x_581_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_581_, 0);
lean_dec(v_unused_592_);
v___x_585_ = v___x_581_;
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_581_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_a_583_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_val_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_621_; 
v_val_593_ = lean_ctor_get(v_a_582_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_a_582_);
if (v_isSharedCheck_621_ == 0)
{
v___x_595_ = v_a_582_;
v_isShared_596_ = v_isSharedCheck_621_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_val_593_);
lean_dec(v_a_582_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_621_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_snd_597_; 
v_snd_597_ = lean_ctor_get(v_val_593_, 1);
lean_inc(v_snd_597_);
lean_dec(v_val_593_);
if (lean_obj_tag(v_snd_597_) == 0)
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
lean_del_object(v___x_595_);
v_a_598_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_581_, 2);
v_a_599_ = lean_ctor_get(v_snd_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_snd_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v_snd_597_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v_snd_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
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
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_604_, v_a_598_);
lean_dec_ref(v___x_604_);
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_620_; 
v_a_608_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_581_, 2);
v_a_609_ = lean_ctor_get(v_snd_597_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_snd_597_);
if (v_isSharedCheck_620_ == 0)
{
v___x_611_ = v_snd_597_;
v_isShared_612_ = v_isSharedCheck_620_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v_snd_597_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_620_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_a_609_);
v___x_614_ = v___x_595_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_619_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_618_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_616_, v_a_608_);
lean_dec_ref(v___x_616_);
return v___x_617_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_622_ = lean_ctor_get(v___x_581_, 0);
v_a_623_ = lean_ctor_get(v___x_581_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_581_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_inc(v_a_622_);
lean_dec(v___x_581_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_622_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_631_, lean_object* v_stx_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_631_, v_stx_632_, v___y_633_, v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_636_, lean_object* v_msg_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_fileName_645_; lean_object* v_fileMap_646_; lean_object* v_options_647_; lean_object* v_currRecDepth_648_; lean_object* v_maxRecDepth_649_; lean_object* v_ref_650_; lean_object* v_currNamespace_651_; lean_object* v_openDecls_652_; lean_object* v_initHeartbeats_653_; lean_object* v_maxHeartbeats_654_; lean_object* v_quotContext_655_; lean_object* v_currMacroScope_656_; uint8_t v_diag_657_; lean_object* v_cancelTk_x3f_658_; uint8_t v_suppressElabErrors_659_; lean_object* v_inheritedTraceOptions_660_; lean_object* v_ref_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_fileName_645_ = lean_ctor_get(v___y_642_, 0);
v_fileMap_646_ = lean_ctor_get(v___y_642_, 1);
v_options_647_ = lean_ctor_get(v___y_642_, 2);
v_currRecDepth_648_ = lean_ctor_get(v___y_642_, 3);
v_maxRecDepth_649_ = lean_ctor_get(v___y_642_, 4);
v_ref_650_ = lean_ctor_get(v___y_642_, 5);
v_currNamespace_651_ = lean_ctor_get(v___y_642_, 6);
v_openDecls_652_ = lean_ctor_get(v___y_642_, 7);
v_initHeartbeats_653_ = lean_ctor_get(v___y_642_, 8);
v_maxHeartbeats_654_ = lean_ctor_get(v___y_642_, 9);
v_quotContext_655_ = lean_ctor_get(v___y_642_, 10);
v_currMacroScope_656_ = lean_ctor_get(v___y_642_, 11);
v_diag_657_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*14);
v_cancelTk_x3f_658_ = lean_ctor_get(v___y_642_, 12);
v_suppressElabErrors_659_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_660_ = lean_ctor_get(v___y_642_, 13);
v_ref_661_ = l_Lean_replaceRef(v_ref_636_, v_ref_650_);
lean_inc_ref(v_inheritedTraceOptions_660_);
lean_inc(v_cancelTk_x3f_658_);
lean_inc(v_currMacroScope_656_);
lean_inc(v_quotContext_655_);
lean_inc(v_maxHeartbeats_654_);
lean_inc(v_initHeartbeats_653_);
lean_inc(v_openDecls_652_);
lean_inc(v_currNamespace_651_);
lean_inc(v_maxRecDepth_649_);
lean_inc(v_currRecDepth_648_);
lean_inc_ref(v_options_647_);
lean_inc_ref(v_fileMap_646_);
lean_inc_ref(v_fileName_645_);
v___x_662_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_662_, 0, v_fileName_645_);
lean_ctor_set(v___x_662_, 1, v_fileMap_646_);
lean_ctor_set(v___x_662_, 2, v_options_647_);
lean_ctor_set(v___x_662_, 3, v_currRecDepth_648_);
lean_ctor_set(v___x_662_, 4, v_maxRecDepth_649_);
lean_ctor_set(v___x_662_, 5, v_ref_661_);
lean_ctor_set(v___x_662_, 6, v_currNamespace_651_);
lean_ctor_set(v___x_662_, 7, v_openDecls_652_);
lean_ctor_set(v___x_662_, 8, v_initHeartbeats_653_);
lean_ctor_set(v___x_662_, 9, v_maxHeartbeats_654_);
lean_ctor_set(v___x_662_, 10, v_quotContext_655_);
lean_ctor_set(v___x_662_, 11, v_currMacroScope_656_);
lean_ctor_set(v___x_662_, 12, v_cancelTk_x3f_658_);
lean_ctor_set(v___x_662_, 13, v_inheritedTraceOptions_660_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*14, v_diag_657_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*14 + 1, v_suppressElabErrors_659_);
v___x_663_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___x_662_, v___y_643_);
lean_dec_ref_known(v___x_662_, 14);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_664_, lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_664_, v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v_ref_664_);
return v_res_673_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_674_; double v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_float_of_nat(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_679_, lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_ref_686_; lean_object* v___x_687_; lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_732_; 
v_ref_686_ = lean_ctor_get(v___y_683_, 5);
v___x_687_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_732_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_732_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_732_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v_traceState_693_; lean_object* v_env_694_; lean_object* v_nextMacroScope_695_; lean_object* v_ngen_696_; lean_object* v_auxDeclNGen_697_; lean_object* v_cache_698_; lean_object* v_messages_699_; lean_object* v_infoState_700_; lean_object* v_snapshotTasks_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_731_; 
v___x_692_ = lean_st_ref_take(v___y_684_);
v_traceState_693_ = lean_ctor_get(v___x_692_, 4);
v_env_694_ = lean_ctor_get(v___x_692_, 0);
v_nextMacroScope_695_ = lean_ctor_get(v___x_692_, 1);
v_ngen_696_ = lean_ctor_get(v___x_692_, 2);
v_auxDeclNGen_697_ = lean_ctor_get(v___x_692_, 3);
v_cache_698_ = lean_ctor_get(v___x_692_, 5);
v_messages_699_ = lean_ctor_get(v___x_692_, 6);
v_infoState_700_ = lean_ctor_get(v___x_692_, 7);
v_snapshotTasks_701_ = lean_ctor_get(v___x_692_, 8);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_731_ == 0)
{
v___x_703_ = v___x_692_;
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snapshotTasks_701_);
lean_inc(v_infoState_700_);
lean_inc(v_messages_699_);
lean_inc(v_cache_698_);
lean_inc(v_traceState_693_);
lean_inc(v_auxDeclNGen_697_);
lean_inc(v_ngen_696_);
lean_inc(v_nextMacroScope_695_);
lean_inc(v_env_694_);
lean_dec(v___x_692_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
uint64_t v_tid_705_; lean_object* v_traces_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_730_; 
v_tid_705_ = lean_ctor_get_uint64(v_traceState_693_, sizeof(void*)*1);
v_traces_706_ = lean_ctor_get(v_traceState_693_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_traceState_693_);
if (v_isSharedCheck_730_ == 0)
{
v___x_708_ = v_traceState_693_;
v_isShared_709_ = v_isSharedCheck_730_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_traces_706_);
lean_dec(v_traceState_693_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_730_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; double v___x_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_710_ = lean_box(0);
v___x_711_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_712_ = 0;
v___x_713_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_714_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_714_, 0, v_cls_679_);
lean_ctor_set(v___x_714_, 1, v___x_710_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
lean_ctor_set_float(v___x_714_, sizeof(void*)*3, v___x_711_);
lean_ctor_set_float(v___x_714_, sizeof(void*)*3 + 8, v___x_711_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*3 + 16, v___x_712_);
v___x_715_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_716_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v_a_688_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
lean_inc(v_ref_686_);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v_ref_686_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_PersistentArray_push___redArg(v_traces_706_, v___x_717_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_718_);
v___x_720_ = v___x_708_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_718_);
lean_ctor_set_uint64(v_reuseFailAlloc_729_, sizeof(void*)*1, v_tid_705_);
v___x_720_ = v_reuseFailAlloc_729_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_720_);
v___x_722_ = v___x_703_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_env_694_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_nextMacroScope_695_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_ngen_696_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_auxDeclNGen_697_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_728_, 5, v_cache_698_);
lean_ctor_set(v_reuseFailAlloc_728_, 6, v_messages_699_);
lean_ctor_set(v_reuseFailAlloc_728_, 7, v_infoState_700_);
lean_ctor_set(v_reuseFailAlloc_728_, 8, v_snapshotTasks_701_);
v___x_722_ = v_reuseFailAlloc_728_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_723_ = lean_st_ref_set(v___y_684_, v___x_722_);
v___x_724_ = lean_box(0);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_724_);
v___x_726_ = v___x_690_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_733_, lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_733_, v_msg_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
if (lean_obj_tag(v_as_744_) == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
else
{
lean_object* v_options_754_; uint8_t v_hasTrace_755_; 
v_options_754_ = lean_ctor_get(v___y_749_, 2);
v_hasTrace_755_ = lean_ctor_get_uint8(v_options_754_, sizeof(void*)*1);
if (v_hasTrace_755_ == 0)
{
lean_object* v_tail_756_; 
v_tail_756_ = lean_ctor_get(v_as_744_, 1);
lean_inc(v_tail_756_);
lean_dec_ref_known(v_as_744_, 2);
v_as_744_ = v_tail_756_;
goto _start;
}
else
{
lean_object* v_head_758_; lean_object* v_tail_759_; lean_object* v_fst_760_; lean_object* v_snd_761_; lean_object* v_inheritedTraceOptions_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_head_758_ = lean_ctor_get(v_as_744_, 0);
lean_inc(v_head_758_);
v_tail_759_ = lean_ctor_get(v_as_744_, 1);
lean_inc(v_tail_759_);
lean_dec_ref_known(v_as_744_, 2);
v_fst_760_ = lean_ctor_get(v_head_758_, 0);
lean_inc_n(v_fst_760_, 2);
v_snd_761_ = lean_ctor_get(v_head_758_, 1);
lean_inc(v_snd_761_);
lean_dec(v_head_758_);
v_inheritedTraceOptions_762_ = lean_ctor_get(v___y_749_, 13);
v___x_763_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_764_ = l_Lean_Name_append(v___x_763_, v_fst_760_);
v___x_765_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_762_, v_options_754_, v___x_764_);
lean_dec(v___x_764_);
if (v___x_765_ == 0)
{
lean_dec(v_snd_761_);
lean_dec(v_fst_760_);
v_as_744_ = v_tail_759_;
goto _start;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_767_, 0, v_snd_761_);
v___x_768_ = l_Lean_MessageData_ofFormat(v___x_767_);
v___x_769_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_760_, v___x_768_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_dec_ref_known(v___x_769_, 1);
v_as_744_ = v_tail_759_;
goto _start;
}
else
{
lean_dec(v_tail_759_);
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v___x_782_; 
v___x_782_ = lean_box(0);
return v___x_782_;
}
else
{
lean_object* v_key_783_; lean_object* v_value_784_; lean_object* v_tail_785_; uint8_t v___x_786_; 
v_key_783_ = lean_ctor_get(v_x_781_, 0);
v_value_784_ = lean_ctor_get(v_x_781_, 1);
v_tail_785_ = lean_ctor_get(v_x_781_, 2);
v___x_786_ = lean_name_eq(v_key_783_, v_a_780_);
if (v___x_786_ == 0)
{
v_x_781_ = v_tail_785_;
goto _start;
}
else
{
lean_object* v___x_788_; 
lean_inc(v_value_784_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_value_784_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_789_, lean_object* v_x_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_789_, v_x_790_);
lean_dec(v_x_790_);
lean_dec(v_a_789_);
return v_res_791_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_792_; uint64_t v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(1723u);
v___x_793_ = lean_uint64_of_nat(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_buckets_796_; lean_object* v___x_797_; uint64_t v___y_799_; 
v_buckets_796_ = lean_ctor_get(v_m_794_, 1);
v___x_797_ = lean_array_get_size(v_buckets_796_);
if (lean_obj_tag(v_a_795_) == 0)
{
uint64_t v___x_813_; 
v___x_813_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0);
v___y_799_ = v___x_813_;
goto v___jp_798_;
}
else
{
uint64_t v_hash_814_; 
v_hash_814_ = lean_ctor_get_uint64(v_a_795_, sizeof(void*)*2);
v___y_799_ = v_hash_814_;
goto v___jp_798_;
}
v___jp_798_:
{
uint64_t v___x_800_; uint64_t v___x_801_; uint64_t v_fold_802_; uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; size_t v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_800_ = 32ULL;
v___x_801_ = lean_uint64_shift_right(v___y_799_, v___x_800_);
v_fold_802_ = lean_uint64_xor(v___y_799_, v___x_801_);
v___x_803_ = 16ULL;
v___x_804_ = lean_uint64_shift_right(v_fold_802_, v___x_803_);
v___x_805_ = lean_uint64_xor(v_fold_802_, v___x_804_);
v___x_806_ = lean_uint64_to_usize(v___x_805_);
v___x_807_ = lean_usize_of_nat(v___x_797_);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_sub(v___x_807_, v___x_808_);
v___x_810_ = lean_usize_land(v___x_806_, v___x_809_);
v___x_811_ = lean_array_uget_borrowed(v_buckets_796_, v___x_810_);
v___x_812_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_795_, v___x_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_m_815_);
return v_res_817_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_818_, lean_object* v_i_819_, lean_object* v_k_820_){
_start:
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_array_get_size(v_keys_818_);
v___x_822_ = lean_nat_dec_lt(v_i_819_, v___x_821_);
if (v___x_822_ == 0)
{
lean_dec(v_i_819_);
return v___x_822_;
}
else
{
lean_object* v_k_x27_823_; uint8_t v___x_824_; 
v_k_x27_823_ = lean_array_fget_borrowed(v_keys_818_, v_i_819_);
v___x_824_ = l_Lean_instBEqExtraModUse_beq(v_k_820_, v_k_x27_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_nat_add(v_i_819_, v___x_825_);
lean_dec(v_i_819_);
v_i_819_ = v___x_826_;
goto _start;
}
else
{
lean_dec(v_i_819_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_828_, lean_object* v_i_829_, lean_object* v_k_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_828_, v_i_829_, v_k_830_);
lean_dec_ref(v_k_830_);
lean_dec_ref(v_keys_828_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_833_, size_t v_x_834_, lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_833_) == 0)
{
lean_object* v_es_836_; lean_object* v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v_j_840_; lean_object* v___x_841_; 
v_es_836_ = lean_ctor_get(v_x_833_, 0);
v___x_837_ = lean_box(2);
v___x_838_ = ((size_t)31ULL);
v___x_839_ = lean_usize_land(v_x_834_, v___x_838_);
v_j_840_ = lean_usize_to_nat(v___x_839_);
v___x_841_ = lean_array_get_borrowed(v___x_837_, v_es_836_, v_j_840_);
lean_dec(v_j_840_);
switch(lean_obj_tag(v___x_841_))
{
case 0:
{
lean_object* v_key_842_; uint8_t v___x_843_; 
v_key_842_ = lean_ctor_get(v___x_841_, 0);
v___x_843_ = l_Lean_instBEqExtraModUse_beq(v_x_835_, v_key_842_);
return v___x_843_;
}
case 1:
{
lean_object* v_node_844_; size_t v___x_845_; size_t v___x_846_; 
v_node_844_ = lean_ctor_get(v___x_841_, 0);
v___x_845_ = ((size_t)5ULL);
v___x_846_ = lean_usize_shift_right(v_x_834_, v___x_845_);
v_x_833_ = v_node_844_;
v_x_834_ = v___x_846_;
goto _start;
}
default: 
{
uint8_t v___x_848_; 
v___x_848_ = 0;
return v___x_848_;
}
}
}
else
{
lean_object* v_ks_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_ks_849_ = lean_ctor_get(v_x_833_, 0);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_849_, v___x_850_, v_x_835_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
size_t v_x_298702__boxed_855_; uint8_t v_res_856_; lean_object* v_r_857_; 
v_x_298702__boxed_855_ = lean_unbox_usize(v_x_853_);
lean_dec(v_x_853_);
v_res_856_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_852_, v_x_298702__boxed_855_, v_x_854_);
lean_dec_ref(v_x_854_);
lean_dec_ref(v_x_852_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
uint64_t v___x_860_; size_t v___x_861_; uint8_t v___x_862_; 
v___x_860_ = l_Lean_instHashableExtraModUse_hash(v_x_859_);
v___x_861_ = lean_uint64_to_usize(v___x_860_);
v___x_862_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_858_, v___x_861_, v_x_859_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_863_, v_x_864_);
lean_dec_ref(v_x_864_);
lean_dec_ref(v_x_863_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1));
v___x_870_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0));
v___x_871_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_870_, v___x_869_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_872_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_878_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
lean_ctor_set(v___x_878_, 2, v___x_877_);
lean_ctor_set(v___x_878_, 3, v___x_877_);
lean_ctor_set(v___x_878_, 4, v___x_877_);
lean_ctor_set(v___x_878_, 5, v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v_cls_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_cls_890_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_891_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_892_ = l_Lean_Name_append(v___x_891_, v_cls_890_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_903_, uint8_t v_isMeta_904_, lean_object* v_hint_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; lean_object* v_env_914_; uint8_t v_isExporting_915_; lean_object* v___x_916_; lean_object* v_env_917_; lean_object* v___x_918_; lean_object* v_entry_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_913_ = lean_st_ref_get(v___y_911_);
v_env_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_env_914_);
lean_dec(v___x_913_);
v_isExporting_915_ = lean_ctor_get_uint8(v_env_914_, sizeof(void*)*8);
lean_dec_ref(v_env_914_);
v___x_916_ = lean_st_ref_get(v___y_911_);
v_env_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc_ref(v_env_917_);
lean_dec(v___x_916_);
v___x_918_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
lean_inc(v_mod_903_);
v_entry_919_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_919_, 0, v_mod_903_);
lean_ctor_set_uint8(v_entry_919_, sizeof(void*)*1, v_isExporting_915_);
lean_ctor_set_uint8(v_entry_919_, sizeof(void*)*1 + 1, v_isMeta_904_);
v___x_920_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_921_ = lean_box(1);
v___x_922_ = lean_box(0);
v___x_965_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_918_, v___x_920_, v_env_917_, v___x_921_, v___x_922_);
v___x_966_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_965_, v_entry_919_);
lean_dec(v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v_options_967_; uint8_t v_hasTrace_968_; 
v_options_967_ = lean_ctor_get(v___y_910_, 2);
v_hasTrace_968_ = lean_ctor_get_uint8(v_options_967_, sizeof(void*)*1);
if (v_hasTrace_968_ == 0)
{
lean_dec(v_hint_905_);
lean_dec(v_mod_903_);
v___y_924_ = v___y_909_;
v___y_925_ = v___y_911_;
goto v___jp_923_;
}
else
{
lean_object* v_inheritedTraceOptions_969_; lean_object* v_cls_970_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_inheritedTraceOptions_969_ = lean_ctor_get(v___y_910_, 13);
v_cls_970_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_990_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
v___x_991_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_969_, v_options_967_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec(v_hint_905_);
lean_dec(v_mod_903_);
v___y_924_ = v___y_909_;
v___y_925_ = v___y_911_;
goto v___jp_923_;
}
else
{
lean_object* v___x_992_; lean_object* v___y_994_; 
v___x_992_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
if (v_isExporting_915_ == 0)
{
lean_object* v___x_1001_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21));
v___y_994_ = v___x_1001_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1002_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22));
v___y_994_ = v___x_1002_;
goto v___jp_993_;
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_inc_ref(v___y_994_);
v___x_995_ = l_Lean_stringToMessageData(v___y_994_);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_992_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
if (v_isMeta_904_ == 0)
{
lean_object* v___x_999_; 
v___x_999_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_977_ = v___x_998_;
v___y_978_ = v___x_999_;
goto v___jp_976_;
}
else
{
lean_object* v___x_1000_; 
v___x_1000_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_977_ = v___x_998_;
v___y_978_ = v___x_1000_;
goto v___jp_976_;
}
}
}
v___jp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___y_972_);
lean_ctor_set(v___x_974_, 1, v___y_973_);
v___x_975_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_970_, v___x_974_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_dec_ref_known(v___x_975_, 1);
v___y_924_ = v___y_909_;
v___y_925_ = v___y_911_;
goto v___jp_923_;
}
else
{
lean_dec_ref_known(v_entry_919_, 1);
return v___x_975_;
}
}
v___jp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
lean_inc_ref(v___y_978_);
v___x_979_ = l_Lean_stringToMessageData(v___y_978_);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_977_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_MessageData_ofName(v_mod_903_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = l_Lean_Name_isAnonymous(v_hint_905_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_987_ = l_Lean_MessageData_ofName(v_hint_905_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___y_972_ = v___x_984_;
v___y_973_ = v___x_988_;
goto v___jp_971_;
}
else
{
lean_object* v___x_989_; 
lean_dec(v_hint_905_);
v___x_989_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13);
v___y_972_ = v___x_984_;
v___y_973_ = v___x_989_;
goto v___jp_971_;
}
}
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec_ref_known(v_entry_919_, 1);
lean_dec(v_hint_905_);
lean_dec(v_mod_903_);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
v___jp_923_:
{
lean_object* v___x_926_; lean_object* v_toEnvExtension_927_; lean_object* v_env_928_; lean_object* v_nextMacroScope_929_; lean_object* v_ngen_930_; lean_object* v_auxDeclNGen_931_; lean_object* v_traceState_932_; lean_object* v_messages_933_; lean_object* v_infoState_934_; lean_object* v_snapshotTasks_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_963_; 
v___x_926_ = lean_st_ref_take(v___y_925_);
v_toEnvExtension_927_ = lean_ctor_get(v___x_920_, 0);
v_env_928_ = lean_ctor_get(v___x_926_, 0);
v_nextMacroScope_929_ = lean_ctor_get(v___x_926_, 1);
v_ngen_930_ = lean_ctor_get(v___x_926_, 2);
v_auxDeclNGen_931_ = lean_ctor_get(v___x_926_, 3);
v_traceState_932_ = lean_ctor_get(v___x_926_, 4);
v_messages_933_ = lean_ctor_get(v___x_926_, 6);
v_infoState_934_ = lean_ctor_get(v___x_926_, 7);
v_snapshotTasks_935_ = lean_ctor_get(v___x_926_, 8);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v___x_926_, 5);
lean_dec(v_unused_964_);
v___x_937_ = v___x_926_;
v_isShared_938_ = v_isSharedCheck_963_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_snapshotTasks_935_);
lean_inc(v_infoState_934_);
lean_inc(v_messages_933_);
lean_inc(v_traceState_932_);
lean_inc(v_auxDeclNGen_931_);
lean_inc(v_ngen_930_);
lean_inc(v_nextMacroScope_929_);
lean_inc(v_env_928_);
lean_dec(v___x_926_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_963_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_asyncMode_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v_asyncMode_939_ = lean_ctor_get(v_toEnvExtension_927_, 2);
v___x_940_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_920_, v_env_928_, v_entry_919_, v_asyncMode_939_, v___x_922_);
v___x_941_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 5, v___x_941_);
lean_ctor_set(v___x_937_, 0, v___x_940_);
v___x_943_ = v___x_937_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_nextMacroScope_929_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_ngen_930_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_auxDeclNGen_931_);
lean_ctor_set(v_reuseFailAlloc_962_, 4, v_traceState_932_);
lean_ctor_set(v_reuseFailAlloc_962_, 5, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_962_, 6, v_messages_933_);
lean_ctor_set(v_reuseFailAlloc_962_, 7, v_infoState_934_);
lean_ctor_set(v_reuseFailAlloc_962_, 8, v_snapshotTasks_935_);
v___x_943_ = v_reuseFailAlloc_962_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_mctx_946_; lean_object* v_zetaDeltaFVarIds_947_; lean_object* v_postponed_948_; lean_object* v_diag_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_960_; 
v___x_944_ = lean_st_ref_set(v___y_925_, v___x_943_);
v___x_945_ = lean_st_ref_take(v___y_924_);
v_mctx_946_ = lean_ctor_get(v___x_945_, 0);
v_zetaDeltaFVarIds_947_ = lean_ctor_get(v___x_945_, 2);
v_postponed_948_ = lean_ctor_get(v___x_945_, 3);
v_diag_949_ = lean_ctor_get(v___x_945_, 4);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v___x_945_, 1);
lean_dec(v_unused_961_);
v___x_951_ = v___x_945_;
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_diag_949_);
lean_inc(v_postponed_948_);
lean_inc(v_zetaDeltaFVarIds_947_);
lean_inc(v_mctx_946_);
lean_dec(v___x_945_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v___x_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_mctx_946_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_zetaDeltaFVarIds_947_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_postponed_948_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_diag_949_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = lean_st_ref_set(v___y_924_, v___x_955_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_1005_, lean_object* v_isMeta_1006_, lean_object* v_hint_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
uint8_t v_isMeta_boxed_1015_; lean_object* v_res_1016_; 
v_isMeta_boxed_1015_ = lean_unbox(v_isMeta_1006_);
v_res_1016_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_1005_, v_isMeta_boxed_1015_, v_hint_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1017_, lean_object* v_declName_1018_, lean_object* v_as_1019_, size_t v_sz_1020_, size_t v_i_1021_, lean_object* v_b_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = lean_usize_dec_lt(v_i_1021_, v_sz_1020_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_dec(v_declName_1018_);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_b_1022_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; lean_object* v_modules_1033_; lean_object* v___x_1034_; lean_object* v_a_1035_; lean_object* v___x_1036_; lean_object* v_toImport_1037_; lean_object* v_module_1038_; uint8_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1032_ = l_Lean_Environment_header(v___x_1017_);
v_modules_1033_ = lean_ctor_get(v___x_1032_, 3);
lean_inc_ref(v_modules_1033_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1035_ = lean_array_uget_borrowed(v_as_1019_, v_i_1021_);
v___x_1036_ = lean_array_get(v___x_1034_, v_modules_1033_, v_a_1035_);
lean_dec_ref(v_modules_1033_);
v_toImport_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_ref(v_toImport_1037_);
lean_dec(v___x_1036_);
v_module_1038_ = lean_ctor_get(v_toImport_1037_, 0);
lean_inc(v_module_1038_);
lean_dec_ref(v_toImport_1037_);
v___x_1039_ = 0;
lean_inc(v_declName_1018_);
v___x_1040_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1038_, v___x_1039_, v_declName_1018_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1041_ = lean_box(0);
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_add(v_i_1021_, v___x_1042_);
v_i_1021_ = v___x_1043_;
v_b_1022_ = v___x_1041_;
goto _start;
}
else
{
lean_dec(v_declName_1018_);
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1045_, lean_object* v_declName_1046_, lean_object* v_as_1047_, lean_object* v_sz_1048_, lean_object* v_i_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
size_t v_sz_boxed_1058_; size_t v_i_boxed_1059_; lean_object* v_res_1060_; 
v_sz_boxed_1058_ = lean_unbox_usize(v_sz_1048_);
lean_dec(v_sz_1048_);
v_i_boxed_1059_ = lean_unbox_usize(v_i_1049_);
lean_dec(v_i_1049_);
v_res_1060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1045_, v_declName_1046_, v_as_1047_, v_sz_boxed_1058_, v_i_boxed_1059_, v_b_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v_as_1047_);
lean_dec_ref(v___x_1045_);
return v_res_1060_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___x_1064_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0));
v___x_1065_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1064_, v___x_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1068_, uint8_t v_isMeta_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v_env_1081_; lean_object* v___y_1083_; lean_object* v___x_1096_; 
v___x_1077_ = lean_st_ref_get(v___y_1075_);
v_env_1081_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_ref(v_env_1081_);
lean_dec(v___x_1077_);
v___x_1096_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1081_, v_declName_1068_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec_ref(v_env_1081_);
lean_dec(v_declName_1068_);
goto v___jp_1078_;
}
else
{
lean_object* v_val_1097_; lean_object* v___x_1098_; lean_object* v_modules_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_val_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = l_Lean_Environment_header(v_env_1081_);
v_modules_1099_ = lean_ctor_get(v___x_1098_, 3);
lean_inc_ref(v_modules_1099_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = lean_array_get_size(v_modules_1099_);
v___x_1101_ = lean_nat_dec_lt(v_val_1097_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v_modules_1099_);
lean_dec(v_val_1097_);
lean_dec_ref(v_env_1081_);
lean_dec(v_declName_1068_);
goto v___jp_1078_;
}
else
{
lean_object* v___x_1102_; lean_object* v_env_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___y_1107_; 
v___x_1102_ = lean_st_ref_get(v___y_1075_);
v_env_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_env_1103_);
lean_dec(v___x_1102_);
v___x_1104_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2);
v___x_1105_ = lean_array_fget(v_modules_1099_, v_val_1097_);
lean_dec(v_val_1097_);
lean_dec_ref(v_modules_1099_);
if (v_isMeta_1069_ == 0)
{
lean_dec_ref(v_env_1103_);
v___y_1107_ = v_isMeta_1069_;
goto v___jp_1106_;
}
else
{
uint8_t v___x_1118_; 
lean_inc(v_declName_1068_);
v___x_1118_ = l_Lean_isMarkedMeta(v_env_1103_, v_declName_1068_);
if (v___x_1118_ == 0)
{
v___y_1107_ = v_isMeta_1069_;
goto v___jp_1106_;
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = 0;
v___y_1107_ = v___x_1119_;
goto v___jp_1106_;
}
}
v___jp_1106_:
{
lean_object* v_toImport_1108_; lean_object* v_module_1109_; lean_object* v___x_1110_; 
v_toImport_1108_ = lean_ctor_get(v___x_1105_, 0);
lean_inc_ref(v_toImport_1108_);
lean_dec(v___x_1105_);
v_module_1109_ = lean_ctor_get(v_toImport_1108_, 0);
lean_inc(v_module_1109_);
lean_dec_ref(v_toImport_1108_);
lean_inc(v_declName_1068_);
v___x_1110_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1109_, v___y_1107_, v_declName_1068_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref_known(v___x_1110_, 1);
v___x_1111_ = l_Lean_indirectModUseExt;
v___x_1112_ = lean_box(1);
v___x_1113_ = lean_box(0);
lean_inc_ref(v_env_1081_);
v___x_1114_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1104_, v___x_1111_, v_env_1081_, v___x_1112_, v___x_1113_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1114_, v_declName_1068_);
lean_dec(v___x_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3));
v___y_1083_ = v___x_1116_;
goto v___jp_1082_;
}
else
{
lean_object* v_val_1117_; 
v_val_1117_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v___x_1115_, 1);
v___y_1083_ = v_val_1117_;
goto v___jp_1082_;
}
}
else
{
lean_dec_ref(v_env_1081_);
lean_dec(v_declName_1068_);
return v___x_1110_;
}
}
}
}
v___jp_1078_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
v___jp_1082_:
{
lean_object* v___x_1084_; size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1084_ = lean_box(0);
v_sz_1085_ = lean_array_size(v___y_1083_);
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1081_, v_declName_1068_, v___y_1083_, v_sz_1085_, v___x_1086_, v___x_1084_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v_env_1081_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1095_);
v___x_1089_ = v___x_1087_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v___x_1087_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1084_);
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1084_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1120_, lean_object* v_isMeta_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
uint8_t v_isMeta_boxed_1129_; lean_object* v_res_1130_; 
v_isMeta_boxed_1129_ = lean_unbox(v_isMeta_1121_);
v_res_1130_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1120_, v_isMeta_boxed_1129_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1131_, lean_object* v_b_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
if (lean_obj_tag(v_as_x27_1131_) == 0)
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_b_1132_);
return v___x_1140_;
}
else
{
lean_object* v_head_1141_; lean_object* v_tail_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; 
v_head_1141_ = lean_ctor_get(v_as_x27_1131_, 0);
v_tail_1142_ = lean_ctor_get(v_as_x27_1131_, 1);
v___x_1143_ = 1;
lean_inc(v_head_1141_);
v___x_1144_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1141_, v___x_1143_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; 
lean_dec_ref_known(v___x_1144_, 1);
v___x_1145_ = lean_box(0);
v_as_x27_1131_ = v_tail_1142_;
v_b_1132_ = v___x_1145_;
goto _start;
}
else
{
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1147_, v_b_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v_as_x27_1147_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1157_, lean_object* v_currNamespace_1158_, lean_object* v_openDecls_1159_, lean_object* v_n_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = l_Lean_ResolveName_resolveNamespace(v_env_1157_, v_currNamespace_1158_, v_openDecls_1159_, v_n_1160_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v___y_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1165_, lean_object* v_currNamespace_1166_, lean_object* v_openDecls_1167_, lean_object* v_n_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1165_, v_currNamespace_1166_, v_openDecls_1167_, v_n_1168_, v___y_1169_, v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_currNamespace_1172_);
lean_ctor_set(v___x_1175_, 1, v___y_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1176_, v___y_1177_, v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1180_, lean_object* v_options_1181_, lean_object* v_currNamespace_1182_, lean_object* v_openDecls_1183_, lean_object* v_n_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = l_Lean_ResolveName_resolveGlobalName(v_env_1180_, v_options_1181_, v_currNamespace_1182_, v_openDecls_1183_, v_n_1184_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v___y_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1189_, lean_object* v_options_1190_, lean_object* v_currNamespace_1191_, lean_object* v_openDecls_1192_, lean_object* v_n_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1189_, v_options_1190_, v_currNamespace_1191_, v_openDecls_1192_, v_n_1193_, v___y_1194_, v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v_options_1190_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; lean_object* v_env_1207_; lean_object* v_options_1208_; lean_object* v_currRecDepth_1209_; lean_object* v_maxRecDepth_1210_; lean_object* v_ref_1211_; lean_object* v_currNamespace_1212_; lean_object* v_openDecls_1213_; lean_object* v_quotContext_1214_; lean_object* v_currMacroScope_1215_; lean_object* v___x_1216_; lean_object* v_nextMacroScope_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v_methods_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1206_ = lean_st_ref_get(v___y_1204_);
v_env_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_ref_n(v_env_1207_, 4);
lean_dec(v___x_1206_);
v_options_1208_ = lean_ctor_get(v___y_1203_, 2);
v_currRecDepth_1209_ = lean_ctor_get(v___y_1203_, 3);
v_maxRecDepth_1210_ = lean_ctor_get(v___y_1203_, 4);
v_ref_1211_ = lean_ctor_get(v___y_1203_, 5);
v_currNamespace_1212_ = lean_ctor_get(v___y_1203_, 6);
v_openDecls_1213_ = lean_ctor_get(v___y_1203_, 7);
v_quotContext_1214_ = lean_ctor_get(v___y_1203_, 10);
v_currMacroScope_1215_ = lean_ctor_get(v___y_1203_, 11);
v___x_1216_ = lean_st_ref_get(v___y_1204_);
v_nextMacroScope_1217_ = lean_ctor_get(v___x_1216_, 1);
lean_inc(v_nextMacroScope_1217_);
lean_dec(v___x_1216_);
v___f_1218_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1218_, 0, v_env_1207_);
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1219_, 0, v_env_1207_);
lean_inc_n(v_openDecls_1213_, 2);
lean_inc_n(v_currNamespace_1212_, 3);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1220_, 0, v_env_1207_);
lean_closure_set(v___f_1220_, 1, v_currNamespace_1212_);
lean_closure_set(v___f_1220_, 2, v_openDecls_1213_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1221_, 0, v_currNamespace_1212_);
lean_inc_ref(v_options_1208_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1222_, 0, v_env_1207_);
lean_closure_set(v___f_1222_, 1, v_options_1208_);
lean_closure_set(v___f_1222_, 2, v_currNamespace_1212_);
lean_closure_set(v___f_1222_, 3, v_openDecls_1213_);
v_methods_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1223_, 0, v___f_1218_);
lean_ctor_set(v_methods_1223_, 1, v___f_1221_);
lean_ctor_set(v_methods_1223_, 2, v___f_1219_);
lean_ctor_set(v_methods_1223_, 3, v___f_1220_);
lean_ctor_set(v_methods_1223_, 4, v___f_1222_);
lean_inc(v_ref_1211_);
lean_inc(v_maxRecDepth_1210_);
lean_inc(v_currRecDepth_1209_);
lean_inc(v_currMacroScope_1215_);
lean_inc(v_quotContext_1214_);
v___x_1224_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1224_, 0, v_methods_1223_);
lean_ctor_set(v___x_1224_, 1, v_quotContext_1214_);
lean_ctor_set(v___x_1224_, 2, v_currMacroScope_1215_);
lean_ctor_set(v___x_1224_, 3, v_currRecDepth_1209_);
lean_ctor_set(v___x_1224_, 4, v_maxRecDepth_1210_);
lean_ctor_set(v___x_1224_, 5, v_ref_1211_);
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v_nextMacroScope_1217_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
lean_ctor_set(v___x_1226_, 2, v___x_1225_);
v___x_1227_ = lean_apply_2(v_x_1198_, v___x_1224_, v___x_1226_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v_a_1229_; lean_object* v_macroScope_1230_; lean_object* v_traceMsgs_1231_; lean_object* v_expandedMacroDecls_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 1);
lean_inc(v_a_1228_);
v_a_1229_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1227_, 2);
v_macroScope_1230_ = lean_ctor_get(v_a_1228_, 0);
lean_inc(v_macroScope_1230_);
v_traceMsgs_1231_ = lean_ctor_get(v_a_1228_, 1);
lean_inc(v_traceMsgs_1231_);
v_expandedMacroDecls_1232_ = lean_ctor_get(v_a_1228_, 2);
lean_inc(v_expandedMacroDecls_1232_);
lean_dec(v_a_1228_);
v___x_1233_ = lean_box(0);
v___x_1234_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1232_, v___x_1233_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v_expandedMacroDecls_1232_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1235_; lean_object* v_env_1236_; lean_object* v_ngen_1237_; lean_object* v_auxDeclNGen_1238_; lean_object* v_traceState_1239_; lean_object* v_cache_1240_; lean_object* v_messages_1241_; lean_object* v_infoState_1242_; lean_object* v_snapshotTasks_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref_known(v___x_1234_, 1);
v___x_1235_ = lean_st_ref_take(v___y_1204_);
v_env_1236_ = lean_ctor_get(v___x_1235_, 0);
v_ngen_1237_ = lean_ctor_get(v___x_1235_, 2);
v_auxDeclNGen_1238_ = lean_ctor_get(v___x_1235_, 3);
v_traceState_1239_ = lean_ctor_get(v___x_1235_, 4);
v_cache_1240_ = lean_ctor_get(v___x_1235_, 5);
v_messages_1241_ = lean_ctor_get(v___x_1235_, 6);
v_infoState_1242_ = lean_ctor_get(v___x_1235_, 7);
v_snapshotTasks_1243_ = lean_ctor_get(v___x_1235_, 8);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1235_, 1);
lean_dec(v_unused_1270_);
v___x_1245_ = v___x_1235_;
v_isShared_1246_ = v_isSharedCheck_1269_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snapshotTasks_1243_);
lean_inc(v_infoState_1242_);
lean_inc(v_messages_1241_);
lean_inc(v_cache_1240_);
lean_inc(v_traceState_1239_);
lean_inc(v_auxDeclNGen_1238_);
lean_inc(v_ngen_1237_);
lean_inc(v_env_1236_);
lean_dec(v___x_1235_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1269_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v_macroScope_1230_);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_env_1236_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_macroScope_1230_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_ngen_1237_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_auxDeclNGen_1238_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_traceState_1239_);
lean_ctor_set(v_reuseFailAlloc_1268_, 5, v_cache_1240_);
lean_ctor_set(v_reuseFailAlloc_1268_, 6, v_messages_1241_);
lean_ctor_set(v_reuseFailAlloc_1268_, 7, v_infoState_1242_);
lean_ctor_set(v_reuseFailAlloc_1268_, 8, v_snapshotTasks_1243_);
v___x_1248_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_st_ref_set(v___y_1204_, v___x_1248_);
v___x_1250_ = l_List_reverse___redArg(v_traceMsgs_1231_);
v___x_1251_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1250_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1251_, 0);
lean_dec(v_unused_1259_);
v___x_1253_ = v___x_1251_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_dec(v___x_1251_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v_a_1229_);
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1229_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_a_1229_);
v_a_1260_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1251_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1251_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_traceMsgs_1231_);
lean_dec(v_macroScope_1230_);
lean_dec(v_a_1229_);
v_a_1271_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1234_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1234_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_a_1279_; 
v_a_1279_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1227_, 2);
if (lean_obj_tag(v_a_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v_a_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_a_1280_ = lean_ctor_get(v_a_1279_, 0);
lean_inc(v_a_1280_);
v_a_1281_ = lean_ctor_get(v_a_1279_, 1);
lean_inc_ref(v_a_1281_);
lean_dec_ref_known(v_a_1279_, 2);
v___x_1282_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1283_ = lean_string_dec_eq(v_a_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_a_1281_);
v___x_1285_ = l_Lean_MessageData_ofFormat(v___x_1284_);
v___x_1286_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1280_, v___x_1285_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v_a_1280_);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; 
lean_dec_ref(v_a_1281_);
v___x_1287_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1280_);
return v___x_1287_;
}
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1301_, size_t v_i_1302_, lean_object* v_bs_1303_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_usize_dec_lt(v_i_1302_, v_sz_1301_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_bs_1303_);
return v___x_1305_;
}
else
{
lean_object* v_v_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_v_1306_ = lean_array_uget(v_bs_1303_, v_i_1302_);
v___x_1307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1306_);
v___x_1308_ = l_Lean_Syntax_isOfKind(v_v_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_dec(v_v_1306_);
lean_dec_ref(v_bs_1303_);
v___x_1309_ = lean_box(0);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = l_Lean_Syntax_getArg(v_v_1306_, v___x_1310_);
v___x_1312_ = l_Lean_Syntax_isOfKind(v___x_1311_, v___x_1307_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec(v_v_1306_);
lean_dec_ref(v_bs_1303_);
v___x_1313_ = lean_box(0);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; lean_object* v_bs_x27_1315_; lean_object* v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; lean_object* v___x_1319_; 
v___x_1314_ = lean_unsigned_to_nat(3u);
v_bs_x27_1315_ = lean_array_uset(v_bs_1303_, v_i_1302_, v___x_1310_);
v___x_1316_ = l_Lean_Syntax_getArg(v_v_1306_, v___x_1314_);
lean_dec(v_v_1306_);
v___x_1317_ = ((size_t)1ULL);
v___x_1318_ = lean_usize_add(v_i_1302_, v___x_1317_);
v___x_1319_ = lean_array_uset(v_bs_x27_1315_, v_i_1302_, v___x_1316_);
v_i_1302_ = v___x_1318_;
v_bs_1303_ = v___x_1319_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1321_, lean_object* v_i_1322_, lean_object* v_bs_1323_){
_start:
{
size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1321_);
lean_dec(v_sz_1321_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1322_);
lean_dec(v_i_1322_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1324_, v_i_boxed_1325_, v_bs_1323_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1339_, size_t v_i_1340_, lean_object* v_bs_1341_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_lt(v_i_1340_, v_sz_1339_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_bs_1341_);
return v___x_1343_;
}
else
{
lean_object* v_v_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_v_1344_ = lean_array_uget(v_bs_1341_, v_i_1340_);
v___x_1345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1344_);
v___x_1346_ = l_Lean_Syntax_isOfKind(v_v_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec(v_v_1344_);
lean_dec_ref(v_bs_1341_);
v___x_1347_ = lean_box(0);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = l_Lean_Syntax_getArg(v_v_1344_, v___x_1348_);
v___x_1350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1351_ = l_Lean_Syntax_isOfKind(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec(v_v_1344_);
lean_dec_ref(v_bs_1341_);
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_bs_x27_1355_; lean_object* v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1353_ = lean_unsigned_to_nat(3u);
v___x_1354_ = lean_unsigned_to_nat(0u);
v_bs_x27_1355_ = lean_array_uset(v_bs_1341_, v_i_1340_, v___x_1354_);
v___x_1356_ = l_Lean_Syntax_getArg(v_v_1344_, v___x_1353_);
lean_dec(v_v_1344_);
v___x_1357_ = ((size_t)1ULL);
v___x_1358_ = lean_usize_add(v_i_1340_, v___x_1357_);
v___x_1359_ = lean_array_uset(v_bs_x27_1355_, v_i_1340_, v___x_1356_);
v_i_1340_ = v___x_1358_;
v_bs_1341_ = v___x_1359_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_bs_1363_){
_start:
{
size_t v_sz_boxed_1364_; size_t v_i_boxed_1365_; lean_object* v_res_1366_; 
v_sz_boxed_1364_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1365_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1364_, v_i_boxed_1365_, v_bs_1363_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1373_, size_t v_i_1374_, lean_object* v_bs_1375_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_lt(v_i_1374_, v_sz_1373_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1377_, 0, v_bs_1375_);
return v___x_1377_;
}
else
{
lean_object* v_v_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_v_1378_ = lean_array_uget(v_bs_1375_, v_i_1374_);
v___x_1379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1378_);
v___x_1380_ = l_Lean_Syntax_isOfKind(v_v_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_dec(v_v_1378_);
lean_dec_ref(v_bs_1375_);
v___x_1381_ = lean_box(0);
return v___x_1381_;
}
else
{
lean_object* v___x_1382_; lean_object* v_bs_x27_1383_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1382_ = lean_unsigned_to_nat(0u);
v_bs_x27_1383_ = lean_array_uset(v_bs_1375_, v_i_1374_, v___x_1382_);
v___x_1390_ = l_Lean_Syntax_getArg(v_v_1378_, v___x_1382_);
lean_dec(v_v_1378_);
v___x_1391_ = l_Lean_Syntax_isNone(v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = lean_unsigned_to_nat(2u);
v___x_1393_ = l_Lean_Syntax_matchesNull(v___x_1390_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_dec_ref(v_bs_x27_1383_);
v___x_1394_ = lean_box(0);
return v___x_1394_;
}
else
{
goto v___jp_1384_;
}
}
else
{
lean_dec(v___x_1390_);
goto v___jp_1384_;
}
v___jp_1384_:
{
lean_object* v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_add(v_i_1374_, v___x_1386_);
v___x_1388_ = lean_array_uset(v_bs_x27_1383_, v_i_1374_, v___x_1385_);
v_i_1374_ = v___x_1387_;
v_bs_1375_ = v___x_1388_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1395_, lean_object* v_i_1396_, lean_object* v_bs_1397_){
_start:
{
size_t v_sz_boxed_1398_; size_t v_i_boxed_1399_; lean_object* v_res_1400_; 
v_sz_boxed_1398_ = lean_unbox_usize(v_sz_1395_);
lean_dec(v_sz_1395_);
v_i_boxed_1399_ = lean_unbox_usize(v_i_1396_);
lean_dec(v_i_1396_);
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1398_, v_i_boxed_1399_, v_bs_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1401_, size_t v_i_1402_, lean_object* v_bs_1403_){
_start:
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_usize_dec_lt(v_i_1402_, v_sz_1401_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v_bs_1403_);
return v___x_1405_;
}
else
{
lean_object* v_v_1406_; lean_object* v___x_1407_; lean_object* v_bs_x27_1408_; size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v_v_1406_ = lean_array_uget(v_bs_1403_, v_i_1402_);
v___x_1407_ = lean_unsigned_to_nat(0u);
v_bs_x27_1408_ = lean_array_uset(v_bs_1403_, v_i_1402_, v___x_1407_);
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_add(v_i_1402_, v___x_1409_);
v___x_1411_ = lean_array_uset(v_bs_x27_1408_, v_i_1402_, v_v_1406_);
v_i_1402_ = v___x_1410_;
v_bs_1403_ = v___x_1411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1413_, lean_object* v_i_1414_, lean_object* v_bs_1415_){
_start:
{
size_t v_sz_boxed_1416_; size_t v_i_boxed_1417_; lean_object* v_res_1418_; 
v_sz_boxed_1416_ = lean_unbox_usize(v_sz_1413_);
lean_dec(v_sz_1413_);
v_i_boxed_1417_ = lean_unbox_usize(v_i_1414_);
lean_dec(v_i_1414_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1416_, v_i_boxed_1417_, v_bs_1415_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1420_, v___y_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1424_, v_x_1425_, v___y_1426_, v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec_ref(v_x_1425_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1432_, lean_object* v_as_x27_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
if (lean_obj_tag(v_as_x27_1433_) == 0)
{
lean_object* v___x_1442_; 
lean_dec(v_stx_1432_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_b_1434_);
return v___x_1442_;
}
else
{
lean_object* v_head_1443_; lean_object* v_tail_1444_; lean_object* v_value_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec_ref(v_b_1434_);
v_head_1443_ = lean_ctor_get(v_as_x27_1433_, 0);
v_tail_1444_ = lean_ctor_get(v_as_x27_1433_, 1);
v_value_1445_ = lean_ctor_get(v_head_1443_, 1);
v___x_1446_ = lean_box(0);
lean_inc(v_value_1445_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v_stx_1432_);
v___x_1447_ = lean_apply_8(v_value_1445_, v_stx_1432_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, lean_box(0));
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_stx_1432_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1457_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1457_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1452_, 0, v_a_1448_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v___x_1446_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1453_);
v___x_1455_ = v___x_1450_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1480_; 
v_a_1458_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1460_ = v___x_1447_;
v_isShared_1461_ = v_isSharedCheck_1480_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1447_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1480_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___y_1465_; uint8_t v___x_1478_; 
v___x_1462_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1463_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1478_ = l_Lean_Exception_isInterrupt(v_a_1458_);
if (v___x_1478_ == 0)
{
uint8_t v___x_1479_; 
lean_inc(v_a_1458_);
v___x_1479_ = l_Lean_Exception_isRuntime(v_a_1458_);
v___y_1465_ = v___x_1479_;
goto v___jp_1464_;
}
else
{
v___y_1465_ = v___x_1478_;
goto v___jp_1464_;
}
v___jp_1464_:
{
if (v___y_1465_ == 0)
{
if (lean_obj_tag(v_a_1458_) == 0)
{
lean_object* v___x_1467_; 
lean_dec(v_stx_1432_);
if (v_isShared_1461_ == 0)
{
v___x_1467_ = v___x_1460_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1458_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
else
{
lean_object* v_id_1469_; uint8_t v___x_1470_; 
v_id_1469_ = lean_ctor_get(v_a_1458_, 0);
v___x_1470_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1463_, v_id_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1472_; 
lean_dec(v_stx_1432_);
if (v_isShared_1461_ == 0)
{
v___x_1472_ = v___x_1460_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1458_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
else
{
lean_dec_ref_known(v_a_1458_, 2);
lean_del_object(v___x_1460_);
v_as_x27_1433_ = v_tail_1444_;
v_b_1434_ = v___x_1462_;
goto _start;
}
}
}
else
{
lean_object* v___x_1476_; 
lean_dec(v_stx_1432_);
if (v_isShared_1461_ == 0)
{
v___x_1476_ = v___x_1460_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1458_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1481_, lean_object* v_as_x27_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1481_, v_as_x27_1482_, v_b_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v_as_x27_1482_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1494_, lean_object* v_rhs_x3f_1495_, lean_object* v_otherwise_x3f_1496_, lean_object* v_body_x3f_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
uint8_t v___y_1506_; uint8_t v___y_1507_; lean_object* v___y_1508_; uint8_t v___y_1509_; uint8_t v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v_body_1517_; lean_object* v___y_1538_; lean_object* v_otherwise_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v_rhs_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; 
if (lean_obj_tag(v_rhs_x3f_1495_) == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1551_ = v___x_1562_;
v___y_1552_ = v_a_1498_;
v___y_1553_ = v_a_1499_;
v___y_1554_ = v_a_1500_;
v___y_1555_ = v_a_1501_;
v___y_1556_ = v_a_1502_;
v___y_1557_ = v_a_1503_;
goto v___jp_1550_;
}
else
{
lean_object* v_val_1563_; lean_object* v___x_1564_; 
v_val_1563_ = lean_ctor_get(v_rhs_x3f_1495_, 0);
lean_inc(v_val_1563_);
lean_dec_ref_known(v_rhs_x3f_1495_, 1);
v___x_1564_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1563_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v_rhs_1551_ = v_a_1565_;
v___y_1552_ = v_a_1498_;
v___y_1553_ = v_a_1499_;
v___y_1554_ = v_a_1500_;
v___y_1555_ = v_a_1501_;
v___y_1556_ = v_a_1502_;
v___y_1557_ = v_a_1503_;
goto v___jp_1550_;
}
else
{
lean_dec(v_body_x3f_1497_);
lean_dec(v_otherwise_x3f_1496_);
lean_dec_ref(v_reassigned_1494_);
return v___x_1564_;
}
}
v___jp_1505_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1512_, 0, v___y_1508_);
lean_ctor_set(v___x_1512_, 1, v___y_1511_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*2, v___y_1509_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*2 + 1, v___y_1506_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*2 + 2, v___y_1510_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*2 + 3, v___y_1507_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
v___jp_1514_:
{
lean_object* v___x_1518_; lean_object* v_info_1519_; uint8_t v_breaks_1520_; uint8_t v_continues_1521_; uint8_t v_returnsEarly_1522_; lean_object* v_numRegularExits_1523_; uint8_t v_noFallthrough_1524_; lean_object* v_reassigns_1525_; size_t v_sz_1526_; size_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1518_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1517_, v___y_1516_);
v_info_1519_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1515_, v___x_1518_);
v_breaks_1520_ = lean_ctor_get_uint8(v_info_1519_, sizeof(void*)*2);
v_continues_1521_ = lean_ctor_get_uint8(v_info_1519_, sizeof(void*)*2 + 1);
v_returnsEarly_1522_ = lean_ctor_get_uint8(v_info_1519_, sizeof(void*)*2 + 2);
v_numRegularExits_1523_ = lean_ctor_get(v_info_1519_, 0);
lean_inc(v_numRegularExits_1523_);
v_noFallthrough_1524_ = lean_ctor_get_uint8(v_info_1519_, sizeof(void*)*2 + 3);
v_reassigns_1525_ = lean_ctor_get(v_info_1519_, 1);
lean_inc(v_reassigns_1525_);
lean_dec_ref(v_info_1519_);
v_sz_1526_ = lean_array_size(v_reassigned_1494_);
v___x_1527_ = ((size_t)0ULL);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1526_, v___x_1527_, v_reassigned_1494_);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = lean_array_get_size(v___x_1528_);
v___x_1531_ = lean_nat_dec_lt(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_dec_ref(v___x_1528_);
v___y_1506_ = v_continues_1521_;
v___y_1507_ = v_noFallthrough_1524_;
v___y_1508_ = v_numRegularExits_1523_;
v___y_1509_ = v_breaks_1520_;
v___y_1510_ = v_returnsEarly_1522_;
v___y_1511_ = v_reassigns_1525_;
goto v___jp_1505_;
}
else
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_nat_dec_le(v___x_1530_, v___x_1530_);
if (v___x_1532_ == 0)
{
if (v___x_1531_ == 0)
{
lean_dec_ref(v___x_1528_);
v___y_1506_ = v_continues_1521_;
v___y_1507_ = v_noFallthrough_1524_;
v___y_1508_ = v_numRegularExits_1523_;
v___y_1509_ = v_breaks_1520_;
v___y_1510_ = v_returnsEarly_1522_;
v___y_1511_ = v_reassigns_1525_;
goto v___jp_1505_;
}
else
{
size_t v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_usize_of_nat(v___x_1530_);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1528_, v___x_1527_, v___x_1533_, v_reassigns_1525_);
lean_dec_ref(v___x_1528_);
v___y_1506_ = v_continues_1521_;
v___y_1507_ = v_noFallthrough_1524_;
v___y_1508_ = v_numRegularExits_1523_;
v___y_1509_ = v_breaks_1520_;
v___y_1510_ = v_returnsEarly_1522_;
v___y_1511_ = v___x_1534_;
goto v___jp_1505_;
}
}
else
{
size_t v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_usize_of_nat(v___x_1530_);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1528_, v___x_1527_, v___x_1535_, v_reassigns_1525_);
lean_dec_ref(v___x_1528_);
v___y_1506_ = v_continues_1521_;
v___y_1507_ = v_noFallthrough_1524_;
v___y_1508_ = v_numRegularExits_1523_;
v___y_1509_ = v_breaks_1520_;
v___y_1510_ = v_returnsEarly_1522_;
v___y_1511_ = v___x_1536_;
goto v___jp_1505_;
}
}
}
v___jp_1537_:
{
if (lean_obj_tag(v_body_x3f_1497_) == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1515_ = v___y_1538_;
v___y_1516_ = v_otherwise_1539_;
v_body_1517_ = v___x_1546_;
goto v___jp_1514_;
}
else
{
lean_object* v_val_1547_; lean_object* v___x_1548_; 
v_val_1547_ = lean_ctor_get(v_body_x3f_1497_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v_body_x3f_1497_, 1);
v___x_1548_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1547_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___y_1515_ = v___y_1538_;
v___y_1516_ = v_otherwise_1539_;
v_body_1517_ = v_a_1549_;
goto v___jp_1514_;
}
else
{
lean_dec_ref(v_otherwise_1539_);
lean_dec_ref(v___y_1538_);
lean_dec_ref(v_reassigned_1494_);
return v___x_1548_;
}
}
}
v___jp_1550_:
{
if (lean_obj_tag(v_otherwise_x3f_1496_) == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1538_ = v_rhs_1551_;
v_otherwise_1539_ = v___x_1558_;
v___y_1540_ = v___y_1552_;
v___y_1541_ = v___y_1553_;
v___y_1542_ = v___y_1554_;
v___y_1543_ = v___y_1555_;
v___y_1544_ = v___y_1556_;
v___y_1545_ = v___y_1557_;
goto v___jp_1537_;
}
else
{
lean_object* v_val_1559_; lean_object* v___x_1560_; 
v_val_1559_ = lean_ctor_get(v_otherwise_x3f_1496_, 0);
lean_inc(v_val_1559_);
lean_dec_ref_known(v_otherwise_x3f_1496_, 1);
v___x_1560_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1559_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___y_1538_ = v_rhs_1551_;
v_otherwise_1539_ = v_a_1561_;
v___y_1540_ = v___y_1552_;
v___y_1541_ = v___y_1553_;
v___y_1542_ = v___y_1554_;
v___y_1543_ = v___y_1555_;
v___y_1544_ = v___y_1556_;
v___y_1545_ = v___y_1557_;
goto v___jp_1537_;
}
else
{
lean_dec_ref(v_rhs_1551_);
lean_dec(v_body_x3f_1497_);
lean_dec_ref(v_reassigned_1494_);
return v___x_1560_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1658_ = l_Lean_stringToMessageData(v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1668_, lean_object* v_decl_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v_reassigns_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1669_);
v___x_1706_ = l_Lean_Syntax_isOfKind(v_decl_1669_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1669_);
v___x_1708_ = l_Lean_Syntax_isOfKind(v_decl_1669_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1709_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1710_ = lean_box(0);
v___x_1711_ = l_Lean_Syntax_formatStx(v_decl_1669_, v___x_1710_, v___x_1708_);
v___x_1712_ = l_Std_Format_defWidth;
v___x_1713_ = lean_unsigned_to_nat(0u);
v___x_1714_ = l_Std_Format_pretty(v___x_1711_, v___x_1712_, v___x_1713_, v___x_1713_);
v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
v___x_1716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1709_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1716_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; lean_object* v_pattern_1719_; lean_object* v___y_1721_; lean_object* v_otherwise_x3f_1722_; lean_object* v_body_x3f_x3f_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v_body_x3f_x3f_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___x_1753_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1718_ = lean_unsigned_to_nat(0u);
v_pattern_1719_ = l_Lean_Syntax_getArg(v_decl_1669_, v___x_1718_);
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1792_ = l_Lean_Syntax_getArg(v_decl_1669_, v___x_1753_);
v___x_1793_ = l_Lean_Syntax_isNone(v___x_1792_);
if (v___x_1793_ == 0)
{
uint8_t v___x_1794_; 
lean_inc(v___x_1792_);
v___x_1794_ = l_Lean_Syntax_matchesNull(v___x_1792_, v___x_1753_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v___x_1792_);
lean_dec(v_pattern_1719_);
v___x_1795_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1796_ = lean_box(0);
v___x_1797_ = l_Lean_Syntax_formatStx(v_decl_1669_, v___x_1796_, v___x_1794_);
v___x_1798_ = l_Std_Format_defWidth;
v___x_1799_ = l_Std_Format_pretty(v___x_1797_, v___x_1798_, v___x_1718_, v___x_1718_);
v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1795_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1801_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1803_ = l_Lean_Syntax_getArg(v___x_1792_, v___x_1718_);
lean_dec(v___x_1792_);
v___x_1804_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1805_ = l_Lean_Syntax_isOfKind(v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec(v_pattern_1719_);
v___x_1806_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1807_ = lean_box(0);
v___x_1808_ = l_Lean_Syntax_formatStx(v_decl_1669_, v___x_1807_, v___x_1805_);
v___x_1809_ = l_Std_Format_defWidth;
v___x_1810_ = l_Std_Format_pretty(v___x_1808_, v___x_1809_, v___x_1718_, v___x_1718_);
v___x_1811_ = l_Lean_stringToMessageData(v___x_1810_);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1806_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1812_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1813_;
}
else
{
v___y_1755_ = v_a_1670_;
v___y_1756_ = v_a_1671_;
v___y_1757_ = v_a_1672_;
v___y_1758_ = v_a_1673_;
v___y_1759_ = v_a_1674_;
v___y_1760_ = v_a_1675_;
goto v___jp_1754_;
}
}
}
else
{
lean_dec(v___x_1792_);
v___y_1755_ = v_a_1670_;
v___y_1756_ = v_a_1671_;
v___y_1757_ = v_a_1672_;
v___y_1758_ = v_a_1673_;
v___y_1759_ = v_a_1674_;
v___y_1760_ = v_a_1675_;
goto v___jp_1754_;
}
v___jp_1720_:
{
if (v_reassignment_1668_ == 0)
{
lean_object* v___x_1730_; 
lean_dec(v_pattern_1719_);
v___x_1730_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1690_ = v___y_1721_;
v___y_1691_ = v_body_x3f_x3f_1723_;
v___y_1692_ = v_otherwise_x3f_1722_;
v_reassigns_1693_ = v___x_1730_;
v___y_1694_ = v___y_1724_;
v___y_1695_ = v___y_1725_;
v___y_1696_ = v___y_1726_;
v___y_1697_ = v___y_1727_;
v___y_1698_ = v___y_1728_;
v___y_1699_ = v___y_1729_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1719_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1731_, 1);
v___y_1690_ = v___y_1721_;
v___y_1691_ = v_body_x3f_x3f_1723_;
v___y_1692_ = v_otherwise_x3f_1722_;
v_reassigns_1693_ = v_a_1732_;
v___y_1694_ = v___y_1724_;
v___y_1695_ = v___y_1725_;
v___y_1696_ = v___y_1726_;
v___y_1697_ = v___y_1727_;
v___y_1698_ = v___y_1728_;
v___y_1699_ = v___y_1729_;
goto v___jp_1689_;
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_body_x3f_x3f_1723_);
lean_dec(v_otherwise_x3f_1722_);
lean_dec(v___y_1721_);
v_a_1733_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1731_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1731_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
v___jp_1741_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___y_1743_);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_body_x3f_x3f_1744_);
v___y_1721_ = v___y_1742_;
v_otherwise_x3f_1722_ = v___x_1751_;
v_body_x3f_x3f_1723_ = v___x_1752_;
v___y_1724_ = v___y_1745_;
v___y_1725_ = v___y_1746_;
v___y_1726_ = v___y_1747_;
v___y_1727_ = v___y_1748_;
v___y_1728_ = v___y_1749_;
v___y_1729_ = v___y_1750_;
goto v___jp_1720_;
}
v___jp_1754_:
{
lean_object* v___x_1761_; lean_object* v_rhs_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1761_ = lean_unsigned_to_nat(3u);
v_rhs_1762_ = l_Lean_Syntax_getArg(v_decl_1669_, v___x_1761_);
v___x_1763_ = lean_unsigned_to_nat(4u);
v___x_1764_ = l_Lean_Syntax_getArg(v_decl_1669_, v___x_1763_);
v___x_1765_ = l_Lean_Syntax_isNone(v___x_1764_);
if (v___x_1765_ == 0)
{
uint8_t v___x_1766_; 
lean_inc(v___x_1764_);
v___x_1766_ = l_Lean_Syntax_matchesNull(v___x_1764_, v___x_1761_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec(v___x_1764_);
lean_dec(v_rhs_1762_);
lean_dec(v_pattern_1719_);
v___x_1767_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1768_ = lean_box(0);
v___x_1769_ = l_Lean_Syntax_formatStx(v_decl_1669_, v___x_1768_, v___x_1766_);
v___x_1770_ = l_Std_Format_defWidth;
v___x_1771_ = l_Std_Format_pretty(v___x_1769_, v___x_1770_, v___x_1718_, v___x_1718_);
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1767_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1773_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; lean_object* v_otherwise_x3f_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1775_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1776_ = l_Lean_Syntax_getArg(v___x_1764_, v___x_1753_);
v___x_1777_ = l_Lean_Syntax_getArg(v___x_1764_, v___x_1775_);
lean_dec(v___x_1764_);
v___x_1778_ = l_Lean_Syntax_isNone(v___x_1777_);
if (v___x_1778_ == 0)
{
uint8_t v___x_1779_; 
lean_inc(v___x_1777_);
v___x_1779_ = l_Lean_Syntax_matchesNull(v___x_1777_, v___x_1753_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec(v___x_1777_);
lean_dec(v_otherwise_x3f_1776_);
lean_dec(v_rhs_1762_);
lean_dec(v_pattern_1719_);
v___x_1780_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1781_ = lean_box(0);
v___x_1782_ = l_Lean_Syntax_formatStx(v_decl_1669_, v___x_1781_, v___x_1779_);
v___x_1783_ = l_Std_Format_defWidth;
v___x_1784_ = l_Std_Format_pretty(v___x_1782_, v___x_1783_, v___x_1718_, v___x_1718_);
v___x_1785_ = l_Lean_stringToMessageData(v___x_1784_);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1780_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1786_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
return v___x_1787_;
}
else
{
lean_object* v_body_x3f_x3f_1788_; lean_object* v___x_1789_; 
lean_dec(v_decl_1669_);
v_body_x3f_x3f_1788_ = l_Lean_Syntax_getArg(v___x_1777_, v___x_1718_);
lean_dec(v___x_1777_);
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_body_x3f_x3f_1788_);
v___y_1742_ = v_rhs_1762_;
v___y_1743_ = v_otherwise_x3f_1776_;
v_body_x3f_x3f_1744_ = v___x_1789_;
v___y_1745_ = v___y_1755_;
v___y_1746_ = v___y_1756_;
v___y_1747_ = v___y_1757_;
v___y_1748_ = v___y_1758_;
v___y_1749_ = v___y_1759_;
v___y_1750_ = v___y_1760_;
goto v___jp_1741_;
}
}
else
{
lean_object* v___x_1790_; 
lean_dec(v___x_1777_);
lean_dec(v_decl_1669_);
v___x_1790_ = lean_box(0);
v___y_1742_ = v_rhs_1762_;
v___y_1743_ = v_otherwise_x3f_1776_;
v_body_x3f_x3f_1744_ = v___x_1790_;
v___y_1745_ = v___y_1755_;
v___y_1746_ = v___y_1756_;
v___y_1747_ = v___y_1757_;
v___y_1748_ = v___y_1758_;
v___y_1749_ = v___y_1759_;
v___y_1750_ = v___y_1760_;
goto v___jp_1741_;
}
}
}
else
{
lean_object* v___x_1791_; 
lean_dec(v___x_1764_);
lean_dec(v_decl_1669_);
v___x_1791_ = lean_box(0);
v___y_1721_ = v_rhs_1762_;
v_otherwise_x3f_1722_ = v___x_1791_;
v_body_x3f_x3f_1723_ = v___x_1791_;
v___y_1724_ = v___y_1755_;
v___y_1725_ = v___y_1756_;
v___y_1726_ = v___y_1757_;
v___y_1727_ = v___y_1758_;
v___y_1728_ = v___y_1759_;
v___y_1729_ = v___y_1760_;
goto v___jp_1720_;
}
}
}
}
else
{
lean_object* v___x_1814_; lean_object* v_x_1815_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1814_ = lean_unsigned_to_nat(0u);
v_x_1815_ = l_Lean_Syntax_getArg(v_decl_1669_, v___x_1814_);
v___x_1829_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1815_);
v___x_1830_ = l_Lean_Syntax_isOfKind(v_x_1815_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v_x_1815_);
v___x_1831_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1832_ = lean_box(0);
v___x_1833_ = l_Lean_Syntax_formatStx(v_decl_1669_, v___x_1832_, v___x_1830_);
v___x_1834_ = l_Std_Format_defWidth;
v___x_1835_ = l_Std_Format_pretty(v___x_1833_, v___x_1834_, v___x_1814_, v___x_1814_);
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1831_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1837_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = l_Lean_Syntax_getArg(v_decl_1669_, v___x_1839_);
v___x_1841_ = l_Lean_Syntax_isNone(v___x_1840_);
if (v___x_1841_ == 0)
{
uint8_t v___x_1842_; 
lean_inc(v___x_1840_);
v___x_1842_ = l_Lean_Syntax_matchesNull(v___x_1840_, v___x_1839_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_dec(v___x_1840_);
lean_dec(v_x_1815_);
v___x_1843_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1844_ = lean_box(0);
v___x_1845_ = l_Lean_Syntax_formatStx(v_decl_1669_, v___x_1844_, v___x_1842_);
v___x_1846_ = l_Std_Format_defWidth;
v___x_1847_ = l_Std_Format_pretty(v___x_1845_, v___x_1846_, v___x_1814_, v___x_1814_);
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1843_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1849_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1851_ = l_Lean_Syntax_getArg(v___x_1840_, v___x_1814_);
lean_dec(v___x_1840_);
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1853_ = l_Lean_Syntax_isOfKind(v___x_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec(v_x_1815_);
v___x_1854_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1855_ = lean_box(0);
v___x_1856_ = l_Lean_Syntax_formatStx(v_decl_1669_, v___x_1855_, v___x_1853_);
v___x_1857_ = l_Std_Format_defWidth;
v___x_1858_ = l_Std_Format_pretty(v___x_1856_, v___x_1857_, v___x_1814_, v___x_1814_);
v___x_1859_ = l_Lean_stringToMessageData(v___x_1858_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1854_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1860_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1861_;
}
else
{
v___y_1817_ = v_a_1670_;
v___y_1818_ = v_a_1671_;
v___y_1819_ = v_a_1672_;
v___y_1820_ = v_a_1673_;
v___y_1821_ = v_a_1674_;
v___y_1822_ = v_a_1675_;
goto v___jp_1816_;
}
}
}
else
{
lean_dec(v___x_1840_);
v___y_1817_ = v_a_1670_;
v___y_1818_ = v_a_1671_;
v___y_1819_ = v_a_1672_;
v___y_1820_ = v_a_1673_;
v___y_1821_ = v_a_1674_;
v___y_1822_ = v_a_1675_;
goto v___jp_1816_;
}
}
v___jp_1816_:
{
lean_object* v___x_1823_; lean_object* v_rhs_1824_; 
v___x_1823_ = lean_unsigned_to_nat(3u);
v_rhs_1824_ = l_Lean_Syntax_getArg(v_decl_1669_, v___x_1823_);
lean_dec(v_decl_1669_);
if (v_reassignment_1668_ == 0)
{
lean_object* v___x_1825_; 
lean_dec(v_x_1815_);
v___x_1825_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1678_ = v___y_1818_;
v___y_1679_ = v___y_1819_;
v___y_1680_ = v___y_1820_;
v___y_1681_ = v___y_1817_;
v___y_1682_ = v___y_1821_;
v___y_1683_ = v___y_1822_;
v___y_1684_ = v_rhs_1824_;
v___y_1685_ = v___x_1825_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_unsigned_to_nat(1u);
v___x_1827_ = lean_mk_empty_array_with_capacity(v___x_1826_);
v___x_1828_ = lean_array_push(v___x_1827_, v_x_1815_);
v___y_1678_ = v___y_1818_;
v___y_1679_ = v___y_1819_;
v___y_1680_ = v___y_1820_;
v___y_1681_ = v___y_1817_;
v___y_1682_ = v___y_1821_;
v___y_1683_ = v___y_1822_;
v___y_1684_ = v_rhs_1824_;
v___y_1685_ = v___x_1828_;
goto v___jp_1677_;
}
}
}
v___jp_1677_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___y_1684_);
v___x_1687_ = lean_box(0);
v___x_1688_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1685_, v___x_1686_, v___x_1687_, v___x_1687_, v___y_1681_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1682_, v___y_1683_);
return v___x_1688_;
}
v___jp_1689_:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___y_1690_);
if (lean_obj_tag(v___y_1691_) == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_box(0);
v___x_1702_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1693_, v___x_1700_, v___y_1692_, v___x_1701_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
return v___x_1702_;
}
else
{
lean_object* v_val_1703_; lean_object* v___x_1704_; 
v_val_1703_ = lean_ctor_get(v___y_1691_, 0);
lean_inc(v_val_1703_);
lean_dec_ref_known(v___y_1691_, 1);
v___x_1704_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1693_, v___x_1700_, v___y_1692_, v_val_1703_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1984_, size_t v_sz_1985_, size_t v_i_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_lt(v_i_1986_, v_sz_1985_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v_b_1987_);
return v___x_1996_;
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_array_uget_borrowed(v_as_1984_, v_i_1986_);
lean_inc(v_a_1997_);
v___x_1998_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1997_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; size_t v___x_2001_; size_t v___x_2002_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1999_, v_b_1987_);
v___x_2001_ = ((size_t)1ULL);
v___x_2002_ = lean_usize_add(v_i_1986_, v___x_2001_);
v_i_1986_ = v___x_2002_;
v_b_1987_ = v___x_2000_;
goto _start;
}
else
{
lean_dec_ref(v_b_1987_);
return v___x_1998_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2033_, lean_object* v_as_2034_, size_t v_sz_2035_, size_t v_i_2036_, lean_object* v_b_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_a_2046_; uint8_t v___x_2050_; 
v___x_2050_ = lean_usize_dec_lt(v_i_2036_, v_sz_2035_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_b_2037_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; lean_object* v_a_2053_; uint8_t v___x_2054_; 
v___x_2052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2053_ = lean_array_uget_borrowed(v_as_2034_, v_i_2036_);
lean_inc(v_a_2053_);
v___x_2054_ = l_Lean_Syntax_isOfKind(v_a_2053_, v___x_2052_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref_known(v___x_2055_, 1);
v_a_2046_ = v_b_2037_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v_b_2037_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___y_2067_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = lean_unsigned_to_nat(3u);
v___x_2084_ = l_Lean_Syntax_getArg(v_a_2053_, v___x_2064_);
v___x_2085_ = l_Lean_Syntax_getArgs(v___x_2084_);
lean_dec(v___x_2084_);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2088_ = lean_array_get_size(v___x_2085_);
v___x_2089_ = lean_nat_dec_lt(v___x_2086_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_dec_ref(v___x_2085_);
v___y_2067_ = v___x_2087_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2090_ = lean_box(v___x_2054_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v___x_2087_);
v___x_2092_ = lean_nat_dec_le(v___x_2088_, v___x_2088_);
if (v___x_2092_ == 0)
{
if (v___x_2089_ == 0)
{
lean_dec_ref_known(v___x_2091_, 2);
lean_dec_ref(v___x_2085_);
v___y_2067_ = v___x_2087_;
goto v___jp_2066_;
}
else
{
size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; lean_object* v_snd_2096_; 
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = lean_usize_of_nat(v___x_2088_);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2054_, v___x_2033_, v___x_2085_, v___x_2093_, v___x_2094_, v___x_2091_);
lean_dec_ref(v___x_2085_);
v_snd_2096_ = lean_ctor_get(v___x_2095_, 1);
lean_inc(v_snd_2096_);
lean_dec_ref(v___x_2095_);
v___y_2067_ = v_snd_2096_;
goto v___jp_2066_;
}
}
else
{
size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; lean_object* v_snd_2100_; 
v___x_2097_ = ((size_t)0ULL);
v___x_2098_ = lean_usize_of_nat(v___x_2088_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2054_, v___x_2033_, v___x_2085_, v___x_2097_, v___x_2098_, v___x_2091_);
lean_dec_ref(v___x_2085_);
v_snd_2100_ = lean_ctor_get(v___x_2099_, 1);
lean_inc(v_snd_2100_);
lean_dec_ref(v___x_2099_);
v___y_2067_ = v_snd_2100_;
goto v___jp_2066_;
}
}
v___jp_2066_:
{
size_t v_sz_2068_; size_t v___x_2069_; lean_object* v___x_2070_; 
v_sz_2068_ = lean_array_size(v___y_2067_);
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2068_, v___x_2069_, v___y_2067_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_dec_ref_known(v___x_2071_, 1);
v_a_2046_ = v_b_2037_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_b_2037_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec_ref_known(v___x_2070_, 1);
v___x_2080_ = l_Lean_Syntax_getArg(v_a_2053_, v___x_2065_);
v___x_2081_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2080_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2037_, v_a_2082_);
v_a_2046_ = v___x_2083_;
goto v___jp_2045_;
}
else
{
lean_dec_ref(v_b_2037_);
return v___x_2081_;
}
}
}
}
}
v___jp_2045_:
{
size_t v___x_2047_; size_t v___x_2048_; 
v___x_2047_ = ((size_t)1ULL);
v___x_2048_ = lean_usize_add(v_i_2036_, v___x_2047_);
v_i_2036_ = v___x_2048_;
v_b_2037_ = v_a_2046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2101_, size_t v_sz_2102_, size_t v_i_2103_, lean_object* v_b_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_a_2113_; uint8_t v___x_2117_; 
v___x_2117_ = lean_usize_dec_lt(v_i_2103_, v_sz_2102_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_b_2104_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; lean_object* v_a_2120_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
v_a_2120_ = lean_array_uget_borrowed(v_as_2101_, v_i_2103_);
v___x_2133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2120_);
v___x_2134_ = l_Lean_Syntax_isOfKind(v_a_2120_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2120_);
v___x_2136_ = l_Lean_Syntax_isOfKind(v_a_2120_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2137_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2138_ = lean_box(0);
lean_inc(v_a_2120_);
v___x_2139_ = l_Lean_Syntax_formatStx(v_a_2120_, v___x_2138_, v___x_2136_);
v___x_2140_ = l_Std_Format_defWidth;
v___x_2141_ = l_Std_Format_pretty(v___x_2139_, v___x_2140_, v___x_2119_, v___x_2119_);
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2137_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2143_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_dec_ref_known(v___x_2144_, 1);
v_a_2113_ = v_b_2104_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_b_2104_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = l_Lean_Syntax_getArg(v_a_2120_, v___x_2153_);
v___x_2155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2154_);
v___x_2156_ = l_Lean_Syntax_isOfKind(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec(v___x_2154_);
v___x_2157_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2158_ = lean_box(0);
lean_inc(v_a_2120_);
v___x_2159_ = l_Lean_Syntax_formatStx(v_a_2120_, v___x_2158_, v___x_2156_);
v___x_2160_ = l_Std_Format_defWidth;
v___x_2161_ = l_Std_Format_pretty(v___x_2159_, v___x_2160_, v___x_2119_, v___x_2119_);
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2157_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2163_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_dec_ref_known(v___x_2164_, 1);
v_a_2113_ = v_b_2104_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_b_2104_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; size_t v_sz_2175_; size_t v___x_2176_; lean_object* v___x_2177_; 
v___x_2173_ = l_Lean_Syntax_getArg(v___x_2154_, v___x_2119_);
lean_dec(v___x_2154_);
v___x_2174_ = l_Lean_Syntax_getArgs(v___x_2173_);
lean_dec(v___x_2173_);
v_sz_2175_ = lean_array_size(v___x_2174_);
v___x_2176_ = ((size_t)0ULL);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2134_, v___x_2174_, v_sz_2175_, v___x_2176_, v_b_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec_ref(v___x_2174_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v_a_2113_ = v_a_2178_;
goto v___jp_2112_;
}
else
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2179_ = lean_unsigned_to_nat(2u);
v___x_2180_ = l_Lean_Syntax_getArg(v_a_2120_, v___x_2179_);
v___x_2181_ = l_Lean_Syntax_isNone(v___x_2180_);
if (v___x_2181_ == 0)
{
uint8_t v___x_2182_; 
v___x_2182_ = l_Lean_Syntax_matchesNull(v___x_2180_, v___x_2179_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2183_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2184_ = lean_box(0);
lean_inc(v_a_2120_);
v___x_2185_ = l_Lean_Syntax_formatStx(v_a_2120_, v___x_2184_, v___x_2182_);
v___x_2186_ = l_Std_Format_defWidth;
v___x_2187_ = l_Std_Format_pretty(v___x_2185_, v___x_2186_, v___x_2119_, v___x_2119_);
v___x_2188_ = l_Lean_stringToMessageData(v___x_2187_);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2183_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2189_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_dec_ref_known(v___x_2190_, 1);
v_a_2113_ = v_b_2104_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v_b_2104_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
v___y_2122_ = v___y_2105_;
v___y_2123_ = v___y_2106_;
v___y_2124_ = v___y_2107_;
v___y_2125_ = v___y_2108_;
v___y_2126_ = v___y_2109_;
v___y_2127_ = v___y_2110_;
goto v___jp_2121_;
}
}
else
{
lean_dec(v___x_2180_);
v___y_2122_ = v___y_2105_;
v___y_2123_ = v___y_2106_;
v___y_2124_ = v___y_2107_;
v___y_2125_ = v___y_2108_;
v___y_2126_ = v___y_2109_;
v___y_2127_ = v___y_2110_;
goto v___jp_2121_;
}
}
v___jp_2121_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_unsigned_to_nat(4u);
v___x_2129_ = l_Lean_Syntax_getArg(v_a_2120_, v___x_2128_);
v___x_2130_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2129_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2131_, v_b_2104_);
v_a_2113_ = v___x_2132_;
goto v___jp_2112_;
}
else
{
lean_dec_ref(v_b_2104_);
return v___x_2130_;
}
}
}
v___jp_2112_:
{
size_t v___x_2114_; size_t v___x_2115_; 
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2103_, v___x_2114_);
v_i_2103_ = v___x_2115_;
v_b_2104_ = v_a_2113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2199_) == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2210_; 
v_val_2209_ = lean_ctor_get(v_stx_x3f_2199_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v_stx_x3f_2199_, 1);
v___x_2210_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2209_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
return v___x_2210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2223_, lean_object* v_as_2224_, size_t v_sz_2225_, size_t v_i_2226_, lean_object* v_b_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_a_2236_; uint8_t v___x_2240_; 
v___x_2240_ = lean_usize_dec_lt(v_i_2226_, v_sz_2225_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v_b_2227_);
return v___x_2241_;
}
else
{
lean_object* v___x_2242_; lean_object* v_a_2243_; uint8_t v___x_2244_; 
v___x_2242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2243_ = lean_array_uget_borrowed(v_as_2224_, v_i_2226_);
lean_inc(v_a_2243_);
v___x_2244_ = l_Lean_Syntax_isOfKind(v_a_2243_, v___x_2242_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_dec_ref_known(v___x_2245_, 1);
v_a_2236_ = v_b_2227_;
goto v___jp_2235_;
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref(v_b_2227_);
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___y_2257_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = lean_unsigned_to_nat(3u);
v___x_2274_ = l_Lean_Syntax_getArg(v_a_2243_, v___x_2254_);
v___x_2275_ = l_Lean_Syntax_getArgs(v___x_2274_);
lean_dec(v___x_2274_);
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2278_ = lean_array_get_size(v___x_2275_);
v___x_2279_ = lean_nat_dec_lt(v___x_2276_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_dec_ref(v___x_2275_);
v___y_2257_ = v___x_2277_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2280_ = lean_box(v___x_2244_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v___x_2277_);
v___x_2282_ = lean_nat_dec_le(v___x_2278_, v___x_2278_);
if (v___x_2282_ == 0)
{
if (v___x_2279_ == 0)
{
lean_dec_ref_known(v___x_2281_, 2);
lean_dec_ref(v___x_2275_);
v___y_2257_ = v___x_2277_;
goto v___jp_2256_;
}
else
{
size_t v___x_2283_; size_t v___x_2284_; lean_object* v___x_2285_; lean_object* v_snd_2286_; 
v___x_2283_ = ((size_t)0ULL);
v___x_2284_ = lean_usize_of_nat(v___x_2278_);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2244_, v___x_2223_, v___x_2275_, v___x_2283_, v___x_2284_, v___x_2281_);
lean_dec_ref(v___x_2275_);
v_snd_2286_ = lean_ctor_get(v___x_2285_, 1);
lean_inc(v_snd_2286_);
lean_dec_ref(v___x_2285_);
v___y_2257_ = v_snd_2286_;
goto v___jp_2256_;
}
}
else
{
size_t v___x_2287_; size_t v___x_2288_; lean_object* v___x_2289_; lean_object* v_snd_2290_; 
v___x_2287_ = ((size_t)0ULL);
v___x_2288_ = lean_usize_of_nat(v___x_2278_);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2244_, v___x_2223_, v___x_2275_, v___x_2287_, v___x_2288_, v___x_2281_);
lean_dec_ref(v___x_2275_);
v_snd_2290_ = lean_ctor_get(v___x_2289_, 1);
lean_inc(v_snd_2290_);
lean_dec_ref(v___x_2289_);
v___y_2257_ = v_snd_2290_;
goto v___jp_2256_;
}
}
v___jp_2256_:
{
size_t v_sz_2258_; size_t v___x_2259_; lean_object* v___x_2260_; 
v_sz_2258_ = lean_array_size(v___y_2257_);
v___x_2259_ = ((size_t)0ULL);
v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2258_, v___x_2259_, v___y_2257_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_dec_ref_known(v___x_2261_, 1);
v_a_2236_ = v_b_2227_;
goto v___jp_2235_;
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v_b_2227_);
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec_ref_known(v___x_2260_, 1);
v___x_2270_ = l_Lean_Syntax_getArg(v_a_2243_, v___x_2255_);
v___x_2271_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2270_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2273_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2227_, v_a_2272_);
v_a_2236_ = v___x_2273_;
goto v___jp_2235_;
}
else
{
lean_dec_ref(v_b_2227_);
return v___x_2271_;
}
}
}
}
}
v___jp_2235_:
{
size_t v___x_2237_; size_t v___x_2238_; 
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_add(v_i_2226_, v___x_2237_);
v_i_2226_ = v___x_2238_;
v_b_2227_ = v_a_2236_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; 
v___x_2327_ = l_Lean_NameSet_empty;
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = 0;
v___x_2330_ = 1;
v___x_2331_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2331_, 0, v___x_2328_);
lean_ctor_set(v___x_2331_, 1, v___x_2327_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*2, v___x_2330_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*2 + 1, v___x_2329_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*2 + 2, v___x_2329_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*2 + 3, v___x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2354_; lean_object* v_bodyInfo_2355_; lean_object* v___y_2359_; lean_object* v_bodyInfo_2360_; lean_object* v___x_2363_; lean_object* v_env_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2363_ = lean_st_ref_get(v_a_2338_);
v_env_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc_ref(v_env_2364_);
lean_dec(v___x_2363_);
lean_inc(v_stx_2332_);
v___x_2365_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2365_, 0, v_env_2364_);
lean_closure_set(v___x_2365_, 1, v_stx_2332_);
v___x_2366_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2365_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_4563_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_4563_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_4563_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
if (lean_obj_tag(v_a_2367_) == 1)
{
lean_object* v_val_2371_; lean_object* v_snd_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_del_object(v___x_2369_);
lean_dec(v_stx_2332_);
v_val_2371_ = lean_ctor_get(v_a_2367_, 0);
lean_inc(v_val_2371_);
lean_dec_ref_known(v_a_2367_, 1);
v_snd_2372_ = lean_ctor_get(v_val_2371_, 1);
lean_inc(v_snd_2372_);
lean_dec(v_val_2371_);
v___x_2373_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2373_, 0, lean_box(0));
lean_closure_set(v___x_2373_, 1, v_snd_2372_);
v___x_2374_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2373_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v_stx_2332_ = v_a_2375_;
goto _start;
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
v_a_2377_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2374_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2374_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___x_2567_; uint8_t v___x_2568_; uint8_t v___x_2569_; 
lean_dec(v_a_2367_);
v___x_2567_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2332_);
v___x_2568_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2567_);
v___x_2569_ = 1;
if (v___x_2568_ == 0)
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2332_);
v___x_2571_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2332_);
v___x_2573_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2574_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2332_);
v___x_2575_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2332_);
v___x_2577_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2578_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2332_);
v___x_2579_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; uint8_t v___x_2581_; 
lean_del_object(v___x_2369_);
v___x_2580_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2332_);
v___x_2581_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2332_);
v___x_2583_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2582_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; 
v___x_2584_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2332_);
v___x_2585_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2332_);
v___x_2647_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2332_);
v___x_2649_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2332_);
v___x_2651_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2332_);
v___x_2653_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2332_);
v___x_2655_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2332_);
v___x_2657_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___x_2658_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2332_);
v___x_2659_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2332_);
v___x_2661_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2332_);
v___x_2663_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50));
lean_inc(v_stx_2332_);
v___x_2665_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2332_);
v___x_2667_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2332_);
v___x_2669_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2332_);
v___x_2671_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; uint8_t v___x_2673_; 
v___x_2672_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2332_);
v___x_2673_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2674_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2332_);
v___x_2675_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2332_);
v___x_2677_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; uint8_t v___x_2679_; 
v___x_2678_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v_stx_2332_);
v___x_2679_ = l_Lean_Syntax_isOfKind(v_stx_2332_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v_env_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2680_ = lean_st_ref_get(v_a_2338_);
v_env_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc_ref(v_env_2681_);
lean_dec(v___x_2680_);
lean_inc_n(v_stx_2332_, 2);
v___x_2682_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2683_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2684_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2683_, v_env_2681_, v___x_2682_);
v___x_2685_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2686_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2684_, v___x_2685_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_2684_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2717_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2717_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2717_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v_fst_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2715_; 
v_fst_2691_ = lean_ctor_get(v_a_2687_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_a_2687_);
if (v_isSharedCheck_2715_ == 0)
{
lean_object* v_unused_2716_; 
v_unused_2716_ = lean_ctor_get(v_a_2687_, 1);
lean_dec(v_unused_2716_);
v___x_2693_ = v_a_2687_;
v_isShared_2694_ = v_isSharedCheck_2715_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_fst_2691_);
lean_dec(v_a_2687_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2715_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
if (lean_obj_tag(v_fst_2691_) == 0)
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
lean_del_object(v___x_2689_);
v___x_2695_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2696_ = l_Lean_MessageData_ofName(v___x_2682_);
lean_inc_ref(v___x_2696_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set_tag(v___x_2693_, 7);
lean_ctor_set(v___x_2693_, 1, v___x_2696_);
lean_ctor_set(v___x_2693_, 0, v___x_2695_);
v___x_2698_ = v___x_2693_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2699_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_2702_ = l_Lean_indentD(v___x_2701_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2700_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
lean_ctor_set(v___x_2706_, 1, v___x_2696_);
v___x_2707_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2708_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_2709_;
}
}
else
{
lean_object* v_val_2711_; lean_object* v___x_2713_; 
lean_del_object(v___x_2693_);
lean_dec(v___x_2682_);
lean_dec(v_stx_2332_);
v_val_2711_ = lean_ctor_get(v_fst_2691_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v_fst_2691_, 1);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v_val_2711_);
v___x_2713_ = v___x_2689_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_val_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v___x_2682_);
lean_dec(v_stx_2332_);
v_a_2718_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2686_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2686_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___y_2730_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_unsigned_to_nat(5u);
v___x_2728_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2727_);
v___x_2739_ = lean_unsigned_to_nat(6u);
v___x_2740_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2739_);
lean_dec(v_stx_2332_);
v___x_2741_ = l_Lean_Syntax_getOptional_x3f(v___x_2740_);
lean_dec(v___x_2740_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; 
v___x_2742_ = lean_box(0);
v___y_2730_ = v___x_2742_;
goto v___jp_2729_;
}
else
{
lean_object* v_val_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
v_val_2743_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2741_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_val_2743_);
lean_dec(v___x_2741_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_val_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
v___y_2730_ = v___x_2748_;
goto v___jp_2729_;
}
}
}
v___jp_2729_:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2728_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2731_) == 0)
{
if (lean_obj_tag(v___y_2730_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = l_Lean_NameSet_empty;
v___x_2734_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2734_, 0, v___x_2726_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*2, v___x_2677_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*2 + 1, v___x_2677_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*2 + 2, v___x_2677_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*2 + 3, v___x_2677_);
v___y_2354_ = v_a_2732_;
v_bodyInfo_2355_ = v___x_2734_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2735_; lean_object* v_val_2736_; lean_object* v___x_2737_; 
v_a_2735_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2731_, 1);
v_val_2736_ = lean_ctor_get(v___y_2730_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v___y_2730_, 1);
v___x_2737_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2736_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2737_, 1);
v___y_2354_ = v_a_2735_;
v_bodyInfo_2355_ = v_a_2738_;
goto v___jp_2353_;
}
else
{
lean_dec(v_a_2735_);
return v___x_2737_;
}
}
}
else
{
lean_dec(v___y_2730_);
return v___x_2731_;
}
}
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___y_2755_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2751_ = lean_unsigned_to_nat(1u);
v___x_2752_ = lean_unsigned_to_nat(5u);
v___x_2753_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2752_);
v___x_2764_ = lean_unsigned_to_nat(6u);
v___x_2765_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2764_);
lean_dec(v_stx_2332_);
v___x_2766_ = l_Lean_Syntax_getOptional_x3f(v___x_2765_);
lean_dec(v___x_2765_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_box(0);
v___y_2755_ = v___x_2767_;
goto v___jp_2754_;
}
else
{
lean_object* v_val_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_val_2768_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2766_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_val_2768_);
lean_dec(v___x_2766_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_val_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
v___y_2755_ = v___x_2773_;
goto v___jp_2754_;
}
}
}
v___jp_2754_:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2753_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2756_) == 0)
{
if (lean_obj_tag(v___y_2755_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = l_Lean_NameSet_empty;
v___x_2759_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2759_, 0, v___x_2751_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*2, v___x_2675_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*2 + 1, v___x_2675_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*2 + 2, v___x_2675_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*2 + 3, v___x_2675_);
v___y_2359_ = v_a_2757_;
v_bodyInfo_2360_ = v___x_2759_;
goto v___jp_2358_;
}
else
{
lean_object* v_a_2760_; lean_object* v_val_2761_; lean_object* v___x_2762_; 
v_a_2760_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2756_, 1);
v_val_2761_ = lean_ctor_get(v___y_2755_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v___y_2755_, 1);
v___x_2762_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2761_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___y_2359_ = v_a_2760_;
v_bodyInfo_2360_ = v_a_2763_;
goto v___jp_2358_;
}
else
{
lean_dec(v_a_2760_);
return v___x_2762_;
}
}
}
else
{
lean_dec(v___y_2755_);
return v___x_2756_;
}
}
}
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___x_2991_; uint8_t v___x_2992_; 
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = lean_unsigned_to_nat(1u);
v___x_2991_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2777_);
v___x_2992_ = l_Lean_Syntax_isNone(v___x_2991_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2993_ = lean_unsigned_to_nat(5u);
v___x_2994_ = l_Lean_Syntax_matchesNull(v___x_2991_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; lean_object* v_env_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2995_ = lean_st_ref_get(v_a_2338_);
v_env_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc_ref(v_env_2996_);
lean_dec(v___x_2995_);
lean_inc_n(v_stx_2332_, 2);
v___x_2997_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2998_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2999_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2998_, v_env_2996_, v___x_2997_);
v___x_3000_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3001_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2999_, v___x_3000_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_2999_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3032_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3032_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3032_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v_fst_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3030_; 
v_fst_3006_ = lean_ctor_get(v_a_3002_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_a_3002_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; 
v_unused_3031_ = lean_ctor_get(v_a_3002_, 1);
lean_dec(v_unused_3031_);
v___x_3008_ = v_a_3002_;
v_isShared_3009_ = v_isSharedCheck_3030_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_fst_3006_);
lean_dec(v_a_3002_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3030_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
if (lean_obj_tag(v_fst_3006_) == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
lean_del_object(v___x_3004_);
v___x_3010_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3011_ = l_Lean_MessageData_ofName(v___x_2997_);
lean_inc_ref(v___x_3011_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set_tag(v___x_3008_, 7);
lean_ctor_set(v___x_3008_, 1, v___x_3011_);
lean_ctor_set(v___x_3008_, 0, v___x_3010_);
v___x_3013_ = v___x_3008_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3014_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3017_ = l_Lean_indentD(v___x_3016_);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3015_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3018_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set(v___x_3021_, 1, v___x_3011_);
v___x_3022_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3023_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3024_;
}
}
else
{
lean_object* v_val_3026_; lean_object* v___x_3028_; 
lean_del_object(v___x_3008_);
lean_dec(v___x_2997_);
lean_dec(v_stx_2332_);
v_val_3026_ = lean_ctor_get(v_fst_3006_, 0);
lean_inc(v_val_3026_);
lean_dec_ref_known(v_fst_3006_, 1);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v_val_3026_);
v___x_3028_ = v___x_3004_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_val_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v___x_2997_);
lean_dec(v_stx_2332_);
v_a_3033_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3001_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3001_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
v___y_2779_ = v_a_2333_;
v___y_2780_ = v_a_2334_;
v___y_2781_ = v_a_2335_;
v___y_2782_ = v_a_2336_;
v___y_2783_ = v_a_2337_;
v___y_2784_ = v_a_2338_;
goto v___jp_2778_;
}
}
else
{
lean_dec(v___x_2991_);
v___y_2779_ = v_a_2333_;
v___y_2780_ = v_a_2334_;
v___y_2781_ = v_a_2335_;
v___y_2782_ = v_a_2336_;
v___y_2783_ = v_a_2337_;
v___y_2784_ = v_a_2338_;
goto v___jp_2778_;
}
v___jp_2778_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2785_ = lean_unsigned_to_nat(4u);
v___x_2786_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2785_);
v___x_2787_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v___x_2786_);
v___x_2788_ = l_Lean_Syntax_isOfKind(v___x_2786_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v_env_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
lean_dec(v___x_2786_);
v___x_2789_ = lean_st_ref_get(v___y_2784_);
v_env_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc_ref(v_env_2790_);
lean_dec(v___x_2789_);
lean_inc_n(v_stx_2332_, 2);
v___x_2791_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2792_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2793_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2792_, v_env_2790_, v___x_2791_);
v___x_2794_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2795_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2793_, v___x_2794_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___x_2793_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2826_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2826_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2826_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v_fst_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2824_; 
v_fst_2800_ = lean_ctor_get(v_a_2796_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_a_2796_);
if (v_isSharedCheck_2824_ == 0)
{
lean_object* v_unused_2825_; 
v_unused_2825_ = lean_ctor_get(v_a_2796_, 1);
lean_dec(v_unused_2825_);
v___x_2802_ = v_a_2796_;
v_isShared_2803_ = v_isSharedCheck_2824_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_fst_2800_);
lean_dec(v_a_2796_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2824_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
if (lean_obj_tag(v_fst_2800_) == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
lean_del_object(v___x_2798_);
v___x_2804_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2805_ = l_Lean_MessageData_ofName(v___x_2791_);
lean_inc_ref(v___x_2805_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set_tag(v___x_2802_, 7);
lean_ctor_set(v___x_2802_, 1, v___x_2805_);
lean_ctor_set(v___x_2802_, 0, v___x_2804_);
v___x_2807_ = v___x_2802_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2808_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2807_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_2811_ = l_Lean_indentD(v___x_2810_);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2809_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v___x_2805_);
v___x_2816_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2817_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v___x_2818_;
}
}
else
{
lean_object* v_val_2820_; lean_object* v___x_2822_; 
lean_del_object(v___x_2802_);
lean_dec(v___x_2791_);
lean_dec(v_stx_2332_);
v_val_2820_ = lean_ctor_get(v_fst_2800_, 0);
lean_inc(v_val_2820_);
lean_dec_ref_known(v_fst_2800_, 1);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v_val_2820_);
v___x_2822_ = v___x_2798_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_val_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v___x_2791_);
lean_dec(v_stx_2332_);
v_a_2827_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2795_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2795_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; size_t v_sz_2837_; size_t v___x_2838_; lean_object* v___x_2839_; 
v___x_2835_ = l_Lean_Syntax_getArg(v___x_2786_, v___x_2776_);
v___x_2836_ = l_Lean_Syntax_getArgs(v___x_2835_);
lean_dec(v___x_2835_);
v_sz_2837_ = lean_array_size(v___x_2836_);
v___x_2838_ = ((size_t)0ULL);
v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2837_, v___x_2838_, v___x_2836_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v___x_2840_; lean_object* v_env_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec(v___x_2786_);
v___x_2840_ = lean_st_ref_get(v___y_2784_);
v_env_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc_ref(v_env_2841_);
lean_dec(v___x_2840_);
lean_inc_n(v_stx_2332_, 2);
v___x_2842_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2843_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2844_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2843_, v_env_2841_, v___x_2842_);
v___x_2845_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2846_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2844_, v___x_2845_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___x_2844_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2877_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2877_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2877_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v_fst_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2875_; 
v_fst_2851_ = lean_ctor_get(v_a_2847_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_a_2847_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; 
v_unused_2876_ = lean_ctor_get(v_a_2847_, 1);
lean_dec(v_unused_2876_);
v___x_2853_ = v_a_2847_;
v_isShared_2854_ = v_isSharedCheck_2875_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_fst_2851_);
lean_dec(v_a_2847_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2875_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
if (lean_obj_tag(v_fst_2851_) == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2858_; 
lean_del_object(v___x_2849_);
v___x_2855_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2856_ = l_Lean_MessageData_ofName(v___x_2842_);
lean_inc_ref(v___x_2856_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set_tag(v___x_2853_, 7);
lean_ctor_set(v___x_2853_, 1, v___x_2856_);
lean_ctor_set(v___x_2853_, 0, v___x_2855_);
v___x_2858_ = v___x_2853_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2859_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_2862_ = l_Lean_indentD(v___x_2861_);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2860_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___x_2856_);
v___x_2867_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2868_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v___x_2869_;
}
}
else
{
lean_object* v_val_2871_; lean_object* v___x_2873_; 
lean_del_object(v___x_2853_);
lean_dec(v___x_2842_);
lean_dec(v_stx_2332_);
v_val_2871_ = lean_ctor_get(v_fst_2851_, 0);
lean_inc(v_val_2871_);
lean_dec_ref_known(v_fst_2851_, 1);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v_val_2871_);
v___x_2873_ = v___x_2849_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_val_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec(v___x_2842_);
lean_dec(v_stx_2332_);
v_a_2878_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2846_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2846_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_val_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v_val_2886_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_val_2886_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2887_ = l_Lean_Syntax_getArg(v___x_2786_, v___x_2777_);
lean_dec(v___x_2786_);
v___x_2888_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
lean_inc(v___x_2887_);
v___x_2889_ = l_Lean_Syntax_isOfKind(v___x_2887_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; lean_object* v_env_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_dec(v___x_2887_);
lean_dec(v_val_2886_);
v___x_2890_ = lean_st_ref_get(v___y_2784_);
v_env_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc_ref(v_env_2891_);
lean_dec(v___x_2890_);
lean_inc_n(v_stx_2332_, 2);
v___x_2892_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2893_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2894_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2893_, v_env_2891_, v___x_2892_);
v___x_2895_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2896_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2894_, v___x_2895_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___x_2894_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2927_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2927_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2927_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v_fst_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2925_; 
v_fst_2901_ = lean_ctor_get(v_a_2897_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_a_2897_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; 
v_unused_2926_ = lean_ctor_get(v_a_2897_, 1);
lean_dec(v_unused_2926_);
v___x_2903_ = v_a_2897_;
v_isShared_2904_ = v_isSharedCheck_2925_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_fst_2901_);
lean_dec(v_a_2897_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2925_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
if (lean_obj_tag(v_fst_2901_) == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
lean_del_object(v___x_2899_);
v___x_2905_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2906_ = l_Lean_MessageData_ofName(v___x_2892_);
lean_inc_ref(v___x_2906_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set_tag(v___x_2903_, 7);
lean_ctor_set(v___x_2903_, 1, v___x_2906_);
lean_ctor_set(v___x_2903_, 0, v___x_2905_);
v___x_2908_ = v___x_2903_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2909_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_2912_ = l_Lean_indentD(v___x_2911_);
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2910_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2913_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
lean_ctor_set(v___x_2916_, 1, v___x_2906_);
v___x_2917_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2918_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v___x_2919_;
}
}
else
{
lean_object* v_val_2921_; lean_object* v___x_2923_; 
lean_del_object(v___x_2903_);
lean_dec(v___x_2892_);
lean_dec(v_stx_2332_);
v_val_2921_ = lean_ctor_get(v_fst_2901_, 0);
lean_inc(v_val_2921_);
lean_dec_ref_known(v_fst_2901_, 1);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v_val_2921_);
v___x_2923_ = v___x_2899_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_val_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v___x_2892_);
lean_dec(v_stx_2332_);
v_a_2928_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2896_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2896_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2936_ = l_Lean_Syntax_getArg(v___x_2887_, v___x_2777_);
v___x_2937_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
v___x_2938_ = l_Lean_Syntax_isOfKind(v___x_2936_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; lean_object* v_env_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_dec(v___x_2887_);
lean_dec(v_val_2886_);
v___x_2939_ = lean_st_ref_get(v___y_2784_);
v_env_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc_ref(v_env_2940_);
lean_dec(v___x_2939_);
lean_inc_n(v_stx_2332_, 2);
v___x_2941_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2942_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2943_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2942_, v_env_2940_, v___x_2941_);
v___x_2944_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2945_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2943_, v___x_2944_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___x_2943_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2976_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2976_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2976_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v_fst_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2974_; 
v_fst_2950_ = lean_ctor_get(v_a_2946_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_a_2946_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; 
v_unused_2975_ = lean_ctor_get(v_a_2946_, 1);
lean_dec(v_unused_2975_);
v___x_2952_ = v_a_2946_;
v_isShared_2953_ = v_isSharedCheck_2974_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_fst_2950_);
lean_dec(v_a_2946_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2974_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
if (lean_obj_tag(v_fst_2950_) == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2957_; 
lean_del_object(v___x_2948_);
v___x_2954_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2955_ = l_Lean_MessageData_ofName(v___x_2941_);
lean_inc_ref(v___x_2955_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set_tag(v___x_2952_, 7);
lean_ctor_set(v___x_2952_, 1, v___x_2955_);
lean_ctor_set(v___x_2952_, 0, v___x_2954_);
v___x_2957_ = v___x_2952_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2958_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_2961_ = l_Lean_indentD(v___x_2960_);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2959_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v___x_2955_);
v___x_2966_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2965_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2967_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v___x_2968_;
}
}
else
{
lean_object* v_val_2970_; lean_object* v___x_2972_; 
lean_del_object(v___x_2952_);
lean_dec(v___x_2941_);
lean_dec(v_stx_2332_);
v_val_2970_ = lean_ctor_get(v_fst_2950_, 0);
lean_inc(v_val_2970_);
lean_dec_ref_known(v_fst_2950_, 1);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v_val_2970_);
v___x_2972_ = v___x_2948_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_val_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v___x_2941_);
lean_dec(v_stx_2332_);
v_a_2977_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2945_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2945_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec(v_stx_2332_);
v___x_2985_ = lean_unsigned_to_nat(3u);
v___x_2986_ = l_Lean_Syntax_getArg(v___x_2887_, v___x_2985_);
lean_dec(v___x_2887_);
v___x_2987_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2986_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; size_t v_sz_2989_; lean_object* v___x_2990_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v_sz_2989_ = lean_array_size(v_val_2886_);
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2886_, v_sz_2989_, v___x_2838_, v_a_2988_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v_val_2886_);
return v___x_2990_;
}
else
{
lean_dec(v_val_2886_);
return v___x_2987_;
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
lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_dec(v_stx_2332_);
v___x_3041_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
return v___x_3042_;
}
}
else
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_dec(v_stx_2332_);
v___x_3043_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
return v___x_3044_;
}
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec(v_stx_2332_);
v___x_3045_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
return v___x_3046_;
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec(v_stx_2332_);
v___x_3047_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec(v_stx_2332_);
v___x_3049_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
return v___x_3050_;
}
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; size_t v_sz_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v___x_3051_ = lean_unsigned_to_nat(2u);
v___x_3052_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3051_);
v___x_3053_ = l_Lean_Syntax_getArgs(v___x_3052_);
lean_dec(v___x_3052_);
v_sz_3054_ = lean_array_size(v___x_3053_);
v___x_3055_ = ((size_t)0ULL);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3054_, v___x_3055_, v___x_3053_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3057_; lean_object* v_env_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3057_ = lean_st_ref_get(v_a_2338_);
v_env_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc_ref(v_env_3058_);
lean_dec(v___x_3057_);
lean_inc_n(v_stx_2332_, 2);
v___x_3059_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3060_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3061_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3060_, v_env_3058_, v___x_3059_);
v___x_3062_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3063_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3061_, v___x_3062_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3061_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3094_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3094_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3094_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v_fst_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3092_; 
v_fst_3068_ = lean_ctor_get(v_a_3064_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_a_3064_);
if (v_isSharedCheck_3092_ == 0)
{
lean_object* v_unused_3093_; 
v_unused_3093_ = lean_ctor_get(v_a_3064_, 1);
lean_dec(v_unused_3093_);
v___x_3070_ = v_a_3064_;
v_isShared_3071_ = v_isSharedCheck_3092_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_fst_3068_);
lean_dec(v_a_3064_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3092_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
if (lean_obj_tag(v_fst_3068_) == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
lean_del_object(v___x_3066_);
v___x_3072_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3073_ = l_Lean_MessageData_ofName(v___x_3059_);
lean_inc_ref(v___x_3073_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set_tag(v___x_3070_, 7);
lean_ctor_set(v___x_3070_, 1, v___x_3073_);
lean_ctor_set(v___x_3070_, 0, v___x_3072_);
v___x_3075_ = v___x_3070_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3076_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3079_ = l_Lean_indentD(v___x_3078_);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3077_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___x_3073_);
v___x_3084_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3083_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3085_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3086_;
}
}
else
{
lean_object* v_val_3088_; lean_object* v___x_3090_; 
lean_del_object(v___x_3070_);
lean_dec(v___x_3059_);
lean_dec(v_stx_2332_);
v_val_3088_ = lean_ctor_get(v_fst_3068_, 0);
lean_inc(v_val_3088_);
lean_dec_ref_known(v_fst_3068_, 1);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v_val_3088_);
v___x_3090_ = v___x_3066_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_val_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v___x_3059_);
lean_dec(v_stx_2332_);
v_a_3095_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3063_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3063_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v_val_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3237_; 
v_val_3103_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3105_ = v___x_3056_;
v_isShared_3106_ = v_isSharedCheck_3237_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_val_3103_);
lean_dec(v___x_3056_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3237_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v_finSeq_x3f_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3107_ = lean_unsigned_to_nat(1u);
v___x_3108_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3107_);
v___x_3132_ = lean_unsigned_to_nat(3u);
v___x_3133_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3132_);
v___x_3134_ = l_Lean_Syntax_isNone(v___x_3133_);
if (v___x_3134_ == 0)
{
uint8_t v___x_3135_; 
lean_inc(v___x_3133_);
v___x_3135_ = l_Lean_Syntax_matchesNull(v___x_3133_, v___x_3107_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v_env_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec(v___x_3133_);
lean_dec(v___x_3108_);
lean_del_object(v___x_3105_);
lean_dec(v_val_3103_);
v___x_3136_ = lean_st_ref_get(v_a_2338_);
v_env_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc_ref(v_env_3137_);
lean_dec(v___x_3136_);
lean_inc_n(v_stx_2332_, 2);
v___x_3138_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3139_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3140_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3139_, v_env_3137_, v___x_3138_);
v___x_3141_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3142_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3140_, v___x_3141_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3140_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3173_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3173_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3173_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_fst_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3171_; 
v_fst_3147_ = lean_ctor_get(v_a_3143_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_a_3143_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v_a_3143_, 1);
lean_dec(v_unused_3172_);
v___x_3149_ = v_a_3143_;
v_isShared_3150_ = v_isSharedCheck_3171_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_fst_3147_);
lean_dec(v_a_3143_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3171_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
if (lean_obj_tag(v_fst_3147_) == 0)
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3154_; 
lean_del_object(v___x_3145_);
v___x_3151_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3152_ = l_Lean_MessageData_ofName(v___x_3138_);
lean_inc_ref(v___x_3152_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set_tag(v___x_3149_, 7);
lean_ctor_set(v___x_3149_, 1, v___x_3152_);
lean_ctor_set(v___x_3149_, 0, v___x_3151_);
v___x_3154_ = v___x_3149_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3155_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3154_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3158_ = l_Lean_indentD(v___x_3157_);
v___x_3159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3156_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
lean_ctor_set(v___x_3162_, 1, v___x_3152_);
v___x_3163_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3164_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3165_;
}
}
else
{
lean_object* v_val_3167_; lean_object* v___x_3169_; 
lean_del_object(v___x_3149_);
lean_dec(v___x_3138_);
lean_dec(v_stx_2332_);
v_val_3167_ = lean_ctor_get(v_fst_3147_, 0);
lean_inc(v_val_3167_);
lean_dec_ref_known(v_fst_3147_, 1);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v_val_3167_);
v___x_3169_ = v___x_3145_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_val_3167_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v___x_3138_);
lean_dec(v_stx_2332_);
v_a_3174_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3142_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3142_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = l_Lean_Syntax_getArg(v___x_3133_, v___x_3182_);
lean_dec(v___x_3133_);
v___x_3184_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
lean_inc(v___x_3183_);
v___x_3185_ = l_Lean_Syntax_isOfKind(v___x_3183_, v___x_3184_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; lean_object* v_env_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec(v___x_3183_);
lean_dec(v___x_3108_);
lean_del_object(v___x_3105_);
lean_dec(v_val_3103_);
v___x_3186_ = lean_st_ref_get(v_a_2338_);
v_env_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc_ref(v_env_3187_);
lean_dec(v___x_3186_);
lean_inc_n(v_stx_2332_, 2);
v___x_3188_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3189_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3190_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3189_, v_env_3187_, v___x_3188_);
v___x_3191_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3192_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3190_, v___x_3191_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3190_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3223_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3223_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3223_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_fst_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3221_; 
v_fst_3197_ = lean_ctor_get(v_a_3193_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_a_3193_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_a_3193_, 1);
lean_dec(v_unused_3222_);
v___x_3199_ = v_a_3193_;
v_isShared_3200_ = v_isSharedCheck_3221_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_fst_3197_);
lean_dec(v_a_3193_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3221_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
if (lean_obj_tag(v_fst_3197_) == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_del_object(v___x_3195_);
v___x_3201_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3202_ = l_Lean_MessageData_ofName(v___x_3188_);
lean_inc_ref(v___x_3202_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 7);
lean_ctor_set(v___x_3199_, 1, v___x_3202_);
lean_ctor_set(v___x_3199_, 0, v___x_3201_);
v___x_3204_ = v___x_3199_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3205_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3204_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3208_ = l_Lean_indentD(v___x_3207_);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3206_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v___x_3202_);
v___x_3213_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3214_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3215_;
}
}
else
{
lean_object* v_val_3217_; lean_object* v___x_3219_; 
lean_del_object(v___x_3199_);
lean_dec(v___x_3188_);
lean_dec(v_stx_2332_);
v_val_3217_ = lean_ctor_get(v_fst_3197_, 0);
lean_inc(v_val_3217_);
lean_dec_ref_known(v_fst_3197_, 1);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_val_3217_);
v___x_3219_ = v___x_3195_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_val_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec(v___x_3188_);
lean_dec(v_stx_2332_);
v_a_3224_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3192_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3192_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3234_; 
lean_dec(v_stx_2332_);
v___x_3232_ = l_Lean_Syntax_getArg(v___x_3183_, v___x_3107_);
lean_dec(v___x_3183_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3232_);
v___x_3234_ = v___x_3105_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
v_finSeq_x3f_3110_ = v___x_3234_;
v___y_3111_ = v_a_2333_;
v___y_3112_ = v_a_2334_;
v___y_3113_ = v_a_2335_;
v___y_3114_ = v_a_2336_;
v___y_3115_ = v_a_2337_;
v___y_3116_ = v_a_2338_;
goto v___jp_3109_;
}
}
}
}
else
{
lean_object* v___x_3236_; 
lean_dec(v___x_3133_);
lean_del_object(v___x_3105_);
lean_dec(v_stx_2332_);
v___x_3236_ = lean_box(0);
v_finSeq_x3f_3110_ = v___x_3236_;
v___y_3111_ = v_a_2333_;
v___y_3112_ = v_a_2334_;
v___y_3113_ = v_a_2335_;
v___y_3114_ = v_a_2336_;
v___y_3115_ = v_a_2337_;
v___y_3116_ = v_a_2338_;
goto v___jp_3109_;
}
v___jp_3109_:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3108_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; size_t v_sz_3119_; lean_object* v___x_3120_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v_sz_3119_ = lean_array_size(v_val_3103_);
v___x_3120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3103_, v_sz_3119_, v___x_3055_, v_a_3118_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v_val_3103_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3122_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3131_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3127_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3121_, v_a_3123_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3127_);
v___x_3129_ = v___x_3125_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
else
{
lean_dec(v_a_3121_);
return v___x_3122_;
}
}
else
{
lean_dec(v_finSeq_x3f_3110_);
return v___x_3120_;
}
}
else
{
lean_dec(v_finSeq_x3f_3110_);
lean_dec(v_val_3103_);
return v___x_3117_;
}
}
}
}
}
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = lean_unsigned_to_nat(1u);
v___x_3239_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3238_);
lean_dec(v_stx_2332_);
v___x_3240_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3239_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3265_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3243_ = v___x_3240_;
v_isShared_3244_ = v_isSharedCheck_3265_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3265_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
uint8_t v_breaks_3245_; uint8_t v_returnsEarly_3246_; lean_object* v_reassigns_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3263_; 
v_breaks_3245_ = lean_ctor_get_uint8(v_a_3241_, sizeof(void*)*2);
v_returnsEarly_3246_ = lean_ctor_get_uint8(v_a_3241_, sizeof(void*)*2 + 2);
v_reassigns_3247_ = lean_ctor_get(v_a_3241_, 1);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_a_3241_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; 
v_unused_3264_ = lean_ctor_get(v_a_3241_, 0);
lean_dec(v_unused_3264_);
v___x_3249_ = v_a_3241_;
v_isShared_3250_ = v_isSharedCheck_3263_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_reassigns_3247_);
lean_dec(v_a_3241_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3263_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___y_3252_; uint8_t v___y_3253_; lean_object* v___y_3261_; 
if (v_breaks_3245_ == 0)
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_unsigned_to_nat(0u);
v___y_3261_ = v___x_3262_;
goto v___jp_3260_;
}
else
{
v___y_3261_ = v___x_3238_;
goto v___jp_3260_;
}
v___jp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___y_3252_);
v___x_3255_ = v___x_3249_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___y_3252_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_reassigns_3247_);
lean_ctor_set_uint8(v_reuseFailAlloc_3259_, sizeof(void*)*2 + 2, v_returnsEarly_3246_);
v___x_3255_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3257_; 
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*2, v___x_2659_);
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*2 + 1, v___x_2659_);
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*2 + 3, v___y_3253_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3255_);
v___x_3257_ = v___x_3243_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
v___jp_3260_:
{
if (v_breaks_3245_ == 0)
{
v___y_3252_ = v___y_3261_;
v___y_3253_ = v___x_2661_;
goto v___jp_3251_;
}
else
{
v___y_3252_ = v___y_3261_;
v___y_3253_ = v___x_2659_;
goto v___jp_3251_;
}
}
}
}
}
else
{
return v___x_3240_;
}
}
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3297_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = lean_unsigned_to_nat(1u);
v___x_3446_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3267_);
v___x_3447_ = l_Lean_Syntax_getArgs(v___x_3446_);
lean_dec(v___x_3446_);
v___x_3448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3449_ = lean_array_get_size(v___x_3447_);
v___x_3450_ = lean_nat_dec_lt(v___x_3266_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_dec_ref(v___x_3447_);
v___y_3297_ = v___x_3448_;
goto v___jp_3296_;
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v___x_3451_ = lean_box(v___x_2659_);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v___x_3448_);
v___x_3453_ = lean_nat_dec_le(v___x_3449_, v___x_3449_);
if (v___x_3453_ == 0)
{
if (v___x_3450_ == 0)
{
lean_dec_ref_known(v___x_3452_, 2);
lean_dec_ref(v___x_3447_);
v___y_3297_ = v___x_3448_;
goto v___jp_3296_;
}
else
{
size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; lean_object* v_snd_3457_; 
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = lean_usize_of_nat(v___x_3449_);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2659_, v___x_2657_, v___x_3447_, v___x_3454_, v___x_3455_, v___x_3452_);
lean_dec_ref(v___x_3447_);
v_snd_3457_ = lean_ctor_get(v___x_3456_, 1);
lean_inc(v_snd_3457_);
lean_dec_ref(v___x_3456_);
v___y_3297_ = v_snd_3457_;
goto v___jp_3296_;
}
}
else
{
size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; lean_object* v_snd_3461_; 
v___x_3458_ = ((size_t)0ULL);
v___x_3459_ = lean_usize_of_nat(v___x_3449_);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2659_, v___x_2657_, v___x_3447_, v___x_3458_, v___x_3459_, v___x_3452_);
lean_dec_ref(v___x_3447_);
v_snd_3461_ = lean_ctor_get(v___x_3460_, 1);
lean_inc(v_snd_3461_);
lean_dec_ref(v___x_3460_);
v___y_3297_ = v_snd_3461_;
goto v___jp_3296_;
}
}
v___jp_3268_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = lean_unsigned_to_nat(4u);
v___x_3276_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3275_);
lean_dec(v_stx_2332_);
v___x_3277_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3276_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3295_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3295_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3295_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
uint8_t v_returnsEarly_3282_; lean_object* v_reassigns_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3293_; 
v_returnsEarly_3282_ = lean_ctor_get_uint8(v_a_3278_, sizeof(void*)*2 + 2);
v_reassigns_3283_ = lean_ctor_get(v_a_3278_, 1);
v_isSharedCheck_3293_ = !lean_is_exclusive(v_a_3278_);
if (v_isSharedCheck_3293_ == 0)
{
lean_object* v_unused_3294_; 
v_unused_3294_ = lean_ctor_get(v_a_3278_, 0);
lean_dec(v_unused_3294_);
v___x_3285_ = v_a_3278_;
v_isShared_3286_ = v_isSharedCheck_3293_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_reassigns_3283_);
lean_dec(v_a_3278_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3293_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3267_);
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_reassigns_3283_);
lean_ctor_set_uint8(v_reuseFailAlloc_3292_, sizeof(void*)*2 + 2, v_returnsEarly_3282_);
v___x_3288_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3290_; 
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*2, v___x_2657_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*2 + 1, v___x_2657_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*2 + 3, v___x_2657_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3288_);
v___x_3290_ = v___x_3280_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
else
{
return v___x_3277_;
}
}
v___jp_3296_:
{
size_t v_sz_3298_; size_t v___x_3299_; lean_object* v___x_3300_; 
v_sz_3298_ = lean_array_size(v___y_3297_);
v___x_3299_ = ((size_t)0ULL);
v___x_3300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3298_, v___x_3299_, v___y_3297_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v___x_3301_; lean_object* v_env_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3301_ = lean_st_ref_get(v_a_2338_);
v_env_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc_ref(v_env_3302_);
lean_dec(v___x_3301_);
lean_inc_n(v_stx_2332_, 2);
v___x_3303_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3304_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3305_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3304_, v_env_3302_, v___x_3303_);
v___x_3306_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3307_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3305_, v___x_3306_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3305_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3338_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3338_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3338_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v_fst_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3336_; 
v_fst_3312_ = lean_ctor_get(v_a_3308_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_a_3308_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v_a_3308_, 1);
lean_dec(v_unused_3337_);
v___x_3314_ = v_a_3308_;
v_isShared_3315_ = v_isSharedCheck_3336_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_fst_3312_);
lean_dec(v_a_3308_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3336_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
if (lean_obj_tag(v_fst_3312_) == 0)
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
lean_del_object(v___x_3310_);
v___x_3316_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3317_ = l_Lean_MessageData_ofName(v___x_3303_);
lean_inc_ref(v___x_3317_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 7);
lean_ctor_set(v___x_3314_, 1, v___x_3317_);
lean_ctor_set(v___x_3314_, 0, v___x_3316_);
v___x_3319_ = v___x_3314_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3320_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3323_ = l_Lean_indentD(v___x_3322_);
v___x_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3321_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
lean_ctor_set(v___x_3327_, 1, v___x_3317_);
v___x_3328_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3329_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3330_;
}
}
else
{
lean_object* v_val_3332_; lean_object* v___x_3334_; 
lean_del_object(v___x_3314_);
lean_dec(v___x_3303_);
lean_dec(v_stx_2332_);
v_val_3332_ = lean_ctor_get(v_fst_3312_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v_fst_3312_, 1);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v_val_3332_);
v___x_3334_ = v___x_3310_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_val_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec(v___x_3303_);
lean_dec(v_stx_2332_);
v_a_3339_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3307_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3307_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
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
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
lean_dec_ref_known(v___x_3300_, 1);
v___x_3347_ = lean_unsigned_to_nat(2u);
v___x_3348_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3347_);
v___x_3349_ = l_Lean_Syntax_isNone(v___x_3348_);
if (v___x_3349_ == 0)
{
uint8_t v___x_3350_; 
lean_inc(v___x_3348_);
v___x_3350_ = l_Lean_Syntax_matchesNull(v___x_3348_, v___x_3267_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; lean_object* v_env_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec(v___x_3348_);
v___x_3351_ = lean_st_ref_get(v_a_2338_);
v_env_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc_ref(v_env_3352_);
lean_dec(v___x_3351_);
lean_inc_n(v_stx_2332_, 2);
v___x_3353_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3354_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3355_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3354_, v_env_3352_, v___x_3353_);
v___x_3356_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3357_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3355_, v___x_3356_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3355_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3388_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3388_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3388_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_fst_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3386_; 
v_fst_3362_ = lean_ctor_get(v_a_3358_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_a_3358_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v_a_3358_, 1);
lean_dec(v_unused_3387_);
v___x_3364_ = v_a_3358_;
v_isShared_3365_ = v_isSharedCheck_3386_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_fst_3362_);
lean_dec(v_a_3358_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3386_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
if (lean_obj_tag(v_fst_3362_) == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
lean_del_object(v___x_3360_);
v___x_3366_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3367_ = l_Lean_MessageData_ofName(v___x_3353_);
lean_inc_ref(v___x_3367_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 7);
lean_ctor_set(v___x_3364_, 1, v___x_3367_);
lean_ctor_set(v___x_3364_, 0, v___x_3366_);
v___x_3369_ = v___x_3364_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3370_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3373_ = l_Lean_indentD(v___x_3372_);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3371_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v___x_3367_);
v___x_3378_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3377_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
v___x_3380_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3379_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3380_;
}
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3384_; 
lean_del_object(v___x_3364_);
lean_dec(v___x_3353_);
lean_dec(v_stx_2332_);
v_val_3382_ = lean_ctor_get(v_fst_3362_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v_fst_3362_, 1);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v_val_3382_);
v___x_3384_ = v___x_3360_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_val_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v___x_3353_);
lean_dec(v_stx_2332_);
v_a_3389_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3357_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3357_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3397_ = l_Lean_Syntax_getArg(v___x_3348_, v___x_3266_);
lean_dec(v___x_3348_);
v___x_3398_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
v___x_3399_ = l_Lean_Syntax_isOfKind(v___x_3397_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; lean_object* v_env_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3400_ = lean_st_ref_get(v_a_2338_);
v_env_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc_ref(v_env_3401_);
lean_dec(v___x_3400_);
lean_inc_n(v_stx_2332_, 2);
v___x_3402_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3403_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3404_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3403_, v_env_3401_, v___x_3402_);
v___x_3405_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3406_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3404_, v___x_3405_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3404_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3437_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3437_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3437_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v_fst_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3435_; 
v_fst_3411_ = lean_ctor_get(v_a_3407_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_a_3407_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v_a_3407_, 1);
lean_dec(v_unused_3436_);
v___x_3413_ = v_a_3407_;
v_isShared_3414_ = v_isSharedCheck_3435_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_fst_3411_);
lean_dec(v_a_3407_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3435_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
if (lean_obj_tag(v_fst_3411_) == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
lean_del_object(v___x_3409_);
v___x_3415_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3416_ = l_Lean_MessageData_ofName(v___x_3402_);
lean_inc_ref(v___x_3416_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 7);
lean_ctor_set(v___x_3413_, 1, v___x_3416_);
lean_ctor_set(v___x_3413_, 0, v___x_3415_);
v___x_3418_ = v___x_3413_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3419_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3422_ = l_Lean_indentD(v___x_3421_);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3420_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
lean_ctor_set(v___x_3426_, 1, v___x_3416_);
v___x_3427_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3428_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3429_;
}
}
else
{
lean_object* v_val_3431_; lean_object* v___x_3433_; 
lean_del_object(v___x_3413_);
lean_dec(v___x_3402_);
lean_dec(v_stx_2332_);
v_val_3431_ = lean_ctor_get(v_fst_3411_, 0);
lean_inc(v_val_3431_);
lean_dec_ref_known(v_fst_3411_, 1);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v_val_3431_);
v___x_3433_ = v___x_3409_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_val_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v___x_3402_);
lean_dec(v_stx_2332_);
v_a_3438_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3406_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3406_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
v___y_3269_ = v_a_2333_;
v___y_3270_ = v_a_2334_;
v___y_3271_ = v_a_2335_;
v___y_3272_ = v_a_2336_;
v___y_3273_ = v_a_2337_;
v___y_3274_ = v_a_2338_;
goto v___jp_3268_;
}
}
}
else
{
lean_dec(v___x_3348_);
v___y_3269_ = v_a_2333_;
v___y_3270_ = v_a_2334_;
v___y_3271_ = v_a_2335_;
v___y_3272_ = v_a_2336_;
v___y_3273_ = v_a_2337_;
v___y_3274_ = v_a_2338_;
goto v___jp_3268_;
}
}
}
}
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3462_ = lean_unsigned_to_nat(1u);
v___x_3463_ = lean_unsigned_to_nat(3u);
v___x_3464_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3463_);
lean_dec(v_stx_2332_);
v___x_3465_ = l_Lean_NameSet_empty;
v___x_3466_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3466_, 0, v___x_3462_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*2, v___x_2655_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*2 + 1, v___x_2655_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*2 + 2, v___x_2655_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*2 + 3, v___x_2655_);
v___x_3467_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3464_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3476_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3476_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3476_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3474_; 
v___x_3472_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3466_, v_a_3468_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3472_);
v___x_3474_ = v___x_3470_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
else
{
lean_dec_ref_known(v___x_3466_, 2);
return v___x_3467_;
}
}
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; size_t v_sz_3480_; size_t v___x_3481_; lean_object* v___x_3482_; 
v___x_3477_ = lean_unsigned_to_nat(4u);
v___x_3478_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3477_);
v___x_3479_ = l_Lean_Syntax_getArgs(v___x_3478_);
lean_dec(v___x_3478_);
v_sz_3480_ = lean_array_size(v___x_3479_);
v___x_3481_ = ((size_t)0ULL);
v___x_3482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3480_, v___x_3481_, v___x_3479_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v___x_3483_; lean_object* v_env_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3483_ = lean_st_ref_get(v_a_2338_);
v_env_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc_ref(v_env_3484_);
lean_dec(v___x_3483_);
lean_inc_n(v_stx_2332_, 2);
v___x_3485_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3486_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3487_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3486_, v_env_3484_, v___x_3485_);
v___x_3488_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3489_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3487_, v___x_3488_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3487_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3520_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3520_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3520_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_fst_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3518_; 
v_fst_3494_ = lean_ctor_get(v_a_3490_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_a_3490_);
if (v_isSharedCheck_3518_ == 0)
{
lean_object* v_unused_3519_; 
v_unused_3519_ = lean_ctor_get(v_a_3490_, 1);
lean_dec(v_unused_3519_);
v___x_3496_ = v_a_3490_;
v_isShared_3497_ = v_isSharedCheck_3518_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_fst_3494_);
lean_dec(v_a_3490_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3518_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
if (lean_obj_tag(v_fst_3494_) == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
lean_del_object(v___x_3492_);
v___x_3498_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3499_ = l_Lean_MessageData_ofName(v___x_3485_);
lean_inc_ref(v___x_3499_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set_tag(v___x_3496_, 7);
lean_ctor_set(v___x_3496_, 1, v___x_3499_);
lean_ctor_set(v___x_3496_, 0, v___x_3498_);
v___x_3501_ = v___x_3496_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3502_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3501_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3505_ = l_Lean_indentD(v___x_3504_);
v___x_3506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3503_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3506_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
v___x_3509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
lean_ctor_set(v___x_3509_, 1, v___x_3499_);
v___x_3510_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3509_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3511_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3512_;
}
}
else
{
lean_object* v_val_3514_; lean_object* v___x_3516_; 
lean_del_object(v___x_3496_);
lean_dec(v___x_3485_);
lean_dec(v_stx_2332_);
v_val_3514_ = lean_ctor_get(v_fst_3494_, 0);
lean_inc(v_val_3514_);
lean_dec_ref_known(v_fst_3494_, 1);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v_val_3514_);
v___x_3516_ = v___x_3492_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_val_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v___x_3485_);
lean_dec(v_stx_2332_);
v_a_3521_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3489_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3489_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
else
{
lean_object* v_val_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3616_; 
v_val_3529_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3531_ = v___x_3482_;
v_isShared_3532_ = v_isSharedCheck_3616_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_val_3529_);
lean_dec(v___x_3482_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3616_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v_elseSeq_x3f_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3533_ = lean_unsigned_to_nat(3u);
v___x_3534_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3533_);
v___x_3559_ = lean_unsigned_to_nat(5u);
v___x_3560_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3559_);
v___x_3561_ = l_Lean_Syntax_isNone(v___x_3560_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3560_);
v___x_3563_ = l_Lean_Syntax_matchesNull(v___x_3560_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; lean_object* v_env_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec(v___x_3560_);
lean_dec(v___x_3534_);
lean_del_object(v___x_3531_);
lean_dec(v_val_3529_);
v___x_3564_ = lean_st_ref_get(v_a_2338_);
v_env_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc_ref(v_env_3565_);
lean_dec(v___x_3564_);
lean_inc_n(v_stx_2332_, 2);
v___x_3566_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3567_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3568_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3567_, v_env_3565_, v___x_3566_);
v___x_3569_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3570_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3568_, v___x_3569_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3568_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3601_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3601_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3601_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v_fst_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3599_; 
v_fst_3575_ = lean_ctor_get(v_a_3571_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v_a_3571_);
if (v_isSharedCheck_3599_ == 0)
{
lean_object* v_unused_3600_; 
v_unused_3600_ = lean_ctor_get(v_a_3571_, 1);
lean_dec(v_unused_3600_);
v___x_3577_ = v_a_3571_;
v_isShared_3578_ = v_isSharedCheck_3599_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_fst_3575_);
lean_dec(v_a_3571_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3599_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
if (lean_obj_tag(v_fst_3575_) == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
lean_del_object(v___x_3573_);
v___x_3579_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3580_ = l_Lean_MessageData_ofName(v___x_3566_);
lean_inc_ref(v___x_3580_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set_tag(v___x_3577_, 7);
lean_ctor_set(v___x_3577_, 1, v___x_3580_);
lean_ctor_set(v___x_3577_, 0, v___x_3579_);
v___x_3582_ = v___x_3577_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3583_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3586_ = l_Lean_indentD(v___x_3585_);
v___x_3587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3584_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
lean_ctor_set(v___x_3590_, 1, v___x_3580_);
v___x_3591_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3590_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3592_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3593_;
}
}
else
{
lean_object* v_val_3595_; lean_object* v___x_3597_; 
lean_del_object(v___x_3577_);
lean_dec(v___x_3566_);
lean_dec(v_stx_2332_);
v_val_3595_ = lean_ctor_get(v_fst_3575_, 0);
lean_inc(v_val_3595_);
lean_dec_ref_known(v_fst_3575_, 1);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v_val_3595_);
v___x_3597_ = v___x_3573_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_val_3595_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v___x_3566_);
lean_dec(v_stx_2332_);
v_a_3602_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3570_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3570_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3613_; 
lean_dec(v_stx_2332_);
v___x_3610_ = lean_unsigned_to_nat(1u);
v___x_3611_ = l_Lean_Syntax_getArg(v___x_3560_, v___x_3610_);
lean_dec(v___x_3560_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3611_);
v___x_3613_ = v___x_3531_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
v_elseSeq_x3f_3536_ = v___x_3613_;
v___y_3537_ = v_a_2333_;
v___y_3538_ = v_a_2334_;
v___y_3539_ = v_a_2335_;
v___y_3540_ = v_a_2336_;
v___y_3541_ = v_a_2337_;
v___y_3542_ = v_a_2338_;
goto v___jp_3535_;
}
}
}
else
{
lean_object* v___x_3615_; 
lean_dec(v___x_3560_);
lean_del_object(v___x_3531_);
lean_dec(v_stx_2332_);
v___x_3615_ = lean_box(0);
v_elseSeq_x3f_3536_ = v___x_3615_;
v___y_3537_ = v_a_2333_;
v___y_3538_ = v_a_2334_;
v___y_3539_ = v_a_2335_;
v___y_3540_ = v_a_2336_;
v___y_3541_ = v_a_2337_;
v___y_3542_ = v_a_2338_;
goto v___jp_3535_;
}
v___jp_3535_:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; size_t v_sz_3546_; lean_object* v___x_3547_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = l_Array_reverse___redArg(v_val_3529_);
v_sz_3546_ = lean_array_size(v___x_3545_);
v___x_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3545_, v_sz_3546_, v___x_3481_, v_a_3544_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec_ref(v___x_3545_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3549_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v___x_3549_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3534_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3558_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3558_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3558_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3554_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3550_, v_a_3548_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v___x_3554_);
v___x_3556_ = v___x_3552_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
else
{
lean_dec(v_a_3548_);
return v___x_3549_;
}
}
else
{
lean_dec(v___x_3534_);
return v___x_3547_;
}
}
else
{
lean_dec(v___x_3534_);
lean_dec(v_val_3529_);
return v___x_3543_;
}
}
}
}
}
}
else
{
lean_object* v___x_3617_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___x_3681_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3617_ = lean_unsigned_to_nat(0u);
v___x_3681_ = lean_unsigned_to_nat(1u);
v___x_3788_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3681_);
v___x_3789_ = l_Lean_Syntax_isNone(v___x_3788_);
if (v___x_3789_ == 0)
{
uint8_t v___x_3790_; 
lean_inc(v___x_3788_);
v___x_3790_ = l_Lean_Syntax_matchesNull(v___x_3788_, v___x_3681_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; lean_object* v_env_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_dec(v___x_3788_);
v___x_3791_ = lean_st_ref_get(v_a_2338_);
v_env_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc_ref(v_env_3792_);
lean_dec(v___x_3791_);
lean_inc_n(v_stx_2332_, 2);
v___x_3793_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3794_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3795_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3794_, v_env_3792_, v___x_3793_);
v___x_3796_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3797_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3795_, v___x_3796_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3795_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3828_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3828_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3828_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v_fst_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3826_; 
v_fst_3802_ = lean_ctor_get(v_a_3798_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_a_3798_);
if (v_isSharedCheck_3826_ == 0)
{
lean_object* v_unused_3827_; 
v_unused_3827_ = lean_ctor_get(v_a_3798_, 1);
lean_dec(v_unused_3827_);
v___x_3804_ = v_a_3798_;
v_isShared_3805_ = v_isSharedCheck_3826_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_fst_3802_);
lean_dec(v_a_3798_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3826_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
if (lean_obj_tag(v_fst_3802_) == 0)
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
lean_del_object(v___x_3800_);
v___x_3806_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3807_ = l_Lean_MessageData_ofName(v___x_3793_);
lean_inc_ref(v___x_3807_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set_tag(v___x_3804_, 7);
lean_ctor_set(v___x_3804_, 1, v___x_3807_);
lean_ctor_set(v___x_3804_, 0, v___x_3806_);
v___x_3809_ = v___x_3804_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3810_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3813_ = l_Lean_indentD(v___x_3812_);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3811_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3814_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
lean_ctor_set(v___x_3817_, 1, v___x_3807_);
v___x_3818_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3819_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3820_;
}
}
else
{
lean_object* v_val_3822_; lean_object* v___x_3824_; 
lean_del_object(v___x_3804_);
lean_dec(v___x_3793_);
lean_dec(v_stx_2332_);
v_val_3822_ = lean_ctor_get(v_fst_3802_, 0);
lean_inc(v_val_3822_);
lean_dec_ref_known(v_fst_3802_, 1);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v_val_3822_);
v___x_3824_ = v___x_3800_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_val_3822_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec(v___x_3793_);
lean_dec(v_stx_2332_);
v_a_3829_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3797_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3797_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v___x_3837_ = l_Lean_Syntax_getArg(v___x_3788_, v___x_3617_);
lean_dec(v___x_3788_);
v___x_3838_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3839_ = l_Lean_Syntax_isOfKind(v___x_3837_, v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v_env_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3840_ = lean_st_ref_get(v_a_2338_);
v_env_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc_ref(v_env_3841_);
lean_dec(v___x_3840_);
lean_inc_n(v_stx_2332_, 2);
v___x_3842_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3843_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3844_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3843_, v_env_3841_, v___x_3842_);
v___x_3845_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3846_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3844_, v___x_3845_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3844_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3877_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3877_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3877_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v_fst_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3875_; 
v_fst_3851_ = lean_ctor_get(v_a_3847_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_a_3847_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; 
v_unused_3876_ = lean_ctor_get(v_a_3847_, 1);
lean_dec(v_unused_3876_);
v___x_3853_ = v_a_3847_;
v_isShared_3854_ = v_isSharedCheck_3875_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_fst_3851_);
lean_dec(v_a_3847_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3875_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
if (lean_obj_tag(v_fst_3851_) == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
lean_del_object(v___x_3849_);
v___x_3855_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3856_ = l_Lean_MessageData_ofName(v___x_3842_);
lean_inc_ref(v___x_3856_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set_tag(v___x_3853_, 7);
lean_ctor_set(v___x_3853_, 1, v___x_3856_);
lean_ctor_set(v___x_3853_, 0, v___x_3855_);
v___x_3858_ = v___x_3853_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3859_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3858_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3862_ = l_Lean_indentD(v___x_3861_);
v___x_3863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3860_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3863_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
lean_ctor_set(v___x_3866_, 1, v___x_3856_);
v___x_3867_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3866_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3868_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3869_;
}
}
else
{
lean_object* v_val_3871_; lean_object* v___x_3873_; 
lean_del_object(v___x_3853_);
lean_dec(v___x_3842_);
lean_dec(v_stx_2332_);
v_val_3871_ = lean_ctor_get(v_fst_3851_, 0);
lean_inc(v_val_3871_);
lean_dec_ref_known(v_fst_3851_, 1);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v_val_3871_);
v___x_3873_ = v___x_3849_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_val_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec(v___x_3842_);
lean_dec(v_stx_2332_);
v_a_3878_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3846_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3846_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
else
{
v___y_3683_ = v_a_2333_;
v___y_3684_ = v_a_2334_;
v___y_3685_ = v_a_2335_;
v___y_3686_ = v_a_2336_;
v___y_3687_ = v_a_2337_;
v___y_3688_ = v_a_2338_;
goto v___jp_3682_;
}
}
}
else
{
lean_dec(v___x_3788_);
v___y_3683_ = v_a_2333_;
v___y_3684_ = v_a_2334_;
v___y_3685_ = v_a_2335_;
v___y_3686_ = v_a_2336_;
v___y_3687_ = v_a_2337_;
v___y_3688_ = v_a_2338_;
goto v___jp_3682_;
}
v___jp_3618_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3625_ = lean_unsigned_to_nat(6u);
v___x_3626_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3625_);
v___x_3627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3626_);
v___x_3628_ = l_Lean_Syntax_isOfKind(v___x_3626_, v___x_3627_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; lean_object* v_env_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
lean_dec(v___x_3626_);
v___x_3629_ = lean_st_ref_get(v___y_3624_);
v_env_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc_ref(v_env_3630_);
lean_dec(v___x_3629_);
lean_inc_n(v_stx_2332_, 2);
v___x_3631_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3632_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3633_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3632_, v_env_3630_, v___x_3631_);
v___x_3634_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3635_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3633_, v___x_3634_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___x_3633_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3666_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3638_ = v___x_3635_;
v_isShared_3639_ = v_isSharedCheck_3666_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3666_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v_fst_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3664_; 
v_fst_3640_ = lean_ctor_get(v_a_3636_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_a_3636_);
if (v_isSharedCheck_3664_ == 0)
{
lean_object* v_unused_3665_; 
v_unused_3665_ = lean_ctor_get(v_a_3636_, 1);
lean_dec(v_unused_3665_);
v___x_3642_ = v_a_3636_;
v_isShared_3643_ = v_isSharedCheck_3664_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_fst_3640_);
lean_dec(v_a_3636_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3664_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
if (lean_obj_tag(v_fst_3640_) == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
lean_del_object(v___x_3638_);
v___x_3644_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3645_ = l_Lean_MessageData_ofName(v___x_3631_);
lean_inc_ref(v___x_3645_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set_tag(v___x_3642_, 7);
lean_ctor_set(v___x_3642_, 1, v___x_3645_);
lean_ctor_set(v___x_3642_, 0, v___x_3644_);
v___x_3647_ = v___x_3642_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3648_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3651_ = l_Lean_indentD(v___x_3650_);
v___x_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3649_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
lean_ctor_set(v___x_3655_, 1, v___x_3645_);
v___x_3656_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3657_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
return v___x_3658_;
}
}
else
{
lean_object* v_val_3660_; lean_object* v___x_3662_; 
lean_del_object(v___x_3642_);
lean_dec(v___x_3631_);
lean_dec(v_stx_2332_);
v_val_3660_ = lean_ctor_get(v_fst_3640_, 0);
lean_inc(v_val_3660_);
lean_dec_ref_known(v_fst_3640_, 1);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v_val_3660_);
v___x_3662_ = v___x_3638_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_val_3660_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_dec(v___x_3631_);
lean_dec(v_stx_2332_);
v_a_3667_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3635_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3635_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; size_t v_sz_3678_; size_t v___x_3679_; lean_object* v___x_3680_; 
lean_dec(v_stx_2332_);
v___x_3675_ = l_Lean_Syntax_getArg(v___x_3626_, v___x_3617_);
lean_dec(v___x_3626_);
v___x_3676_ = l_Lean_Syntax_getArgs(v___x_3675_);
lean_dec(v___x_3675_);
v___x_3677_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_3678_ = lean_array_size(v___x_3676_);
v___x_3679_ = ((size_t)0ULL);
v___x_3680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2651_, v___x_3676_, v_sz_3678_, v___x_3679_, v___x_3677_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec_ref(v___x_3676_);
return v___x_3680_;
}
}
v___jp_3682_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v___x_3689_ = lean_unsigned_to_nat(2u);
v___x_3690_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3689_);
v___x_3691_ = l_Lean_Syntax_isNone(v___x_3690_);
if (v___x_3691_ == 0)
{
uint8_t v___x_3692_; 
lean_inc(v___x_3690_);
v___x_3692_ = l_Lean_Syntax_matchesNull(v___x_3690_, v___x_3681_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3693_; lean_object* v_env_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec(v___x_3690_);
v___x_3693_ = lean_st_ref_get(v___y_3688_);
v_env_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc_ref(v_env_3694_);
lean_dec(v___x_3693_);
lean_inc_n(v_stx_2332_, 2);
v___x_3695_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3696_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3697_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3696_, v_env_3694_, v___x_3695_);
v___x_3698_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3699_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3697_, v___x_3698_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___x_3697_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3730_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3730_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3730_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v_fst_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3728_; 
v_fst_3704_ = lean_ctor_get(v_a_3700_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_a_3700_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; 
v_unused_3729_ = lean_ctor_get(v_a_3700_, 1);
lean_dec(v_unused_3729_);
v___x_3706_ = v_a_3700_;
v_isShared_3707_ = v_isSharedCheck_3728_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_fst_3704_);
lean_dec(v_a_3700_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3728_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
if (lean_obj_tag(v_fst_3704_) == 0)
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3711_; 
lean_del_object(v___x_3702_);
v___x_3708_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3709_ = l_Lean_MessageData_ofName(v___x_3695_);
lean_inc_ref(v___x_3709_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 7);
lean_ctor_set(v___x_3706_, 1, v___x_3709_);
lean_ctor_set(v___x_3706_, 0, v___x_3708_);
v___x_3711_ = v___x_3706_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v___x_3709_);
v___x_3711_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3712_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3715_ = l_Lean_indentD(v___x_3714_);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3713_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
lean_ctor_set(v___x_3719_, 1, v___x_3709_);
v___x_3720_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3721_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3722_;
}
}
else
{
lean_object* v_val_3724_; lean_object* v___x_3726_; 
lean_del_object(v___x_3706_);
lean_dec(v___x_3695_);
lean_dec(v_stx_2332_);
v_val_3724_ = lean_ctor_get(v_fst_3704_, 0);
lean_inc(v_val_3724_);
lean_dec_ref_known(v_fst_3704_, 1);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v_val_3724_);
v___x_3726_ = v___x_3702_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_val_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v___x_3695_);
lean_dec(v_stx_2332_);
v_a_3731_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3699_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3699_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; uint8_t v___x_3741_; 
v___x_3739_ = l_Lean_Syntax_getArg(v___x_3690_, v___x_3617_);
lean_dec(v___x_3690_);
v___x_3740_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3741_ = l_Lean_Syntax_isOfKind(v___x_3739_, v___x_3740_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; lean_object* v_env_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3742_ = lean_st_ref_get(v___y_3688_);
v_env_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc_ref(v_env_3743_);
lean_dec(v___x_3742_);
lean_inc_n(v_stx_2332_, 2);
v___x_3744_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3745_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3746_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3745_, v_env_3743_, v___x_3744_);
v___x_3747_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3748_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3746_, v___x_3747_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___x_3746_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3779_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3751_ = v___x_3748_;
v_isShared_3752_ = v_isSharedCheck_3779_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3748_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3779_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v_fst_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3777_; 
v_fst_3753_ = lean_ctor_get(v_a_3749_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_a_3749_);
if (v_isSharedCheck_3777_ == 0)
{
lean_object* v_unused_3778_; 
v_unused_3778_ = lean_ctor_get(v_a_3749_, 1);
lean_dec(v_unused_3778_);
v___x_3755_ = v_a_3749_;
v_isShared_3756_ = v_isSharedCheck_3777_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_fst_3753_);
lean_dec(v_a_3749_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3777_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
if (lean_obj_tag(v_fst_3753_) == 0)
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
lean_del_object(v___x_3751_);
v___x_3757_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3758_ = l_Lean_MessageData_ofName(v___x_3744_);
lean_inc_ref(v___x_3758_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set_tag(v___x_3755_, 7);
lean_ctor_set(v___x_3755_, 1, v___x_3758_);
lean_ctor_set(v___x_3755_, 0, v___x_3757_);
v___x_3760_ = v___x_3755_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3761_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3764_ = l_Lean_indentD(v___x_3763_);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3762_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3765_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
lean_ctor_set(v___x_3768_, 1, v___x_3758_);
v___x_3769_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3768_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3770_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3771_;
}
}
else
{
lean_object* v_val_3773_; lean_object* v___x_3775_; 
lean_del_object(v___x_3755_);
lean_dec(v___x_3744_);
lean_dec(v_stx_2332_);
v_val_3773_ = lean_ctor_get(v_fst_3753_, 0);
lean_inc(v_val_3773_);
lean_dec_ref_known(v_fst_3753_, 1);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 0, v_val_3773_);
v___x_3775_ = v___x_3751_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_val_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v___x_3744_);
lean_dec(v_stx_2332_);
v_a_3780_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3748_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3748_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
v___y_3619_ = v___y_3683_;
v___y_3620_ = v___y_3684_;
v___y_3621_ = v___y_3685_;
v___y_3622_ = v___y_3686_;
v___y_3623_ = v___y_3687_;
v___y_3624_ = v___y_3688_;
goto v___jp_3618_;
}
}
}
else
{
lean_dec(v___x_3690_);
v___y_3619_ = v___y_3683_;
v___y_3620_ = v___y_3684_;
v___y_3621_ = v___y_3685_;
v___y_3622_ = v___y_3686_;
v___y_3623_ = v___y_3687_;
v___y_3624_ = v___y_3688_;
goto v___jp_3618_;
}
}
}
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3886_ = lean_unsigned_to_nat(0u);
v___x_3887_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3886_);
v___x_3888_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_3887_);
v___x_3889_ = l_Lean_Syntax_isOfKind(v___x_3887_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3890_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_3887_);
v___x_3891_ = l_Lean_Syntax_isOfKind(v___x_3887_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; lean_object* v_env_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
lean_dec(v___x_3887_);
v___x_3892_ = lean_st_ref_get(v_a_2338_);
v_env_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc_ref(v_env_3893_);
lean_dec(v___x_3892_);
lean_inc_n(v_stx_2332_, 2);
v___x_3894_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3895_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3896_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3895_, v_env_3893_, v___x_3894_);
v___x_3897_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3898_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3896_, v___x_3897_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3896_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3929_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3929_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3929_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v_fst_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3927_; 
v_fst_3903_ = lean_ctor_get(v_a_3899_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_a_3899_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; 
v_unused_3928_ = lean_ctor_get(v_a_3899_, 1);
lean_dec(v_unused_3928_);
v___x_3905_ = v_a_3899_;
v_isShared_3906_ = v_isSharedCheck_3927_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_fst_3903_);
lean_dec(v_a_3899_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3927_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
if (lean_obj_tag(v_fst_3903_) == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3910_; 
lean_del_object(v___x_3901_);
v___x_3907_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3908_ = l_Lean_MessageData_ofName(v___x_3894_);
lean_inc_ref(v___x_3908_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set_tag(v___x_3905_, 7);
lean_ctor_set(v___x_3905_, 1, v___x_3908_);
lean_ctor_set(v___x_3905_, 0, v___x_3907_);
v___x_3910_ = v___x_3905_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3911_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3910_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3914_ = l_Lean_indentD(v___x_3913_);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3912_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3915_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
lean_ctor_set(v___x_3918_, 1, v___x_3908_);
v___x_3919_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3920_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3921_;
}
}
else
{
lean_object* v_val_3923_; lean_object* v___x_3925_; 
lean_del_object(v___x_3905_);
lean_dec(v___x_3894_);
lean_dec(v_stx_2332_);
v_val_3923_ = lean_ctor_get(v_fst_3903_, 0);
lean_inc(v_val_3923_);
lean_dec_ref_known(v_fst_3903_, 1);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v_val_3923_);
v___x_3925_ = v___x_3901_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_val_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec(v___x_3894_);
lean_dec(v_stx_2332_);
v_a_3930_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3898_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3898_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
else
{
lean_object* v___x_3938_; 
lean_dec(v_stx_2332_);
v___x_3938_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2569_, v___x_3887_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3938_;
}
}
else
{
lean_object* v___x_3939_; 
lean_dec(v_stx_2332_);
v___x_3939_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2569_, v___x_3887_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3939_;
}
}
}
else
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3940_ = lean_unsigned_to_nat(0u);
v___x_3941_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_3940_);
v___x_3942_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
lean_inc(v___x_3941_);
v___x_3943_ = l_Lean_Syntax_isOfKind(v___x_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
lean_inc(v___x_3941_);
v___x_3945_ = l_Lean_Syntax_isOfKind(v___x_3941_, v___x_3944_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3946_; lean_object* v_env_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
lean_dec(v___x_3941_);
v___x_3946_ = lean_st_ref_get(v_a_2338_);
v_env_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc_ref(v_env_3947_);
lean_dec(v___x_3946_);
lean_inc_n(v_stx_2332_, 2);
v___x_3948_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_3949_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3950_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3949_, v_env_3947_, v___x_3948_);
v___x_3951_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3952_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_3950_, v___x_3951_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3950_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3983_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3955_ = v___x_3952_;
v_isShared_3956_ = v_isSharedCheck_3983_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3952_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3983_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v_fst_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3981_; 
v_fst_3957_ = lean_ctor_get(v_a_3953_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v_a_3953_);
if (v_isSharedCheck_3981_ == 0)
{
lean_object* v_unused_3982_; 
v_unused_3982_ = lean_ctor_get(v_a_3953_, 1);
lean_dec(v_unused_3982_);
v___x_3959_ = v_a_3953_;
v_isShared_3960_ = v_isSharedCheck_3981_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_fst_3957_);
lean_dec(v_a_3953_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3981_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
if (lean_obj_tag(v_fst_3957_) == 0)
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3964_; 
lean_del_object(v___x_3955_);
v___x_3961_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3962_ = l_Lean_MessageData_ofName(v___x_3948_);
lean_inc_ref(v___x_3962_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set_tag(v___x_3959_, 7);
lean_ctor_set(v___x_3959_, 1, v___x_3962_);
lean_ctor_set(v___x_3959_, 0, v___x_3961_);
v___x_3964_ = v___x_3959_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3961_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v___x_3962_);
v___x_3964_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3965_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3964_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
v___x_3967_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_3968_ = l_Lean_indentD(v___x_3967_);
v___x_3969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3966_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3969_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v___x_3962_);
v___x_3973_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3974_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3975_;
}
}
else
{
lean_object* v_val_3977_; lean_object* v___x_3979_; 
lean_del_object(v___x_3959_);
lean_dec(v___x_3948_);
lean_dec(v_stx_2332_);
v_val_3977_ = lean_ctor_get(v_fst_3957_, 0);
lean_inc(v_val_3977_);
lean_dec_ref_known(v_fst_3957_, 1);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v_val_3977_);
v___x_3979_ = v___x_3955_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_val_3977_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v___x_3948_);
lean_dec(v_stx_2332_);
v_a_3984_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3952_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3952_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
else
{
lean_object* v___x_3992_; 
lean_dec(v_stx_2332_);
v___x_3992_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_3941_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3941_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_object* v_a_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v_a_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc(v_a_3993_);
lean_dec_ref_known(v___x_3992_, 1);
v___x_3994_ = lean_box(0);
v___x_3995_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3993_, v___x_3994_, v___x_3994_, v___x_3994_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_3995_;
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
v_a_3996_ = lean_ctor_get(v___x_3992_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3992_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3992_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3992_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
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
lean_object* v___x_4004_; 
lean_dec(v_stx_2332_);
v___x_4004_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_3941_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_3941_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v___x_4006_ = lean_box(0);
v___x_4007_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4005_, v___x_4006_, v___x_4006_, v___x_4006_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4007_;
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
v_a_4008_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_4004_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_4004_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; 
v___x_4016_ = lean_unsigned_to_nat(1u);
v___x_4017_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4016_);
v___x_4018_ = l_Lean_Syntax_isNone(v___x_4017_);
if (v___x_4018_ == 0)
{
uint8_t v___x_4019_; 
v___x_4019_ = l_Lean_Syntax_matchesNull(v___x_4017_, v___x_4016_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; lean_object* v_env_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4020_ = lean_st_ref_get(v_a_2338_);
v_env_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc_ref(v_env_4021_);
lean_dec(v___x_4020_);
lean_inc_n(v_stx_2332_, 2);
v___x_4022_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4023_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4024_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4023_, v_env_4021_, v___x_4022_);
v___x_4025_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4026_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4024_, v___x_4025_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4024_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4057_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4029_ = v___x_4026_;
v_isShared_4030_ = v_isSharedCheck_4057_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4026_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4057_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v_fst_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4055_; 
v_fst_4031_ = lean_ctor_get(v_a_4027_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_a_4027_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; 
v_unused_4056_ = lean_ctor_get(v_a_4027_, 1);
lean_dec(v_unused_4056_);
v___x_4033_ = v_a_4027_;
v_isShared_4034_ = v_isSharedCheck_4055_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_fst_4031_);
lean_dec(v_a_4027_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4055_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
if (lean_obj_tag(v_fst_4031_) == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4038_; 
lean_del_object(v___x_4029_);
v___x_4035_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4036_ = l_Lean_MessageData_ofName(v___x_4022_);
lean_inc_ref(v___x_4036_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set_tag(v___x_4033_, 7);
lean_ctor_set(v___x_4033_, 1, v___x_4036_);
lean_ctor_set(v___x_4033_, 0, v___x_4035_);
v___x_4038_ = v___x_4033_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4035_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v___x_4036_);
v___x_4038_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4039_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4038_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4042_ = l_Lean_indentD(v___x_4041_);
v___x_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4040_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
lean_ctor_set(v___x_4046_, 1, v___x_4036_);
v___x_4047_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4046_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
v___x_4049_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4048_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4049_;
}
}
else
{
lean_object* v_val_4051_; lean_object* v___x_4053_; 
lean_del_object(v___x_4033_);
lean_dec(v___x_4022_);
lean_dec(v_stx_2332_);
v_val_4051_ = lean_ctor_get(v_fst_4031_, 0);
lean_inc(v_val_4051_);
lean_dec_ref_known(v_fst_4031_, 1);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v_val_4051_);
v___x_4053_ = v___x_4029_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_val_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_dec(v___x_4022_);
lean_dec(v_stx_2332_);
v_a_4058_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4026_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4026_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
else
{
v___y_2587_ = v_a_2333_;
v___y_2588_ = v_a_2334_;
v___y_2589_ = v_a_2335_;
v___y_2590_ = v_a_2336_;
v___y_2591_ = v_a_2337_;
v___y_2592_ = v_a_2338_;
goto v___jp_2586_;
}
}
else
{
lean_dec(v___x_4017_);
v___y_2587_ = v_a_2333_;
v___y_2588_ = v_a_2334_;
v___y_2589_ = v_a_2335_;
v___y_2590_ = v_a_2336_;
v___y_2591_ = v_a_2337_;
v___y_2592_ = v_a_2338_;
goto v___jp_2586_;
}
}
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; 
v___x_4066_ = lean_unsigned_to_nat(1u);
v___x_4067_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4066_);
v___x_4068_ = l_Lean_Syntax_isNone(v___x_4067_);
if (v___x_4068_ == 0)
{
uint8_t v___x_4069_; 
v___x_4069_ = l_Lean_Syntax_matchesNull(v___x_4067_, v___x_4066_);
if (v___x_4069_ == 0)
{
lean_object* v___x_4070_; lean_object* v_env_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4070_ = lean_st_ref_get(v_a_2338_);
v_env_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc_ref(v_env_4071_);
lean_dec(v___x_4070_);
lean_inc_n(v_stx_2332_, 2);
v___x_4072_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4073_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4074_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4073_, v_env_4071_, v___x_4072_);
v___x_4075_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4076_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4074_, v___x_4075_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4074_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4107_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4107_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4107_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v_fst_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4105_; 
v_fst_4081_ = lean_ctor_get(v_a_4077_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_a_4077_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; 
v_unused_4106_ = lean_ctor_get(v_a_4077_, 1);
lean_dec(v_unused_4106_);
v___x_4083_ = v_a_4077_;
v_isShared_4084_ = v_isSharedCheck_4105_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_fst_4081_);
lean_dec(v_a_4077_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4105_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
if (lean_obj_tag(v_fst_4081_) == 0)
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
lean_del_object(v___x_4079_);
v___x_4085_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4086_ = l_Lean_MessageData_ofName(v___x_4072_);
lean_inc_ref(v___x_4086_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set_tag(v___x_4083_, 7);
lean_ctor_set(v___x_4083_, 1, v___x_4086_);
lean_ctor_set(v___x_4083_, 0, v___x_4085_);
v___x_4088_ = v___x_4083_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4085_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4089_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4092_ = l_Lean_indentD(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4090_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
v___x_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
lean_ctor_set(v___x_4096_, 1, v___x_4086_);
v___x_4097_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4096_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4098_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4099_;
}
}
else
{
lean_object* v_val_4101_; lean_object* v___x_4103_; 
lean_del_object(v___x_4083_);
lean_dec(v___x_4072_);
lean_dec(v_stx_2332_);
v_val_4101_ = lean_ctor_get(v_fst_4081_, 0);
lean_inc(v_val_4101_);
lean_dec_ref_known(v_fst_4081_, 1);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v_val_4101_);
v___x_4103_ = v___x_4079_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_val_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v___x_4072_);
lean_dec(v_stx_2332_);
v_a_4108_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4076_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4076_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
else
{
v___y_2386_ = v_a_2333_;
v___y_2387_ = v_a_2334_;
v___y_2388_ = v_a_2335_;
v___y_2389_ = v_a_2336_;
v___y_2390_ = v_a_2337_;
v___y_2391_ = v_a_2338_;
goto v___jp_2385_;
}
}
else
{
lean_dec(v___x_4067_);
v___y_2386_ = v_a_2333_;
v___y_2387_ = v_a_2334_;
v___y_2388_ = v_a_2335_;
v___y_2389_ = v_a_2336_;
v___y_2390_ = v_a_2337_;
v___y_2391_ = v_a_2338_;
goto v___jp_2385_;
}
}
v___jp_2586_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2593_ = lean_unsigned_to_nat(2u);
v___x_2594_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2593_);
v___x_2595_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2596_ = l_Lean_Syntax_isOfKind(v___x_2594_, v___x_2595_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v_env_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2597_ = lean_st_ref_get(v___y_2592_);
v_env_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc_ref(v_env_2598_);
lean_dec(v___x_2597_);
lean_inc_n(v_stx_2332_, 2);
v___x_2599_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2600_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2601_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2600_, v_env_2598_, v___x_2599_);
v___x_2602_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2603_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2601_, v___x_2602_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___x_2601_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2634_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2634_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2634_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_fst_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2632_; 
v_fst_2608_ = lean_ctor_get(v_a_2604_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2604_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v_a_2604_, 1);
lean_dec(v_unused_2633_);
v___x_2610_ = v_a_2604_;
v_isShared_2611_ = v_isSharedCheck_2632_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_fst_2608_);
lean_dec(v_a_2604_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2632_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
if (lean_obj_tag(v_fst_2608_) == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
lean_del_object(v___x_2606_);
v___x_2612_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2613_ = l_Lean_MessageData_ofName(v___x_2599_);
lean_inc_ref(v___x_2613_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set_tag(v___x_2610_, 7);
lean_ctor_set(v___x_2610_, 1, v___x_2613_);
lean_ctor_set(v___x_2610_, 0, v___x_2612_);
v___x_2615_ = v___x_2610_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2616_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_2619_ = l_Lean_indentD(v___x_2618_);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2617_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v___x_2613_);
v___x_2624_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2625_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
return v___x_2626_;
}
}
else
{
lean_object* v_val_2628_; lean_object* v___x_2630_; 
lean_del_object(v___x_2610_);
lean_dec(v___x_2599_);
lean_dec(v_stx_2332_);
v_val_2628_ = lean_ctor_get(v_fst_2608_, 0);
lean_inc(v_val_2628_);
lean_dec_ref_known(v_fst_2608_, 1);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v_val_2628_);
v___x_2630_ = v___x_2606_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_val_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v___x_2599_);
lean_dec(v_stx_2332_);
v_a_2635_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2603_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2603_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_unsigned_to_nat(3u);
v___x_2644_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2643_);
lean_dec(v_stx_2332_);
v___x_2645_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2585_, v___x_2644_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
return v___x_2645_;
}
}
}
else
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; uint8_t v___x_4119_; 
v___x_4116_ = lean_unsigned_to_nat(0u);
v___x_4117_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4116_);
v___x_4118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4119_ = l_Lean_Syntax_isOfKind(v___x_4117_, v___x_4118_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4120_; lean_object* v_env_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4120_ = lean_st_ref_get(v_a_2338_);
v_env_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc_ref(v_env_4121_);
lean_dec(v___x_4120_);
lean_inc_n(v_stx_2332_, 2);
v___x_4122_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4123_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4124_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4123_, v_env_4121_, v___x_4122_);
v___x_4125_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4126_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4124_, v___x_4125_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4124_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4157_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4129_ = v___x_4126_;
v_isShared_4130_ = v_isSharedCheck_4157_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4157_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v_fst_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4155_; 
v_fst_4131_ = lean_ctor_get(v_a_4127_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_a_4127_);
if (v_isSharedCheck_4155_ == 0)
{
lean_object* v_unused_4156_; 
v_unused_4156_ = lean_ctor_get(v_a_4127_, 1);
lean_dec(v_unused_4156_);
v___x_4133_ = v_a_4127_;
v_isShared_4134_ = v_isSharedCheck_4155_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_fst_4131_);
lean_dec(v_a_4127_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4155_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
if (lean_obj_tag(v_fst_4131_) == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
lean_del_object(v___x_4129_);
v___x_4135_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4136_ = l_Lean_MessageData_ofName(v___x_4122_);
lean_inc_ref(v___x_4136_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set_tag(v___x_4133_, 7);
lean_ctor_set(v___x_4133_, 1, v___x_4136_);
lean_ctor_set(v___x_4133_, 0, v___x_4135_);
v___x_4138_ = v___x_4133_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v___x_4135_);
lean_ctor_set(v_reuseFailAlloc_4150_, 1, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4139_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4142_ = l_Lean_indentD(v___x_4141_);
v___x_4143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4140_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
v___x_4144_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4143_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
lean_ctor_set(v___x_4146_, 1, v___x_4136_);
v___x_4147_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4146_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4148_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4149_;
}
}
else
{
lean_object* v_val_4151_; lean_object* v___x_4153_; 
lean_del_object(v___x_4133_);
lean_dec(v___x_4122_);
lean_dec(v_stx_2332_);
v_val_4151_ = lean_ctor_get(v_fst_4131_, 0);
lean_inc(v_val_4151_);
lean_dec_ref_known(v_fst_4131_, 1);
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 0, v_val_4151_);
v___x_4153_ = v___x_4129_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_val_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec(v___x_4122_);
lean_dec(v_stx_2332_);
v_a_4158_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4126_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4126_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
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
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
v___x_4166_ = lean_unsigned_to_nat(1u);
v___x_4167_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4166_);
v___x_4168_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84));
lean_inc(v___x_4167_);
v___x_4169_ = l_Lean_Syntax_isOfKind(v___x_4167_, v___x_4168_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; lean_object* v_env_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_dec(v___x_4167_);
v___x_4170_ = lean_st_ref_get(v_a_2338_);
v_env_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc_ref(v_env_4171_);
lean_dec(v___x_4170_);
lean_inc_n(v_stx_2332_, 2);
v___x_4172_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4173_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4174_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4173_, v_env_4171_, v___x_4172_);
v___x_4175_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4176_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4174_, v___x_4175_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4174_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4207_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4179_ = v___x_4176_;
v_isShared_4180_ = v_isSharedCheck_4207_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4176_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4207_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v_fst_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4205_; 
v_fst_4181_ = lean_ctor_get(v_a_4177_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v_a_4177_);
if (v_isSharedCheck_4205_ == 0)
{
lean_object* v_unused_4206_; 
v_unused_4206_ = lean_ctor_get(v_a_4177_, 1);
lean_dec(v_unused_4206_);
v___x_4183_ = v_a_4177_;
v_isShared_4184_ = v_isSharedCheck_4205_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_fst_4181_);
lean_dec(v_a_4177_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4205_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
if (lean_obj_tag(v_fst_4181_) == 0)
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4188_; 
lean_del_object(v___x_4179_);
v___x_4185_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4186_ = l_Lean_MessageData_ofName(v___x_4172_);
lean_inc_ref(v___x_4186_);
if (v_isShared_4184_ == 0)
{
lean_ctor_set_tag(v___x_4183_, 7);
lean_ctor_set(v___x_4183_, 1, v___x_4186_);
lean_ctor_set(v___x_4183_, 0, v___x_4185_);
v___x_4188_ = v___x_4183_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4185_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v___x_4186_);
v___x_4188_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4189_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4188_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
v___x_4191_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4192_ = l_Lean_indentD(v___x_4191_);
v___x_4193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4190_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4193_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
lean_ctor_set(v___x_4196_, 1, v___x_4186_);
v___x_4197_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4196_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4198_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4199_;
}
}
else
{
lean_object* v_val_4201_; lean_object* v___x_4203_; 
lean_del_object(v___x_4183_);
lean_dec(v___x_4172_);
lean_dec(v_stx_2332_);
v_val_4201_ = lean_ctor_get(v_fst_4181_, 0);
lean_inc(v_val_4201_);
lean_dec_ref_known(v_fst_4181_, 1);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 0, v_val_4201_);
v___x_4203_ = v___x_4179_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_val_4201_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec(v___x_4172_);
lean_dec(v_stx_2332_);
v_a_4208_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4176_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4176_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
else
{
lean_object* v___x_4216_; uint8_t v___x_4217_; 
v___x_4216_ = l_Lean_Syntax_getArg(v___x_4167_, v___x_4116_);
lean_dec(v___x_4167_);
lean_inc(v___x_4216_);
v___x_4217_ = l_Lean_Syntax_matchesNull(v___x_4216_, v___x_4166_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4218_; lean_object* v_env_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
lean_dec(v___x_4216_);
v___x_4218_ = lean_st_ref_get(v_a_2338_);
v_env_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc_ref(v_env_4219_);
lean_dec(v___x_4218_);
lean_inc_n(v_stx_2332_, 2);
v___x_4220_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4221_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4222_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4221_, v_env_4219_, v___x_4220_);
v___x_4223_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4224_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4222_, v___x_4223_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4222_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4255_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4255_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4255_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v_fst_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4253_; 
v_fst_4229_ = lean_ctor_get(v_a_4225_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_a_4225_);
if (v_isSharedCheck_4253_ == 0)
{
lean_object* v_unused_4254_; 
v_unused_4254_ = lean_ctor_get(v_a_4225_, 1);
lean_dec(v_unused_4254_);
v___x_4231_ = v_a_4225_;
v_isShared_4232_ = v_isSharedCheck_4253_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_fst_4229_);
lean_dec(v_a_4225_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4253_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
if (lean_obj_tag(v_fst_4229_) == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4236_; 
lean_del_object(v___x_4227_);
v___x_4233_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4234_ = l_Lean_MessageData_ofName(v___x_4220_);
lean_inc_ref(v___x_4234_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set_tag(v___x_4231_, 7);
lean_ctor_set(v___x_4231_, 1, v___x_4234_);
lean_ctor_set(v___x_4231_, 0, v___x_4233_);
v___x_4236_ = v___x_4231_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4233_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4237_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4236_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
v___x_4239_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4240_ = l_Lean_indentD(v___x_4239_);
v___x_4241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4238_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
v___x_4242_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4241_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4243_);
lean_ctor_set(v___x_4244_, 1, v___x_4234_);
v___x_4245_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4244_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4246_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4247_;
}
}
else
{
lean_object* v_val_4249_; lean_object* v___x_4251_; 
lean_del_object(v___x_4231_);
lean_dec(v___x_4220_);
lean_dec(v_stx_2332_);
v_val_4249_ = lean_ctor_get(v_fst_4229_, 0);
lean_inc(v_val_4249_);
lean_dec_ref_known(v_fst_4229_, 1);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v_val_4249_);
v___x_4251_ = v___x_4227_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_val_4249_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v___x_4220_);
lean_dec(v_stx_2332_);
v_a_4256_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4224_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4224_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
lean_object* v___x_4264_; lean_object* v___x_4265_; uint8_t v___x_4266_; 
v___x_4264_ = l_Lean_Syntax_getArg(v___x_4216_, v___x_4116_);
lean_dec(v___x_4216_);
v___x_4265_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86));
v___x_4266_ = l_Lean_Syntax_isOfKind(v___x_4264_, v___x_4265_);
if (v___x_4266_ == 0)
{
lean_object* v___x_4267_; lean_object* v_env_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4267_ = lean_st_ref_get(v_a_2338_);
v_env_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc_ref(v_env_4268_);
lean_dec(v___x_4267_);
lean_inc_n(v_stx_2332_, 2);
v___x_4269_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4270_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4271_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4270_, v_env_4268_, v___x_4269_);
v___x_4272_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4273_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4271_, v___x_4272_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4271_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4304_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4276_ = v___x_4273_;
v_isShared_4277_ = v_isSharedCheck_4304_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4273_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4304_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v_fst_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4302_; 
v_fst_4278_ = lean_ctor_get(v_a_4274_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_a_4274_);
if (v_isSharedCheck_4302_ == 0)
{
lean_object* v_unused_4303_; 
v_unused_4303_ = lean_ctor_get(v_a_4274_, 1);
lean_dec(v_unused_4303_);
v___x_4280_ = v_a_4274_;
v_isShared_4281_ = v_isSharedCheck_4302_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_fst_4278_);
lean_dec(v_a_4274_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4302_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
if (lean_obj_tag(v_fst_4278_) == 0)
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4285_; 
lean_del_object(v___x_4276_);
v___x_4282_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4283_ = l_Lean_MessageData_ofName(v___x_4269_);
lean_inc_ref(v___x_4283_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set_tag(v___x_4280_, 7);
lean_ctor_set(v___x_4280_, 1, v___x_4283_);
lean_ctor_set(v___x_4280_, 0, v___x_4282_);
v___x_4285_ = v___x_4280_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4282_);
lean_ctor_set(v_reuseFailAlloc_4297_, 1, v___x_4283_);
v___x_4285_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4286_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4285_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___x_4288_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4289_ = l_Lean_indentD(v___x_4288_);
v___x_4290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4287_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
v___x_4291_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4290_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___x_4293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4292_);
lean_ctor_set(v___x_4293_, 1, v___x_4283_);
v___x_4294_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4293_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4295_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4296_;
}
}
else
{
lean_object* v_val_4298_; lean_object* v___x_4300_; 
lean_del_object(v___x_4280_);
lean_dec(v___x_4269_);
lean_dec(v_stx_2332_);
v_val_4298_ = lean_ctor_get(v_fst_4278_, 0);
lean_inc(v_val_4298_);
lean_dec_ref_known(v_fst_4278_, 1);
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 0, v_val_4298_);
v___x_4300_ = v___x_4276_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_val_4298_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec(v___x_4269_);
lean_dec(v_stx_2332_);
v_a_4305_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4273_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4273_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
lean_dec(v_stx_2332_);
v___x_4313_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
return v___x_4314_;
}
}
}
}
}
}
else
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4315_ = lean_unsigned_to_nat(1u);
v___x_4316_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4315_);
v___x_4317_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4318_ = l_Lean_Syntax_isOfKind(v___x_4316_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; lean_object* v_env_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4319_ = lean_st_ref_get(v_a_2338_);
v_env_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc_ref(v_env_4320_);
lean_dec(v___x_4319_);
lean_inc_n(v_stx_2332_, 2);
v___x_4321_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4322_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4323_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4322_, v_env_4320_, v___x_4321_);
v___x_4324_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4325_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4323_, v___x_4324_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4323_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4356_; 
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4328_ = v___x_4325_;
v_isShared_4329_ = v_isSharedCheck_4356_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4325_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4356_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v_fst_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4354_; 
v_fst_4330_ = lean_ctor_get(v_a_4326_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v_a_4326_);
if (v_isSharedCheck_4354_ == 0)
{
lean_object* v_unused_4355_; 
v_unused_4355_ = lean_ctor_get(v_a_4326_, 1);
lean_dec(v_unused_4355_);
v___x_4332_ = v_a_4326_;
v_isShared_4333_ = v_isSharedCheck_4354_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_fst_4330_);
lean_dec(v_a_4326_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4354_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
if (lean_obj_tag(v_fst_4330_) == 0)
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4337_; 
lean_del_object(v___x_4328_);
v___x_4334_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4335_ = l_Lean_MessageData_ofName(v___x_4321_);
lean_inc_ref(v___x_4335_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set_tag(v___x_4332_, 7);
lean_ctor_set(v___x_4332_, 1, v___x_4335_);
lean_ctor_set(v___x_4332_, 0, v___x_4334_);
v___x_4337_ = v___x_4332_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4334_);
lean_ctor_set(v_reuseFailAlloc_4349_, 1, v___x_4335_);
v___x_4337_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4338_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4337_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
v___x_4340_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4341_ = l_Lean_indentD(v___x_4340_);
v___x_4342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4339_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
v___x_4343_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4342_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
v___x_4345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
lean_ctor_set(v___x_4345_, 1, v___x_4335_);
v___x_4346_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4345_);
lean_ctor_set(v___x_4347_, 1, v___x_4346_);
v___x_4348_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4347_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4348_;
}
}
else
{
lean_object* v_val_4350_; lean_object* v___x_4352_; 
lean_del_object(v___x_4332_);
lean_dec(v___x_4321_);
lean_dec(v_stx_2332_);
v_val_4350_ = lean_ctor_get(v_fst_4330_, 0);
lean_inc(v_val_4350_);
lean_dec_ref_known(v_fst_4330_, 1);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v_val_4350_);
v___x_4352_ = v___x_4328_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_val_4350_);
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
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v___x_4321_);
lean_dec(v_stx_2332_);
v_a_4357_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4325_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4325_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
else
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; 
v___x_4365_ = lean_unsigned_to_nat(2u);
v___x_4366_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4365_);
v___x_4367_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4368_ = l_Lean_Syntax_isOfKind(v___x_4366_, v___x_4367_);
if (v___x_4368_ == 0)
{
lean_object* v___x_4369_; lean_object* v_env_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4369_ = lean_st_ref_get(v_a_2338_);
v_env_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc_ref(v_env_4370_);
lean_dec(v___x_4369_);
lean_inc_n(v_stx_2332_, 2);
v___x_4371_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4372_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4373_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4372_, v_env_4370_, v___x_4371_);
v___x_4374_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4375_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4373_, v___x_4374_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4373_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4406_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4406_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4406_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v_fst_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4404_; 
v_fst_4380_ = lean_ctor_get(v_a_4376_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_a_4376_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; 
v_unused_4405_ = lean_ctor_get(v_a_4376_, 1);
lean_dec(v_unused_4405_);
v___x_4382_ = v_a_4376_;
v_isShared_4383_ = v_isSharedCheck_4404_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_fst_4380_);
lean_dec(v_a_4376_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4404_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
if (lean_obj_tag(v_fst_4380_) == 0)
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4387_; 
lean_del_object(v___x_4378_);
v___x_4384_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4385_ = l_Lean_MessageData_ofName(v___x_4371_);
lean_inc_ref(v___x_4385_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set_tag(v___x_4382_, 7);
lean_ctor_set(v___x_4382_, 1, v___x_4385_);
lean_ctor_set(v___x_4382_, 0, v___x_4384_);
v___x_4387_ = v___x_4382_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4384_);
lean_ctor_set(v_reuseFailAlloc_4399_, 1, v___x_4385_);
v___x_4387_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4388_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4391_ = l_Lean_indentD(v___x_4390_);
v___x_4392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4389_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4392_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
lean_ctor_set(v___x_4395_, 1, v___x_4385_);
v___x_4396_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4395_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
v___x_4398_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4397_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4398_;
}
}
else
{
lean_object* v_val_4400_; lean_object* v___x_4402_; 
lean_del_object(v___x_4382_);
lean_dec(v___x_4371_);
lean_dec(v_stx_2332_);
v_val_4400_ = lean_ctor_get(v_fst_4380_, 0);
lean_inc(v_val_4400_);
lean_dec_ref_known(v_fst_4380_, 1);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v_val_4400_);
v___x_4402_ = v___x_4378_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_val_4400_);
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
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v___x_4371_);
lean_dec(v_stx_2332_);
v_a_4407_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4375_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4375_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
else
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
lean_dec(v_stx_2332_);
v___x_4415_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
return v___x_4416_;
}
}
}
}
else
{
lean_object* v___x_4417_; lean_object* v___x_4418_; uint8_t v___x_4419_; 
v___x_4417_ = lean_unsigned_to_nat(1u);
v___x_4418_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4417_);
v___x_4419_ = l_Lean_Syntax_isNone(v___x_4418_);
if (v___x_4419_ == 0)
{
uint8_t v___x_4420_; 
v___x_4420_ = l_Lean_Syntax_matchesNull(v___x_4418_, v___x_4417_);
if (v___x_4420_ == 0)
{
lean_object* v___x_4421_; lean_object* v_env_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
lean_del_object(v___x_2369_);
v___x_4421_ = lean_st_ref_get(v_a_2338_);
v_env_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc_ref(v_env_4422_);
lean_dec(v___x_4421_);
lean_inc_n(v_stx_2332_, 2);
v___x_4423_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4424_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4425_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4424_, v_env_4422_, v___x_4423_);
v___x_4426_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4427_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4425_, v___x_4426_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4425_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4458_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4430_ = v___x_4427_;
v_isShared_4431_ = v_isSharedCheck_4458_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4427_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4458_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v_fst_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4456_; 
v_fst_4432_ = lean_ctor_get(v_a_4428_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_a_4428_);
if (v_isSharedCheck_4456_ == 0)
{
lean_object* v_unused_4457_; 
v_unused_4457_ = lean_ctor_get(v_a_4428_, 1);
lean_dec(v_unused_4457_);
v___x_4434_ = v_a_4428_;
v_isShared_4435_ = v_isSharedCheck_4456_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_fst_4432_);
lean_dec(v_a_4428_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4456_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
if (lean_obj_tag(v_fst_4432_) == 0)
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4439_; 
lean_del_object(v___x_4430_);
v___x_4436_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4437_ = l_Lean_MessageData_ofName(v___x_4423_);
lean_inc_ref(v___x_4437_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set_tag(v___x_4434_, 7);
lean_ctor_set(v___x_4434_, 1, v___x_4437_);
lean_ctor_set(v___x_4434_, 0, v___x_4436_);
v___x_4439_ = v___x_4434_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4436_);
lean_ctor_set(v_reuseFailAlloc_4451_, 1, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4440_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4439_);
lean_ctor_set(v___x_4441_, 1, v___x_4440_);
v___x_4442_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4443_ = l_Lean_indentD(v___x_4442_);
v___x_4444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4441_);
lean_ctor_set(v___x_4444_, 1, v___x_4443_);
v___x_4445_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4444_);
lean_ctor_set(v___x_4446_, 1, v___x_4445_);
v___x_4447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4446_);
lean_ctor_set(v___x_4447_, 1, v___x_4437_);
v___x_4448_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4447_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
v___x_4450_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4449_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4450_;
}
}
else
{
lean_object* v_val_4452_; lean_object* v___x_4454_; 
lean_del_object(v___x_4434_);
lean_dec(v___x_4423_);
lean_dec(v_stx_2332_);
v_val_4452_ = lean_ctor_get(v_fst_4432_, 0);
lean_inc(v_val_4452_);
lean_dec_ref_known(v_fst_4432_, 1);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 0, v_val_4452_);
v___x_4454_ = v___x_4430_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_val_4452_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_dec(v___x_4423_);
lean_dec(v_stx_2332_);
v_a_4459_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4427_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4427_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
else
{
v___y_2457_ = v_a_2333_;
v___y_2458_ = v_a_2334_;
v___y_2459_ = v_a_2335_;
v___y_2460_ = v_a_2336_;
v___y_2461_ = v_a_2337_;
v___y_2462_ = v_a_2338_;
goto v___jp_2456_;
}
}
else
{
lean_dec(v___x_4418_);
v___y_2457_ = v_a_2333_;
v___y_2458_ = v_a_2334_;
v___y_2459_ = v_a_2335_;
v___y_2460_ = v_a_2336_;
v___y_2461_ = v_a_2337_;
v___y_2462_ = v_a_2338_;
goto v___jp_2456_;
}
}
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_del_object(v___x_2369_);
v___x_4467_ = lean_unsigned_to_nat(1u);
v___x_4468_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4467_);
lean_dec(v_stx_2332_);
v___x_4469_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4468_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4469_;
}
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_del_object(v___x_2369_);
v___x_4470_ = lean_unsigned_to_nat(0u);
v___x_4471_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4470_);
lean_dec(v_stx_2332_);
v___x_4472_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_4471_);
if (lean_obj_tag(v___x_4472_) == 1)
{
lean_object* v_val_4473_; lean_object* v_snd_4474_; lean_object* v_body_4475_; lean_object* v___x_4476_; 
v_val_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_val_4473_);
lean_dec_ref_known(v___x_4472_, 1);
v_snd_4474_ = lean_ctor_get(v_val_4473_, 1);
lean_inc(v_snd_4474_);
lean_dec(v_val_4473_);
v_body_4475_ = lean_ctor_get(v_snd_4474_, 1);
lean_inc(v_body_4475_);
lean_dec(v_snd_4474_);
v___x_4476_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_4475_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4497_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4479_ = v___x_4476_;
v_isShared_4480_ = v_isSharedCheck_4497_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4476_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4497_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
uint8_t v_breaks_4481_; uint8_t v_continues_4482_; uint8_t v_returnsEarly_4483_; lean_object* v_reassigns_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4495_; 
v_breaks_4481_ = lean_ctor_get_uint8(v_a_4477_, sizeof(void*)*2);
v_continues_4482_ = lean_ctor_get_uint8(v_a_4477_, sizeof(void*)*2 + 1);
v_returnsEarly_4483_ = lean_ctor_get_uint8(v_a_4477_, sizeof(void*)*2 + 2);
v_reassigns_4484_ = lean_ctor_get(v_a_4477_, 1);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_a_4477_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; 
v_unused_4496_ = lean_ctor_get(v_a_4477_, 0);
lean_dec(v_unused_4496_);
v___x_4486_ = v_a_4477_;
v_isShared_4487_ = v_isSharedCheck_4495_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_reassigns_4484_);
lean_dec(v_a_4477_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4495_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4488_; lean_object* v___x_4490_; 
v___x_4488_ = lean_unsigned_to_nat(1u);
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 0, v___x_4488_);
v___x_4490_ = v___x_4486_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4488_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v_reassigns_4484_);
lean_ctor_set_uint8(v_reuseFailAlloc_4494_, sizeof(void*)*2, v_breaks_4481_);
lean_ctor_set_uint8(v_reuseFailAlloc_4494_, sizeof(void*)*2 + 1, v_continues_4482_);
lean_ctor_set_uint8(v_reuseFailAlloc_4494_, sizeof(void*)*2 + 2, v_returnsEarly_4483_);
v___x_4490_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
lean_object* v___x_4492_; 
lean_ctor_set_uint8(v___x_4490_, sizeof(void*)*2 + 3, v___x_2573_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v___x_4490_);
v___x_4492_ = v___x_4479_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
}
else
{
return v___x_4476_;
}
}
else
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_dec(v___x_4472_);
v___x_4498_ = lean_unsigned_to_nat(1u);
v___x_4499_ = l_Lean_NameSet_empty;
v___x_4500_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4500_, 0, v___x_4498_);
lean_ctor_set(v___x_4500_, 1, v___x_4499_);
lean_ctor_set_uint8(v___x_4500_, sizeof(void*)*2, v___x_2573_);
lean_ctor_set_uint8(v___x_4500_, sizeof(void*)*2 + 1, v___x_2573_);
lean_ctor_set_uint8(v___x_4500_, sizeof(void*)*2 + 2, v___x_2573_);
lean_ctor_set_uint8(v___x_4500_, sizeof(void*)*2 + 3, v___x_2573_);
v___x_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
}
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4507_; lean_object* v___x_4508_; uint8_t v___x_4509_; 
lean_del_object(v___x_2369_);
v___x_4502_ = lean_unsigned_to_nat(0u);
v___x_4507_ = lean_unsigned_to_nat(1u);
v___x_4508_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_4507_);
v___x_4509_ = l_Lean_Syntax_isNone(v___x_4508_);
if (v___x_4509_ == 0)
{
uint8_t v___x_4510_; 
v___x_4510_ = l_Lean_Syntax_matchesNull(v___x_4508_, v___x_4507_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; lean_object* v_env_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4511_ = lean_st_ref_get(v_a_2338_);
v_env_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc_ref(v_env_4512_);
lean_dec(v___x_4511_);
lean_inc_n(v_stx_2332_, 2);
v___x_4513_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_4514_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4515_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4514_, v_env_4512_, v___x_4513_);
v___x_4516_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4517_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_4515_, v___x_4516_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v___x_4515_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4548_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4520_ = v___x_4517_;
v_isShared_4521_ = v_isSharedCheck_4548_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4517_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4548_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v_fst_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4546_; 
v_fst_4522_ = lean_ctor_get(v_a_4518_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v_a_4518_);
if (v_isSharedCheck_4546_ == 0)
{
lean_object* v_unused_4547_; 
v_unused_4547_ = lean_ctor_get(v_a_4518_, 1);
lean_dec(v_unused_4547_);
v___x_4524_ = v_a_4518_;
v_isShared_4525_ = v_isSharedCheck_4546_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_fst_4522_);
lean_dec(v_a_4518_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4546_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
if (lean_obj_tag(v_fst_4522_) == 0)
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4529_; 
lean_del_object(v___x_4520_);
v___x_4526_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4527_ = l_Lean_MessageData_ofName(v___x_4513_);
lean_inc_ref(v___x_4527_);
if (v_isShared_4525_ == 0)
{
lean_ctor_set_tag(v___x_4524_, 7);
lean_ctor_set(v___x_4524_, 1, v___x_4527_);
lean_ctor_set(v___x_4524_, 0, v___x_4526_);
v___x_4529_ = v___x_4524_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4526_);
lean_ctor_set(v_reuseFailAlloc_4541_, 1, v___x_4527_);
v___x_4529_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4530_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4529_);
lean_ctor_set(v___x_4531_, 1, v___x_4530_);
v___x_4532_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_4533_ = l_Lean_indentD(v___x_4532_);
v___x_4534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4531_);
lean_ctor_set(v___x_4534_, 1, v___x_4533_);
v___x_4535_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4534_);
lean_ctor_set(v___x_4536_, 1, v___x_4535_);
v___x_4537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
lean_ctor_set(v___x_4537_, 1, v___x_4527_);
v___x_4538_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4537_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
v___x_4540_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4539_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_4540_;
}
}
else
{
lean_object* v_val_4542_; lean_object* v___x_4544_; 
lean_del_object(v___x_4524_);
lean_dec(v___x_4513_);
lean_dec(v_stx_2332_);
v_val_4542_ = lean_ctor_get(v_fst_4522_, 0);
lean_inc(v_val_4542_);
lean_dec_ref_known(v_fst_4522_, 1);
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 0, v_val_4542_);
v___x_4544_ = v___x_4520_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_val_4542_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec(v___x_4513_);
lean_dec(v_stx_2332_);
v_a_4549_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4517_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4517_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
else
{
lean_dec(v_stx_2332_);
goto v___jp_4503_;
}
}
else
{
lean_dec(v___x_4508_);
lean_dec(v_stx_2332_);
goto v___jp_4503_;
}
v___jp_4503_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4504_ = l_Lean_NameSet_empty;
v___x_4505_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4505_, 0, v___x_4502_);
lean_ctor_set(v___x_4505_, 1, v___x_4504_);
lean_ctor_set_uint8(v___x_4505_, sizeof(void*)*2, v___x_2571_);
lean_ctor_set_uint8(v___x_4505_, sizeof(void*)*2 + 1, v___x_2571_);
lean_ctor_set_uint8(v___x_4505_, sizeof(void*)*2 + 2, v___x_2569_);
lean_ctor_set_uint8(v___x_4505_, sizeof(void*)*2 + 3, v___x_2569_);
v___x_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
return v___x_4506_;
}
}
}
else
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_del_object(v___x_2369_);
lean_dec(v_stx_2332_);
v___x_4557_ = lean_unsigned_to_nat(0u);
v___x_4558_ = l_Lean_NameSet_empty;
v___x_4559_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4559_, 0, v___x_4557_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
lean_ctor_set_uint8(v___x_4559_, sizeof(void*)*2, v___x_2568_);
lean_ctor_set_uint8(v___x_4559_, sizeof(void*)*2 + 1, v___x_2569_);
lean_ctor_set_uint8(v___x_4559_, sizeof(void*)*2 + 2, v___x_2568_);
lean_ctor_set_uint8(v___x_4559_, sizeof(void*)*2 + 3, v___x_2569_);
v___x_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
return v___x_4560_;
}
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
lean_del_object(v___x_2369_);
lean_dec(v_stx_2332_);
v___x_4561_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87);
v___x_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
return v___x_4562_;
}
v___jp_2385_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2392_ = lean_unsigned_to_nat(2u);
v___x_2393_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2392_);
v___x_2394_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2395_ = l_Lean_Syntax_isOfKind(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v_env_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2396_ = lean_st_ref_get(v___y_2391_);
v_env_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc_ref(v_env_2397_);
lean_dec(v___x_2396_);
lean_inc_n(v_stx_2332_, 2);
v___x_2398_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2399_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2400_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2399_, v_env_2397_, v___x_2398_);
v___x_2401_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2402_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2400_, v___x_2401_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___x_2400_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2433_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2433_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2433_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v_fst_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2431_; 
v_fst_2407_ = lean_ctor_get(v_a_2403_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_a_2403_);
if (v_isSharedCheck_2431_ == 0)
{
lean_object* v_unused_2432_; 
v_unused_2432_ = lean_ctor_get(v_a_2403_, 1);
lean_dec(v_unused_2432_);
v___x_2409_ = v_a_2403_;
v_isShared_2410_ = v_isSharedCheck_2431_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_fst_2407_);
lean_dec(v_a_2403_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2431_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
if (lean_obj_tag(v_fst_2407_) == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
lean_del_object(v___x_2405_);
v___x_2411_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2412_ = l_Lean_MessageData_ofName(v___x_2398_);
lean_inc_ref(v___x_2412_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set_tag(v___x_2409_, 7);
lean_ctor_set(v___x_2409_, 1, v___x_2412_);
lean_ctor_set(v___x_2409_, 0, v___x_2411_);
v___x_2414_ = v___x_2409_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2415_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_2418_ = l_Lean_indentD(v___x_2417_);
v___x_2419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2416_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
lean_ctor_set(v___x_2422_, 1, v___x_2412_);
v___x_2423_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2424_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2425_;
}
}
else
{
lean_object* v_val_2427_; lean_object* v___x_2429_; 
lean_del_object(v___x_2409_);
lean_dec(v___x_2398_);
lean_dec(v_stx_2332_);
v_val_2427_ = lean_ctor_get(v_fst_2407_, 0);
lean_inc(v_val_2427_);
lean_dec_ref_known(v_fst_2407_, 1);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v_val_2427_);
v___x_2429_ = v___x_2405_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_val_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v___x_2398_);
lean_dec(v_stx_2332_);
v_a_2434_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2402_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2402_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2442_ = lean_unsigned_to_nat(7u);
v___x_2443_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2442_);
v___x_2444_ = lean_unsigned_to_nat(8u);
v___x_2445_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2444_);
lean_dec(v_stx_2332_);
v___x_2446_ = l_Lean_Syntax_getOptional_x3f(v___x_2445_);
lean_dec(v___x_2445_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_box(0);
v___y_2341_ = v___x_2443_;
v___y_2342_ = v___y_2387_;
v___y_2343_ = v___y_2386_;
v___y_2344_ = v___y_2391_;
v___y_2345_ = v___y_2389_;
v___y_2346_ = v___y_2390_;
v___y_2347_ = v___y_2388_;
v___y_2348_ = v___x_2447_;
goto v___jp_2340_;
}
else
{
lean_object* v_val_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_val_2448_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2446_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_val_2448_);
lean_dec(v___x_2446_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_val_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
v___y_2341_ = v___x_2443_;
v___y_2342_ = v___y_2387_;
v___y_2343_ = v___y_2386_;
v___y_2344_ = v___y_2391_;
v___y_2345_ = v___y_2389_;
v___y_2346_ = v___y_2390_;
v___y_2347_ = v___y_2388_;
v___y_2348_ = v___x_2453_;
goto v___jp_2340_;
}
}
}
}
}
v___jp_2456_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2463_ = lean_unsigned_to_nat(2u);
v___x_2464_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2463_);
v___x_2465_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2466_ = l_Lean_Syntax_isOfKind(v___x_2464_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v_env_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_del_object(v___x_2369_);
v___x_2467_ = lean_st_ref_get(v___y_2462_);
v_env_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_ref(v_env_2468_);
lean_dec(v___x_2467_);
lean_inc_n(v_stx_2332_, 2);
v___x_2469_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2470_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2471_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2470_, v_env_2468_, v___x_2469_);
v___x_2472_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2473_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2471_, v___x_2472_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___x_2471_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2504_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2476_ = v___x_2473_;
v_isShared_2477_ = v_isSharedCheck_2504_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2504_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v_fst_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2502_; 
v_fst_2478_ = lean_ctor_get(v_a_2474_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_a_2474_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; 
v_unused_2503_ = lean_ctor_get(v_a_2474_, 1);
lean_dec(v_unused_2503_);
v___x_2480_ = v_a_2474_;
v_isShared_2481_ = v_isSharedCheck_2502_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_fst_2478_);
lean_dec(v_a_2474_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2502_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
if (lean_obj_tag(v_fst_2478_) == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
lean_del_object(v___x_2476_);
v___x_2482_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2483_ = l_Lean_MessageData_ofName(v___x_2469_);
lean_inc_ref(v___x_2483_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 7);
lean_ctor_set(v___x_2480_, 1, v___x_2483_);
lean_ctor_set(v___x_2480_, 0, v___x_2482_);
v___x_2485_ = v___x_2480_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2486_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_2489_ = l_Lean_indentD(v___x_2488_);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2487_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v___x_2483_);
v___x_2494_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2495_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
return v___x_2496_;
}
}
else
{
lean_object* v_val_2498_; lean_object* v___x_2500_; 
lean_del_object(v___x_2480_);
lean_dec(v___x_2469_);
lean_dec(v_stx_2332_);
v_val_2498_ = lean_ctor_get(v_fst_2478_, 0);
lean_inc(v_val_2498_);
lean_dec_ref_known(v_fst_2478_, 1);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v_val_2498_);
v___x_2500_ = v___x_2476_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_val_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v___x_2469_);
lean_dec(v_stx_2332_);
v_a_2505_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2473_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2473_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2513_ = lean_unsigned_to_nat(3u);
v___x_2514_ = l_Lean_Syntax_getArg(v_stx_2332_, v___x_2513_);
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2516_ = l_Lean_Syntax_isOfKind(v___x_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; lean_object* v_env_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_del_object(v___x_2369_);
v___x_2517_ = lean_st_ref_get(v___y_2462_);
v_env_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc_ref(v_env_2518_);
lean_dec(v___x_2517_);
lean_inc_n(v_stx_2332_, 2);
v___x_2519_ = l_Lean_Syntax_getKind(v_stx_2332_);
v___x_2520_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2521_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2520_, v_env_2518_, v___x_2519_);
v___x_2522_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2523_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2332_, v___x_2521_, v___x_2522_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
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
v___x_2532_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2533_ = l_Lean_MessageData_ofName(v___x_2519_);
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
v___x_2536_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = l_Lean_MessageData_ofSyntax(v_stx_2332_);
v___x_2539_ = l_Lean_indentD(v___x_2538_);
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2537_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v___x_2533_);
v___x_2544_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2545_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
return v___x_2546_;
}
}
else
{
lean_object* v_val_2548_; lean_object* v___x_2550_; 
lean_del_object(v___x_2530_);
lean_dec(v___x_2519_);
lean_dec(v_stx_2332_);
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
lean_dec(v___x_2519_);
lean_dec(v_stx_2332_);
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
lean_object* v___x_2563_; lean_object* v___x_2565_; 
lean_dec(v_stx_2332_);
v___x_2563_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2563_);
v___x_2565_ = v___x_2369_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec(v_stx_2332_);
v_a_4564_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_2366_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_2366_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
v___jp_2340_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2349_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___y_2341_);
v___x_2352_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2349_, v___x_2350_, v___x_2351_, v___y_2348_, v___y_2343_, v___y_2342_, v___y_2347_, v___y_2345_, v___y_2346_, v___y_2344_);
return v___x_2352_;
}
v___jp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2354_, v_bodyInfo_2355_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
v___jp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2359_, v_bodyInfo_2360_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4572_, size_t v_sz_4573_, size_t v_i_4574_, lean_object* v_b_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
uint8_t v___x_4583_; 
v___x_4583_ = lean_usize_dec_lt(v_i_4574_, v_sz_4573_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4584_; 
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v_b_4575_);
return v___x_4584_;
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4586_; 
v_a_4585_ = lean_array_uget_borrowed(v_as_4572_, v_i_4574_);
lean_inc(v_a_4585_);
v___x_4586_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4585_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v___x_4588_; size_t v___x_4589_; size_t v___x_4590_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref_known(v___x_4586_, 1);
v___x_4588_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_4575_, v_a_4587_);
v___x_4589_ = ((size_t)1ULL);
v___x_4590_ = lean_usize_add(v_i_4574_, v___x_4589_);
v_i_4574_ = v___x_4590_;
v_b_4575_ = v___x_4588_;
goto _start;
}
else
{
lean_dec_ref(v_b_4575_);
return v___x_4586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v_info_4600_; lean_object* v___x_4601_; size_t v_sz_4602_; size_t v___x_4603_; lean_object* v___x_4604_; 
v_info_4600_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_4601_ = l_Lean_Parser_Term_getDoElems(v_stx_4592_);
v_sz_4602_ = lean_array_size(v___x_4601_);
v___x_4603_ = ((size_t)0ULL);
v___x_4604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4601_, v_sz_4602_, v___x_4603_, v_info_4600_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
lean_dec_ref(v___x_4601_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4623_, lean_object* v_sz_4624_, lean_object* v_i_4625_, lean_object* v_b_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
size_t v_sz_boxed_4634_; size_t v_i_boxed_4635_; lean_object* v_res_4636_; 
v_sz_boxed_4634_ = lean_unbox_usize(v_sz_4624_);
lean_dec(v_sz_4624_);
v_i_boxed_4635_ = lean_unbox_usize(v_i_4625_);
lean_dec(v_i_4625_);
v_res_4636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4623_, v_sz_boxed_4634_, v_i_boxed_4635_, v_b_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec_ref(v_as_4623_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4637_, lean_object* v_sz_4638_, lean_object* v_i_4639_, lean_object* v_b_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
size_t v_sz_boxed_4648_; size_t v_i_boxed_4649_; lean_object* v_res_4650_; 
v_sz_boxed_4648_ = lean_unbox_usize(v_sz_4638_);
lean_dec(v_sz_4638_);
v_i_boxed_4649_ = lean_unbox_usize(v_i_4639_);
lean_dec(v_i_4639_);
v_res_4650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4637_, v_sz_boxed_4648_, v_i_boxed_4649_, v_b_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec_ref(v_as_4637_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_4651_, lean_object* v_rhs_x3f_4652_, lean_object* v_otherwise_x3f_4653_, lean_object* v_body_x3f_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_4651_, v_rhs_x3f_4652_, v_otherwise_x3f_4653_, v_body_x3f_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec_ref(v_a_4657_);
lean_dec(v_a_4656_);
lean_dec_ref(v_a_4655_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4663_, lean_object* v_as_4664_, lean_object* v_sz_4665_, lean_object* v_i_4666_, lean_object* v_b_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
uint8_t v___x_300807__boxed_4675_; size_t v_sz_boxed_4676_; size_t v_i_boxed_4677_; lean_object* v_res_4678_; 
v___x_300807__boxed_4675_ = lean_unbox(v___x_4663_);
v_sz_boxed_4676_ = lean_unbox_usize(v_sz_4665_);
lean_dec(v_sz_4665_);
v_i_boxed_4677_ = lean_unbox_usize(v_i_4666_);
lean_dec(v_i_4666_);
v_res_4678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_300807__boxed_4675_, v_as_4664_, v_sz_boxed_4676_, v_i_boxed_4677_, v_b_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec_ref(v_as_4664_);
return v_res_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4679_, lean_object* v_as_4680_, lean_object* v_sz_4681_, lean_object* v_i_4682_, lean_object* v_b_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
uint8_t v___x_300858__boxed_4691_; size_t v_sz_boxed_4692_; size_t v_i_boxed_4693_; lean_object* v_res_4694_; 
v___x_300858__boxed_4691_ = lean_unbox(v___x_4679_);
v_sz_boxed_4692_ = lean_unbox_usize(v_sz_4681_);
lean_dec(v_sz_4681_);
v_i_boxed_4693_ = lean_unbox_usize(v_i_4682_);
lean_dec(v_i_4682_);
v_res_4694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_300858__boxed_4691_, v_as_4680_, v_sz_boxed_4692_, v_i_boxed_4693_, v_b_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec_ref(v_as_4680_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_4695_, lean_object* v_sz_4696_, lean_object* v_i_4697_, lean_object* v_b_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
size_t v_sz_boxed_4706_; size_t v_i_boxed_4707_; lean_object* v_res_4708_; 
v_sz_boxed_4706_ = lean_unbox_usize(v_sz_4696_);
lean_dec(v_sz_4696_);
v_i_boxed_4707_ = lean_unbox_usize(v_i_4697_);
lean_dec(v_i_4697_);
v_res_4708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_4695_, v_sz_boxed_4706_, v_i_boxed_4707_, v_b_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec_ref(v_as_4695_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_4709_, lean_object* v_decl_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
uint8_t v_reassignment_boxed_4718_; lean_object* v_res_4719_; 
v_reassignment_boxed_4718_ = lean_unbox(v_reassignment_4709_);
v_res_4719_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_4718_, v_decl_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_);
lean_dec(v_a_4716_);
lean_dec_ref(v_a_4715_);
lean_dec(v_a_4714_);
lean_dec_ref(v_a_4713_);
lean_dec(v_a_4712_);
lean_dec_ref(v_a_4711_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
lean_dec(v_a_4724_);
lean_dec_ref(v_a_4723_);
lean_dec(v_a_4722_);
lean_dec_ref(v_a_4721_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* v_00_u03b1_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
lean_object* v___x_4737_; 
v___x_4737_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_00_u03b1_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_00_u03b1_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
lean_dec(v___y_4744_);
lean_dec_ref(v___y_4743_);
lean_dec(v___y_4742_);
lean_dec_ref(v___y_4741_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
return v_res_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_4747_, lean_object* v_ref_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_4748_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_4757_, lean_object* v_ref_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_4757_, v_ref_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_4767_, lean_object* v_x_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_4777_, lean_object* v_x_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_4777_, v_x_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_4787_, lean_object* v_as_4788_, lean_object* v_as_x27_4789_, lean_object* v_b_4790_, lean_object* v_a_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_4787_, v_as_x27_4789_, v_b_4790_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_4800_, lean_object* v_as_4801_, lean_object* v_as_x27_4802_, lean_object* v_b_4803_, lean_object* v_a_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_4800_, v_as_4801_, v_as_x27_4802_, v_b_4803_, v_a_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec(v_as_x27_4802_);
lean_dec(v_as_4801_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_4813_, lean_object* v_msg_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_4814_, v___y_4815_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_4823_, lean_object* v_msg_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_4823_, v_msg_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_4833_, lean_object* v_msg_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_4833_, v_msg_4834_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_4843_, lean_object* v_msg_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_4843_, v_msg_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_4853_, lean_object* v_as_x27_4854_, lean_object* v_b_4855_, lean_object* v_a_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v___x_4864_; 
v___x_4864_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_4854_, v_b_4855_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_4865_, lean_object* v_as_x27_4866_, lean_object* v_b_4867_, lean_object* v_a_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_4865_, v_as_x27_4866_, v_b_4867_, v_a_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
lean_dec(v_as_x27_4866_);
lean_dec(v_as_4865_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_4877_, lean_object* v_ref_4878_, lean_object* v_msg_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_4878_, v_msg_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_4888_, lean_object* v_ref_4889_, lean_object* v_msg_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v_res_4898_; 
v_res_4898_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_4888_, v_ref_4889_, v_msg_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4893_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec(v_ref_4889_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_4899_, lean_object* v_macroStack_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v___x_4908_; 
v___x_4908_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_4899_, v_macroStack_4900_, v___y_4905_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_4909_, lean_object* v_macroStack_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_4909_, v_macroStack_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
lean_dec(v___y_4916_);
lean_dec_ref(v___y_4915_);
lean_dec(v___y_4914_);
lean_dec_ref(v___y_4913_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_4919_, lean_object* v_m_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v___x_4922_; 
v___x_4922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_4920_, v_a_4921_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_4923_, lean_object* v_m_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_4923_, v_m_4924_, v_a_4925_);
lean_dec(v_a_4925_);
lean_dec_ref(v_m_4924_);
return v_res_4926_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_4927_, lean_object* v_x_4928_, lean_object* v_x_4929_){
_start:
{
uint8_t v___x_4930_; 
v___x_4930_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_4928_, v_x_4929_);
return v___x_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_4931_, lean_object* v_x_4932_, lean_object* v_x_4933_){
_start:
{
uint8_t v_res_4934_; lean_object* v_r_4935_; 
v_res_4934_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_4931_, v_x_4932_, v_x_4933_);
lean_dec_ref(v_x_4933_);
lean_dec_ref(v_x_4932_);
v_r_4935_ = lean_box(v_res_4934_);
return v_r_4935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_4936_, lean_object* v_a_4937_, lean_object* v_x_4938_){
_start:
{
lean_object* v___x_4939_; 
v___x_4939_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_4937_, v_x_4938_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_4940_, lean_object* v_a_4941_, lean_object* v_x_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_4940_, v_a_4941_, v_x_4942_);
lean_dec(v_x_4942_);
lean_dec(v_a_4941_);
return v_res_4943_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_4944_, lean_object* v_x_4945_, size_t v_x_4946_, lean_object* v_x_4947_){
_start:
{
uint8_t v___x_4948_; 
v___x_4948_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_4945_, v_x_4946_, v_x_4947_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4949_, lean_object* v_x_4950_, lean_object* v_x_4951_, lean_object* v_x_4952_){
_start:
{
size_t v_x_306864__boxed_4953_; uint8_t v_res_4954_; lean_object* v_r_4955_; 
v_x_306864__boxed_4953_ = lean_unbox_usize(v_x_4951_);
lean_dec(v_x_4951_);
v_res_4954_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_4949_, v_x_4950_, v_x_306864__boxed_4953_, v_x_4952_);
lean_dec_ref(v_x_4952_);
lean_dec_ref(v_x_4950_);
v_r_4955_ = lean_box(v_res_4954_);
return v_r_4955_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_4956_, lean_object* v_keys_4957_, lean_object* v_vals_4958_, lean_object* v_heq_4959_, lean_object* v_i_4960_, lean_object* v_k_4961_){
_start:
{
uint8_t v___x_4962_; 
v___x_4962_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_4957_, v_i_4960_, v_k_4961_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_4963_, lean_object* v_keys_4964_, lean_object* v_vals_4965_, lean_object* v_heq_4966_, lean_object* v_i_4967_, lean_object* v_k_4968_){
_start:
{
uint8_t v_res_4969_; lean_object* v_r_4970_; 
v_res_4969_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_4963_, v_keys_4964_, v_vals_4965_, v_heq_4966_, v_i_4967_, v_k_4968_);
lean_dec_ref(v_k_4968_);
lean_dec_ref(v_vals_4965_);
lean_dec_ref(v_keys_4964_);
v_r_4970_ = lean_box(v_res_4969_);
return v_r_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_){
_start:
{
lean_object* v___x_4979_; 
v___x_4979_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
lean_dec(v_a_4986_);
lean_dec_ref(v_a_4985_);
lean_dec(v_a_4984_);
lean_dec_ref(v_a_4983_);
lean_dec(v_a_4982_);
lean_dec_ref(v_a_4981_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_){
_start:
{
lean_object* v_res_5006_; 
v_res_5006_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_);
lean_dec(v_a_5004_);
lean_dec_ref(v_a_5003_);
lean_dec(v_a_5002_);
lean_dec_ref(v_a_5001_);
lean_dec(v_a_5000_);
lean_dec_ref(v_a_4999_);
return v_res_5006_;
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
