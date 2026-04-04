// Lean compiler output
// Module: Lean.Elab.Do.InferControlInfo
// Imports: public import Lean.Elab.Term meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_getLetPatDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getLetIdDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo;
static lean_once_cell_t l_Lean_Elab_Do_ControlInfo_pure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlInfo_pure___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_pure;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ", exitsRegularly: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = ",\n    reassigns: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofName, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ",\n    returnsEarly: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "breaks: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", continues: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22;
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
static const lean_string_object l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "controlInfoElemAttribute"};
static const lean_object* l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 110, 218, 82, 47, 2, 10, 58)}};
static const lean_object* l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
static const lean_string_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 249, .m_capacity = 249, .m_length = 246, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `TSyntax \\`doElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`.\n"};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(77) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(77) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1;
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80;
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
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = 0;
v___x_4_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4_, 0, v___x_2_);
lean_ctor_set(v___x_4_, 1, v___x_1_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 1, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 2, v___x_3_);
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
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; 
v___x_7_ = l_Lean_NameSet_empty;
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = 0;
v___x_10_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_10_, 0, v___x_8_);
lean_ctor_set(v___x_10_, 1, v___x_7_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*2, v___x_9_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*2 + 1, v___x_9_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*2 + 2, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object* v_a_12_, lean_object* v_b_13_){
_start:
{
uint8_t v_breaks_14_; uint8_t v_continues_15_; uint8_t v_returnsEarly_16_; lean_object* v_numRegularExits_17_; lean_object* v_reassigns_18_; uint8_t v___y_20_; uint8_t v___y_21_; uint8_t v___y_22_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_breaks_14_ = lean_ctor_get_uint8(v_a_12_, sizeof(void*)*2);
v_continues_15_ = lean_ctor_get_uint8(v_a_12_, sizeof(void*)*2 + 1);
v_returnsEarly_16_ = lean_ctor_get_uint8(v_a_12_, sizeof(void*)*2 + 2);
v_numRegularExits_17_ = lean_ctor_get(v_a_12_, 0);
v_reassigns_18_ = lean_ctor_get(v_a_12_, 1);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_nat_dec_eq(v_numRegularExits_17_, v___x_33_);
if (v___x_34_ == 0)
{
uint8_t v___x_35_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_41_; 
lean_inc(v_reassigns_18_);
lean_dec_ref(v_a_12_);
v___x_35_ = 1;
if (v_breaks_14_ == 0)
{
uint8_t v_breaks_43_; 
v_breaks_43_ = lean_ctor_get_uint8(v_b_13_, sizeof(void*)*2);
v___y_41_ = v_breaks_43_;
goto v___jp_40_;
}
else
{
v___y_41_ = v___x_35_;
goto v___jp_40_;
}
v___jp_36_:
{
if (v_returnsEarly_16_ == 0)
{
uint8_t v_returnsEarly_39_; 
v_returnsEarly_39_ = lean_ctor_get_uint8(v_b_13_, sizeof(void*)*2 + 2);
v___y_20_ = v___y_37_;
v___y_21_ = v___y_38_;
v___y_22_ = v_returnsEarly_39_;
goto v___jp_19_;
}
else
{
v___y_20_ = v___y_37_;
v___y_21_ = v___y_38_;
v___y_22_ = v___x_35_;
goto v___jp_19_;
}
}
v___jp_40_:
{
if (v_continues_15_ == 0)
{
uint8_t v_continues_42_; 
v_continues_42_ = lean_ctor_get_uint8(v_b_13_, sizeof(void*)*2 + 1);
v___y_37_ = v___y_41_;
v___y_38_ = v_continues_42_;
goto v___jp_36_;
}
else
{
v___y_37_ = v___y_41_;
v___y_38_ = v___x_35_;
goto v___jp_36_;
}
}
}
else
{
lean_dec_ref(v_b_13_);
return v_a_12_;
}
v___jp_19_:
{
lean_object* v_numRegularExits_23_; lean_object* v_reassigns_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_32_; 
v_numRegularExits_23_ = lean_ctor_get(v_b_13_, 0);
v_reassigns_24_ = lean_ctor_get(v_b_13_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_b_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_26_ = v_b_13_;
v_isShared_27_ = v_isSharedCheck_32_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_reassigns_24_);
lean_inc(v_numRegularExits_23_);
lean_dec(v_b_13_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_32_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_28_ = l_Lean_NameSet_append(v_reassigns_18_, v_reassigns_24_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_28_);
v___x_30_ = v___x_26_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_numRegularExits_23_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*2, v___y_20_);
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*2 + 1, v___y_21_);
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*2 + 2, v___y_22_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object* v_a_44_, lean_object* v_b_45_){
_start:
{
uint8_t v_breaks_46_; uint8_t v_continues_47_; uint8_t v_returnsEarly_48_; lean_object* v_numRegularExits_49_; lean_object* v_reassigns_50_; uint8_t v___y_52_; uint8_t v___y_53_; uint8_t v___y_54_; uint8_t v___y_67_; uint8_t v___y_68_; uint8_t v___y_71_; 
v_breaks_46_ = lean_ctor_get_uint8(v_a_44_, sizeof(void*)*2);
v_continues_47_ = lean_ctor_get_uint8(v_a_44_, sizeof(void*)*2 + 1);
v_returnsEarly_48_ = lean_ctor_get_uint8(v_a_44_, sizeof(void*)*2 + 2);
v_numRegularExits_49_ = lean_ctor_get(v_a_44_, 0);
lean_inc(v_numRegularExits_49_);
v_reassigns_50_ = lean_ctor_get(v_a_44_, 1);
lean_inc(v_reassigns_50_);
lean_dec_ref(v_a_44_);
if (v_breaks_46_ == 0)
{
uint8_t v_breaks_73_; 
v_breaks_73_ = lean_ctor_get_uint8(v_b_45_, sizeof(void*)*2);
v___y_71_ = v_breaks_73_;
goto v___jp_70_;
}
else
{
v___y_71_ = v_breaks_46_;
goto v___jp_70_;
}
v___jp_51_:
{
lean_object* v_numRegularExits_55_; lean_object* v_reassigns_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_65_; 
v_numRegularExits_55_ = lean_ctor_get(v_b_45_, 0);
v_reassigns_56_ = lean_ctor_get(v_b_45_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_b_45_);
if (v_isSharedCheck_65_ == 0)
{
v___x_58_ = v_b_45_;
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_reassigns_56_);
lean_inc(v_numRegularExits_55_);
lean_dec(v_b_45_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_60_ = lean_nat_add(v_numRegularExits_49_, v_numRegularExits_55_);
lean_dec(v_numRegularExits_55_);
lean_dec(v_numRegularExits_49_);
v___x_61_ = l_Lean_NameSet_append(v_reassigns_50_, v_reassigns_56_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_61_);
lean_ctor_set(v___x_58_, 0, v___x_60_);
v___x_63_ = v___x_58_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*2, v___y_52_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*2 + 1, v___y_53_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*2 + 2, v___y_54_);
return v___x_63_;
}
}
}
v___jp_66_:
{
if (v_returnsEarly_48_ == 0)
{
uint8_t v_returnsEarly_69_; 
v_returnsEarly_69_ = lean_ctor_get_uint8(v_b_45_, sizeof(void*)*2 + 2);
v___y_52_ = v___y_67_;
v___y_53_ = v___y_68_;
v___y_54_ = v_returnsEarly_69_;
goto v___jp_51_;
}
else
{
v___y_52_ = v___y_67_;
v___y_53_ = v___y_68_;
v___y_54_ = v_returnsEarly_48_;
goto v___jp_51_;
}
}
v___jp_70_:
{
if (v_continues_47_ == 0)
{
uint8_t v_continues_72_; 
v_continues_72_ = lean_ctor_get_uint8(v_b_45_, sizeof(void*)*2 + 1);
v___y_67_ = v___y_71_;
v___y_68_ = v_continues_72_;
goto v___jp_66_;
}
else
{
v___y_67_ = v___y_71_;
v___y_68_ = v_continues_47_;
goto v___jp_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object* v_x1_74_, lean_object* v_x2_75_, lean_object* v_x3_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v_x1_74_);
lean_ctor_set(v___x_77_, 1, v_x3_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0));
v___x_80_ = l_Lean_stringToMessageData(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2));
v___x_83_ = l_Lean_stringToMessageData(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15));
v___x_106_ = l_Lean_stringToMessageData(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19));
v___x_111_ = l_Lean_stringToMessageData(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21));
v___x_114_ = l_Lean_stringToMessageData(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object* v___f_115_, lean_object* v_info_116_){
_start:
{
uint8_t v_breaks_117_; uint8_t v_continues_118_; uint8_t v_returnsEarly_119_; lean_object* v_numRegularExits_120_; lean_object* v_reassigns_121_; lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___y_144_; lean_object* v___y_145_; lean_object* v___x_153_; lean_object* v___y_155_; 
v_breaks_117_ = lean_ctor_get_uint8(v_info_116_, sizeof(void*)*2);
v_continues_118_ = lean_ctor_get_uint8(v_info_116_, sizeof(void*)*2 + 1);
v_returnsEarly_119_ = lean_ctor_get_uint8(v_info_116_, sizeof(void*)*2 + 2);
v_numRegularExits_120_ = lean_ctor_get(v_info_116_, 0);
lean_inc(v_numRegularExits_120_);
v_reassigns_121_ = lean_ctor_get(v_info_116_, 1);
lean_inc(v_reassigns_121_);
lean_dec_ref(v_info_116_);
v___x_153_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20);
if (v_breaks_117_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_155_ = v___x_163_;
goto v___jp_154_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_155_ = v___x_164_;
goto v___jp_154_;
}
v___jp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_inc_ref(v___y_124_);
v___x_125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_125_, 0, v___y_124_);
v___x_126_ = l_Lean_MessageData_ofFormat(v___x_125_);
v___x_127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_127_, 0, v___y_123_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1);
v___x_129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_Nat_reprFast(v_numRegularExits_120_);
v___x_131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
v___x_132_ = l_Lean_MessageData_ofFormat(v___x_131_);
v___x_133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_129_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3);
v___x_135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_box(0);
v___x_137_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13));
v___x_138_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_137_, v___f_115_, v___x_136_, v_reassigns_121_);
v___x_139_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14));
v___x_140_ = l_List_mapTR_loop___redArg(v___x_139_, v___x_138_, v___x_136_);
v___x_141_ = l_Lean_MessageData_ofList(v___x_140_);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_135_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
return v___x_142_;
}
v___jp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_inc_ref(v___y_145_);
v___x_146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_146_, 0, v___y_145_);
v___x_147_ = l_Lean_MessageData_ofFormat(v___x_146_);
v___x_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_148_, 0, v___y_144_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16);
v___x_150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
if (v_returnsEarly_119_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_123_ = v___x_150_;
v___y_124_ = v___x_151_;
goto v___jp_122_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_123_ = v___x_150_;
v___y_124_ = v___x_152_;
goto v___jp_122_;
}
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
lean_inc_ref(v___y_155_);
v___x_156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_156_, 0, v___y_155_);
v___x_157_ = l_Lean_MessageData_ofFormat(v___x_156_);
v___x_158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_153_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22);
v___x_160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
if (v_continues_118_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_144_ = v___x_160_;
v___y_145_ = v___x_161_;
goto v___jp_143_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_144_ = v___x_160_;
v___y_145_ = v___x_162_;
goto v___jp_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object* v_ref_193_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_195_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1));
v___x_196_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3));
v___x_197_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8));
v___x_198_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12));
v___x_199_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13));
v___x_200_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_195_, v___x_196_, v___x_197_, v___x_198_, v___x_199_, v_ref_193_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object* v_ref_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v_ref_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_212_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1(){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = ((lean_object*)(l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_218_ = ((lean_object*)(l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0));
v___x_219_ = l_Lean_addBuiltinDocString(v___x_217_, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3(){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = ((lean_object*)(l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_249_ = ((lean_object*)(l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6));
v___x_250_ = l_Lean_addBuiltinDeclarationRanges(v___x_248_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object* v_msgData_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; lean_object* v_env_260_; lean_object* v___x_261_; lean_object* v_mctx_262_; lean_object* v_lctx_263_; lean_object* v_options_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_259_ = lean_st_ref_get(v___y_257_);
v_env_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_env_260_);
lean_dec(v___x_259_);
v___x_261_ = lean_st_ref_get(v___y_255_);
v_mctx_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc_ref(v_mctx_262_);
lean_dec(v___x_261_);
v_lctx_263_ = lean_ctor_get(v___y_254_, 2);
v_options_264_ = lean_ctor_get(v___y_256_, 2);
lean_inc_ref(v_options_264_);
lean_inc_ref(v_lctx_263_);
v___x_265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_265_, 0, v_env_260_);
lean_ctor_set(v___x_265_, 1, v_mctx_262_);
lean_ctor_set(v___x_265_, 2, v_lctx_263_);
lean_ctor_set(v___x_265_, 3, v_options_264_);
v___x_266_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_msgData_253_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
return v_res_274_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_box(1);
v___x_276_ = l_Lean_MessageData_ofFormat(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_281_ = l_Lean_MessageData_ofFormat(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
return v_x_282_;
}
else
{
lean_object* v_head_284_; lean_object* v_tail_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_307_; 
v_head_284_ = lean_ctor_get(v_x_283_, 0);
v_tail_285_ = lean_ctor_get(v_x_283_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_307_ == 0)
{
v___x_287_ = v_x_283_;
v_isShared_288_ = v_isSharedCheck_307_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_tail_285_);
lean_inc(v_head_284_);
lean_dec(v_x_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_307_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_before_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_305_; 
v_before_289_ = lean_ctor_get(v_head_284_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_head_284_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_head_284_, 1);
lean_dec(v_unused_306_);
v___x_291_ = v_head_284_;
v_isShared_292_ = v_isSharedCheck_305_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_before_289_);
lean_dec(v_head_284_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_305_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 7);
lean_ctor_set(v___x_291_, 1, v___x_293_);
lean_ctor_set(v___x_291_, 0, v_x_282_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_x_282_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_304_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 7);
lean_ctor_set(v___x_287_, 1, v___x_296_);
lean_ctor_set(v___x_287_, 0, v___x_295_);
v___x_298_ = v___x_287_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_303_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_MessageData_ofSyntax(v_before_289_);
v___x_300_ = l_Lean_indentD(v___x_299_);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_298_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v_x_282_ = v___x_301_;
v_x_283_ = v_tail_285_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_308_, lean_object* v_opt_309_){
_start:
{
lean_object* v_name_310_; lean_object* v_defValue_311_; lean_object* v_map_312_; lean_object* v___x_313_; 
v_name_310_ = lean_ctor_get(v_opt_309_, 0);
v_defValue_311_ = lean_ctor_get(v_opt_309_, 1);
v_map_312_ = lean_ctor_get(v_opts_308_, 0);
v___x_313_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_312_, v_name_310_);
if (lean_obj_tag(v___x_313_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = lean_unbox(v_defValue_311_);
return v___x_314_;
}
else
{
lean_object* v_val_315_; 
v_val_315_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_315_);
lean_dec_ref(v___x_313_);
if (lean_obj_tag(v_val_315_) == 1)
{
uint8_t v_v_316_; 
v_v_316_ = lean_ctor_get_uint8(v_val_315_, 0);
lean_dec_ref(v_val_315_);
return v_v_316_;
}
else
{
uint8_t v___x_317_; 
lean_dec(v_val_315_);
v___x_317_ = lean_unbox(v_defValue_311_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_318_, lean_object* v_opt_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_318_, v_opt_319_);
lean_dec_ref(v_opt_319_);
lean_dec_ref(v_opts_318_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_326_ = l_Lean_MessageData_ofFormat(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_327_, lean_object* v_macroStack_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_options_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_options_331_ = lean_ctor_get(v___y_329_, 2);
v___x_332_ = l_Lean_Elab_pp_macroStack;
v___x_333_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_options_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v_macroStack_328_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v_msgData_327_);
return v___x_334_;
}
else
{
if (lean_obj_tag(v_macroStack_328_) == 0)
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v_msgData_327_);
return v___x_335_;
}
else
{
lean_object* v_head_336_; lean_object* v_after_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_352_; 
v_head_336_ = lean_ctor_get(v_macroStack_328_, 0);
lean_inc(v_head_336_);
v_after_337_ = lean_ctor_get(v_head_336_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_head_336_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; 
v_unused_353_ = lean_ctor_get(v_head_336_, 0);
lean_dec(v_unused_353_);
v___x_339_ = v_head_336_;
v_isShared_340_ = v_isSharedCheck_352_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_after_337_);
lean_dec(v_head_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_352_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_340_ == 0)
{
lean_ctor_set_tag(v___x_339_, 7);
lean_ctor_set(v___x_339_, 1, v___x_341_);
lean_ctor_set(v___x_339_, 0, v_msgData_327_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_msgData_327_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_351_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_msgData_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_344_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_MessageData_ofSyntax(v_after_337_);
v___x_347_ = l_Lean_indentD(v___x_346_);
v_msgData_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_348_, 0, v___x_345_);
lean_ctor_set(v_msgData_348_, 1, v___x_347_);
v___x_349_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_348_, v_macroStack_328_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_354_, lean_object* v_macroStack_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_354_, v_macroStack_355_, v___y_356_);
lean_dec_ref(v___y_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_ref_367_; lean_object* v___x_368_; lean_object* v_a_369_; lean_object* v_macroStack_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v_ref_367_ = lean_ctor_get(v___y_364_, 5);
v___x_368_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_359_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v___x_368_);
v_macroStack_370_ = lean_ctor_get(v___y_360_, 1);
lean_inc_n(v_macroStack_370_, 2);
v___x_371_ = l_Lean_Elab_getBetterRef(v_ref_367_, v_macroStack_370_);
v___x_372_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_369_, v_macroStack_370_, v___y_364_);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_381_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_371_);
lean_ctor_set(v___x_377_, 1, v_a_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 1);
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_391_, size_t v_i_392_, size_t v_stop_393_, lean_object* v_b_394_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_eq(v_i_392_, v_stop_393_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; size_t v___x_398_; size_t v___x_399_; 
v___x_396_ = lean_array_uget_borrowed(v_as_391_, v_i_392_);
lean_inc(v___x_396_);
v___x_397_ = l_Lean_NameSet_insert(v_b_394_, v___x_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_392_, v___x_398_);
v_i_392_ = v___x_399_;
v_b_394_ = v___x_397_;
goto _start;
}
else
{
return v_b_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_401_, lean_object* v_i_402_, lean_object* v_stop_403_, lean_object* v_b_404_){
_start:
{
size_t v_i_boxed_405_; size_t v_stop_boxed_406_; lean_object* v_res_407_; 
v_i_boxed_405_ = lean_unbox_usize(v_i_402_);
lean_dec(v_i_402_);
v_stop_boxed_406_ = lean_unbox_usize(v_stop_403_);
lean_dec(v_stop_403_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_401_, v_i_boxed_405_, v_stop_boxed_406_, v_b_404_);
lean_dec_ref(v_as_401_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_408_, size_t v_i_409_, lean_object* v_bs_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_lt(v_i_409_, v_sz_408_);
if (v___x_411_ == 0)
{
return v_bs_410_;
}
else
{
lean_object* v_v_412_; lean_object* v___x_413_; lean_object* v_bs_x27_414_; lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; 
v_v_412_ = lean_array_uget(v_bs_410_, v_i_409_);
v___x_413_ = lean_unsigned_to_nat(0u);
v_bs_x27_414_ = lean_array_uset(v_bs_410_, v_i_409_, v___x_413_);
v___x_415_ = l_Lean_TSyntax_getId(v_v_412_);
lean_dec(v_v_412_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_add(v_i_409_, v___x_416_);
v___x_418_ = lean_array_uset(v_bs_x27_414_, v_i_409_, v___x_415_);
v_i_409_ = v___x_417_;
v_bs_410_ = v___x_418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_420_, lean_object* v_i_421_, lean_object* v_bs_422_){
_start:
{
size_t v_sz_boxed_423_; size_t v_i_boxed_424_; lean_object* v_res_425_; 
v_sz_boxed_423_ = lean_unbox_usize(v_sz_420_);
lean_dec(v_sz_420_);
v_i_boxed_424_ = lean_unbox_usize(v_i_421_);
lean_dec(v_i_421_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_423_, v_i_boxed_424_, v_bs_422_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_box(0);
v___x_427_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg(){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0);
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t v_sz_434_, size_t v_i_435_, lean_object* v_bs_436_){
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
lean_object* v___x_439_; lean_object* v_bs_x27_440_; lean_object* v___x_441_; size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v_bs_x27_440_ = lean_array_uset(v_bs_436_, v_i_435_, v___x_439_);
v___x_441_ = lean_box(0);
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_add(v_i_435_, v___x_442_);
v___x_444_ = lean_array_uset(v_bs_x27_440_, v_i_435_, v___x_441_);
v_i_435_ = v___x_443_;
v_bs_436_ = v___x_444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_sz_446_, lean_object* v_i_447_, lean_object* v_bs_448_){
_start:
{
size_t v_sz_boxed_449_; size_t v_i_boxed_450_; lean_object* v_res_451_; 
v_sz_boxed_449_ = lean_unbox_usize(v_sz_446_);
lean_dec(v_sz_446_);
v_i_boxed_450_ = lean_unbox_usize(v_i_447_);
lean_dec(v_i_447_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_boxed_449_, v_i_boxed_450_, v_bs_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_452_, uint8_t v___x_453_, lean_object* v_as_454_, size_t v_i_455_, size_t v_stop_456_, lean_object* v_b_457_){
_start:
{
lean_object* v___y_459_; uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_eq(v_i_455_, v_stop_456_);
if (v___x_463_ == 0)
{
lean_object* v_fst_464_; uint8_t v___x_465_; 
v_fst_464_ = lean_ctor_get(v_b_457_, 0);
v___x_465_ = lean_unbox(v_fst_464_);
if (v___x_465_ == 0)
{
lean_object* v_snd_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_snd_466_ = lean_ctor_get(v_b_457_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_b_457_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_b_457_, 0);
lean_dec(v_unused_475_);
v___x_468_ = v_b_457_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snd_466_);
lean_dec(v_b_457_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_box(v___x_452_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_snd_466_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
v___y_459_ = v___x_472_;
goto v___jp_458_;
}
}
}
else
{
lean_object* v_snd_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_486_; 
v_snd_476_ = lean_ctor_get(v_b_457_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_b_457_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_b_457_, 0);
lean_dec(v_unused_487_);
v___x_478_ = v_b_457_;
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_snd_476_);
lean_dec(v_b_457_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_480_ = lean_array_uget_borrowed(v_as_454_, v_i_455_);
lean_inc(v___x_480_);
v___x_481_ = lean_array_push(v_snd_476_, v___x_480_);
v___x_482_ = lean_box(v___x_453_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_481_);
lean_ctor_set(v___x_478_, 0, v___x_482_);
v___x_484_ = v___x_478_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_481_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
v___y_459_ = v___x_484_;
goto v___jp_458_;
}
}
}
}
else
{
return v_b_457_;
}
v___jp_458_:
{
size_t v___x_460_; size_t v___x_461_; 
v___x_460_ = ((size_t)1ULL);
v___x_461_ = lean_usize_add(v_i_455_, v___x_460_);
v_i_455_ = v___x_461_;
v_b_457_ = v___y_459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_488_, lean_object* v___x_489_, lean_object* v_as_490_, lean_object* v_i_491_, lean_object* v_stop_492_, lean_object* v_b_493_){
_start:
{
uint8_t v___x_284253__boxed_494_; uint8_t v___x_284254__boxed_495_; size_t v_i_boxed_496_; size_t v_stop_boxed_497_; lean_object* v_res_498_; 
v___x_284253__boxed_494_ = lean_unbox(v___x_488_);
v___x_284254__boxed_495_ = lean_unbox(v___x_489_);
v_i_boxed_496_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_stop_boxed_497_ = lean_unbox_usize(v_stop_492_);
lean_dec(v_stop_492_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_284253__boxed_494_, v___x_284254__boxed_495_, v_as_490_, v_i_boxed_496_, v_stop_boxed_497_, v_b_493_);
lean_dec_ref(v_as_490_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_499_, lean_object* v_declName_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v___x_503_; lean_object* v_env_504_; lean_object* v___x_505_; uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_503_ = 0;
v_env_504_ = l_Lean_Environment_setExporting(v_env_499_, v___x_503_);
lean_inc(v_declName_500_);
v___x_505_ = l_Lean_mkPrivateName(v_env_504_, v_declName_500_);
v___x_506_ = 1;
lean_inc_ref(v_env_504_);
v___x_507_ = l_Lean_Environment_contains(v_env_504_, v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_508_ = l_Lean_privateToUserName(v_declName_500_);
v___x_509_ = l_Lean_Environment_contains(v_env_504_, v___x_508_, v___x_506_);
v___x_510_ = lean_box(v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___y_502_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref(v_env_504_);
lean_dec(v_declName_500_);
v___x_512_ = lean_box(v___x_507_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___y_502_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_514_, lean_object* v_declName_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_514_, v_declName_515_, v___y_516_, v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_518_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = l_Lean_maxRecDepthErrorMessage;
v___x_525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_527_ = l_Lean_MessageData_ofFormat(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_529_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_530_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_531_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_ref_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_539_, lean_object* v___y_540_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
v_a_541_ = lean_ctor_get(v_x_539_, 0);
lean_inc(v_a_541_);
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v_a_541_);
lean_ctor_set(v___x_542_, 1, v___y_540_);
return v___x_542_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_544_; 
v_a_543_ = lean_ctor_get(v_x_539_, 0);
lean_inc(v_a_543_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_a_543_);
lean_ctor_set(v___x_544_, 1, v___y_540_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_545_, v___y_546_);
lean_dec_ref(v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_548_, lean_object* v_stx_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_548_, v_stx_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
if (lean_obj_tag(v_a_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_a_554_ = lean_ctor_get(v___x_552_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v___x_552_, 0);
lean_dec(v_unused_563_);
v___x_556_ = v___x_552_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_box(0);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_a_554_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_592_; 
v_val_564_ = lean_ctor_get(v_a_553_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_a_553_);
if (v_isSharedCheck_592_ == 0)
{
v___x_566_ = v_a_553_;
v_isShared_567_ = v_isSharedCheck_592_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_dec(v_a_553_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_592_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_snd_568_; 
v_snd_568_ = lean_ctor_get(v_val_564_, 1);
lean_inc(v_snd_568_);
lean_dec(v_val_564_);
if (lean_obj_tag(v_snd_568_) == 0)
{
lean_object* v_a_569_; lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_566_);
v_a_569_ = lean_ctor_get(v___x_552_, 1);
lean_inc(v_a_569_);
lean_dec_ref(v___x_552_);
v_a_570_ = lean_ctor_get(v_snd_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_snd_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_572_ = v_snd_568_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v_snd_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_575_, v_a_569_);
lean_dec_ref(v___x_575_);
return v___x_576_;
}
}
}
else
{
lean_object* v_a_579_; lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_591_; 
v_a_579_ = lean_ctor_get(v___x_552_, 1);
lean_inc(v_a_579_);
lean_dec_ref(v___x_552_);
v_a_580_ = lean_ctor_get(v_snd_568_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_snd_568_);
if (v_isSharedCheck_591_ == 0)
{
v___x_582_ = v_snd_568_;
v_isShared_583_ = v_isSharedCheck_591_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v_snd_568_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_591_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v_a_580_);
v___x_585_ = v___x_566_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_590_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_585_);
v___x_587_ = v___x_582_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_589_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_587_, v_a_579_);
lean_dec_ref(v___x_587_);
return v___x_588_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_593_ = lean_ctor_get(v___x_552_, 0);
v_a_594_ = lean_ctor_get(v___x_552_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_552_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_inc(v_a_593_);
lean_dec(v___x_552_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_593_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_602_, lean_object* v_stx_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_602_, v_stx_603_, v___y_604_, v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_607_, lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_fileName_616_; lean_object* v_fileMap_617_; lean_object* v_options_618_; lean_object* v_currRecDepth_619_; lean_object* v_maxRecDepth_620_; lean_object* v_ref_621_; lean_object* v_currNamespace_622_; lean_object* v_openDecls_623_; lean_object* v_initHeartbeats_624_; lean_object* v_maxHeartbeats_625_; lean_object* v_quotContext_626_; lean_object* v_currMacroScope_627_; uint8_t v_diag_628_; lean_object* v_cancelTk_x3f_629_; uint8_t v_suppressElabErrors_630_; lean_object* v_inheritedTraceOptions_631_; lean_object* v_ref_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_fileName_616_ = lean_ctor_get(v___y_613_, 0);
v_fileMap_617_ = lean_ctor_get(v___y_613_, 1);
v_options_618_ = lean_ctor_get(v___y_613_, 2);
v_currRecDepth_619_ = lean_ctor_get(v___y_613_, 3);
v_maxRecDepth_620_ = lean_ctor_get(v___y_613_, 4);
v_ref_621_ = lean_ctor_get(v___y_613_, 5);
v_currNamespace_622_ = lean_ctor_get(v___y_613_, 6);
v_openDecls_623_ = lean_ctor_get(v___y_613_, 7);
v_initHeartbeats_624_ = lean_ctor_get(v___y_613_, 8);
v_maxHeartbeats_625_ = lean_ctor_get(v___y_613_, 9);
v_quotContext_626_ = lean_ctor_get(v___y_613_, 10);
v_currMacroScope_627_ = lean_ctor_get(v___y_613_, 11);
v_diag_628_ = lean_ctor_get_uint8(v___y_613_, sizeof(void*)*14);
v_cancelTk_x3f_629_ = lean_ctor_get(v___y_613_, 12);
v_suppressElabErrors_630_ = lean_ctor_get_uint8(v___y_613_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_631_ = lean_ctor_get(v___y_613_, 13);
v_ref_632_ = l_Lean_replaceRef(v_ref_607_, v_ref_621_);
lean_inc_ref(v_inheritedTraceOptions_631_);
lean_inc(v_cancelTk_x3f_629_);
lean_inc(v_currMacroScope_627_);
lean_inc(v_quotContext_626_);
lean_inc(v_maxHeartbeats_625_);
lean_inc(v_initHeartbeats_624_);
lean_inc(v_openDecls_623_);
lean_inc(v_currNamespace_622_);
lean_inc(v_maxRecDepth_620_);
lean_inc(v_currRecDepth_619_);
lean_inc_ref(v_options_618_);
lean_inc_ref(v_fileMap_617_);
lean_inc_ref(v_fileName_616_);
v___x_633_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_633_, 0, v_fileName_616_);
lean_ctor_set(v___x_633_, 1, v_fileMap_617_);
lean_ctor_set(v___x_633_, 2, v_options_618_);
lean_ctor_set(v___x_633_, 3, v_currRecDepth_619_);
lean_ctor_set(v___x_633_, 4, v_maxRecDepth_620_);
lean_ctor_set(v___x_633_, 5, v_ref_632_);
lean_ctor_set(v___x_633_, 6, v_currNamespace_622_);
lean_ctor_set(v___x_633_, 7, v_openDecls_623_);
lean_ctor_set(v___x_633_, 8, v_initHeartbeats_624_);
lean_ctor_set(v___x_633_, 9, v_maxHeartbeats_625_);
lean_ctor_set(v___x_633_, 10, v_quotContext_626_);
lean_ctor_set(v___x_633_, 11, v_currMacroScope_627_);
lean_ctor_set(v___x_633_, 12, v_cancelTk_x3f_629_);
lean_ctor_set(v___x_633_, 13, v_inheritedTraceOptions_631_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*14, v_diag_628_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*14 + 1, v_suppressElabErrors_630_);
v___x_634_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___x_633_, v___y_614_);
lean_dec_ref(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_635_, lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_635_, v_msg_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v_ref_635_);
return v_res_644_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_645_; double v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_float_of_nat(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_650_, lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_ref_657_; lean_object* v___x_658_; lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_703_; 
v_ref_657_ = lean_ctor_get(v___y_654_, 5);
v___x_658_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_703_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_703_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_703_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v_traceState_664_; lean_object* v_env_665_; lean_object* v_nextMacroScope_666_; lean_object* v_ngen_667_; lean_object* v_auxDeclNGen_668_; lean_object* v_cache_669_; lean_object* v_messages_670_; lean_object* v_infoState_671_; lean_object* v_snapshotTasks_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_702_; 
v___x_663_ = lean_st_ref_take(v___y_655_);
v_traceState_664_ = lean_ctor_get(v___x_663_, 4);
v_env_665_ = lean_ctor_get(v___x_663_, 0);
v_nextMacroScope_666_ = lean_ctor_get(v___x_663_, 1);
v_ngen_667_ = lean_ctor_get(v___x_663_, 2);
v_auxDeclNGen_668_ = lean_ctor_get(v___x_663_, 3);
v_cache_669_ = lean_ctor_get(v___x_663_, 5);
v_messages_670_ = lean_ctor_get(v___x_663_, 6);
v_infoState_671_ = lean_ctor_get(v___x_663_, 7);
v_snapshotTasks_672_ = lean_ctor_get(v___x_663_, 8);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_702_ == 0)
{
v___x_674_ = v___x_663_;
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snapshotTasks_672_);
lean_inc(v_infoState_671_);
lean_inc(v_messages_670_);
lean_inc(v_cache_669_);
lean_inc(v_traceState_664_);
lean_inc(v_auxDeclNGen_668_);
lean_inc(v_ngen_667_);
lean_inc(v_nextMacroScope_666_);
lean_inc(v_env_665_);
lean_dec(v___x_663_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
uint64_t v_tid_676_; lean_object* v_traces_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_701_; 
v_tid_676_ = lean_ctor_get_uint64(v_traceState_664_, sizeof(void*)*1);
v_traces_677_ = lean_ctor_get(v_traceState_664_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_traceState_664_);
if (v_isSharedCheck_701_ == 0)
{
v___x_679_ = v_traceState_664_;
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_traces_677_);
lean_dec(v_traceState_664_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; double v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_683_ = 0;
v___x_684_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_685_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_685_, 0, v_cls_650_);
lean_ctor_set(v___x_685_, 1, v___x_681_);
lean_ctor_set(v___x_685_, 2, v___x_684_);
lean_ctor_set_float(v___x_685_, sizeof(void*)*3, v___x_682_);
lean_ctor_set_float(v___x_685_, sizeof(void*)*3 + 8, v___x_682_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*3 + 16, v___x_683_);
v___x_686_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_687_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v_a_659_);
lean_ctor_set(v___x_687_, 2, v___x_686_);
lean_inc(v_ref_657_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_ref_657_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_PersistentArray_push___redArg(v_traces_677_, v___x_688_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_689_);
v___x_691_ = v___x_679_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_689_);
lean_ctor_set_uint64(v_reuseFailAlloc_700_, sizeof(void*)*1, v_tid_676_);
v___x_691_ = v_reuseFailAlloc_700_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 4, v___x_691_);
v___x_693_ = v___x_674_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_env_665_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_nextMacroScope_666_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_ngen_667_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_auxDeclNGen_668_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_699_, 5, v_cache_669_);
lean_ctor_set(v_reuseFailAlloc_699_, 6, v_messages_670_);
lean_ctor_set(v_reuseFailAlloc_699_, 7, v_infoState_671_);
lean_ctor_set(v_reuseFailAlloc_699_, 8, v_snapshotTasks_672_);
v___x_693_ = v_reuseFailAlloc_699_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_694_ = lean_st_ref_set(v___y_655_, v___x_693_);
v___x_695_ = lean_box(0);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_695_);
v___x_697_ = v___x_661_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_704_, lean_object* v_msg_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_704_, v_msg_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
if (lean_obj_tag(v_as_715_) == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_box(0);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v_options_725_; uint8_t v_hasTrace_726_; 
v_options_725_ = lean_ctor_get(v___y_720_, 2);
v_hasTrace_726_ = lean_ctor_get_uint8(v_options_725_, sizeof(void*)*1);
if (v_hasTrace_726_ == 0)
{
lean_object* v_tail_727_; 
v_tail_727_ = lean_ctor_get(v_as_715_, 1);
lean_inc(v_tail_727_);
lean_dec_ref(v_as_715_);
v_as_715_ = v_tail_727_;
goto _start;
}
else
{
lean_object* v_head_729_; lean_object* v_tail_730_; lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v_inheritedTraceOptions_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_head_729_ = lean_ctor_get(v_as_715_, 0);
lean_inc(v_head_729_);
v_tail_730_ = lean_ctor_get(v_as_715_, 1);
lean_inc(v_tail_730_);
lean_dec_ref(v_as_715_);
v_fst_731_ = lean_ctor_get(v_head_729_, 0);
lean_inc_n(v_fst_731_, 2);
v_snd_732_ = lean_ctor_get(v_head_729_, 1);
lean_inc(v_snd_732_);
lean_dec(v_head_729_);
v_inheritedTraceOptions_733_ = lean_ctor_get(v___y_720_, 13);
v___x_734_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_735_ = l_Lean_Name_append(v___x_734_, v_fst_731_);
v___x_736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_733_, v_options_725_, v___x_735_);
lean_dec(v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v_snd_732_);
lean_dec(v_fst_731_);
v_as_715_ = v_tail_730_;
goto _start;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_738_, 0, v_snd_732_);
v___x_739_ = l_Lean_MessageData_ofFormat(v___x_738_);
v___x_740_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_731_, v___x_739_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_dec_ref(v___x_740_);
v_as_715_ = v_tail_730_;
goto _start;
}
else
{
lean_dec(v_tail_730_);
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_751_, lean_object* v_x_752_){
_start:
{
if (lean_obj_tag(v_x_752_) == 0)
{
lean_object* v___x_753_; 
v___x_753_ = lean_box(0);
return v___x_753_;
}
else
{
lean_object* v_key_754_; lean_object* v_value_755_; lean_object* v_tail_756_; uint8_t v___x_757_; 
v_key_754_ = lean_ctor_get(v_x_752_, 0);
v_value_755_ = lean_ctor_get(v_x_752_, 1);
v_tail_756_ = lean_ctor_get(v_x_752_, 2);
v___x_757_ = lean_name_eq(v_key_754_, v_a_751_);
if (v___x_757_ == 0)
{
v_x_752_ = v_tail_756_;
goto _start;
}
else
{
lean_object* v___x_759_; 
lean_inc(v_value_755_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v_value_755_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_760_, lean_object* v_x_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_760_, v_x_761_);
lean_dec(v_x_761_);
lean_dec(v_a_760_);
return v_res_762_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_763_; uint64_t v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(1723u);
v___x_764_ = lean_uint64_of_nat(v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_buckets_767_; lean_object* v___x_768_; uint64_t v___y_770_; 
v_buckets_767_ = lean_ctor_get(v_m_765_, 1);
v___x_768_ = lean_array_get_size(v_buckets_767_);
if (lean_obj_tag(v_a_766_) == 0)
{
uint64_t v___x_784_; 
v___x_784_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0);
v___y_770_ = v___x_784_;
goto v___jp_769_;
}
else
{
uint64_t v_hash_785_; 
v_hash_785_ = lean_ctor_get_uint64(v_a_766_, sizeof(void*)*2);
v___y_770_ = v_hash_785_;
goto v___jp_769_;
}
v___jp_769_:
{
uint64_t v___x_771_; uint64_t v___x_772_; uint64_t v_fold_773_; uint64_t v___x_774_; uint64_t v___x_775_; uint64_t v___x_776_; size_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_771_ = 32ULL;
v___x_772_ = lean_uint64_shift_right(v___y_770_, v___x_771_);
v_fold_773_ = lean_uint64_xor(v___y_770_, v___x_772_);
v___x_774_ = 16ULL;
v___x_775_ = lean_uint64_shift_right(v_fold_773_, v___x_774_);
v___x_776_ = lean_uint64_xor(v_fold_773_, v___x_775_);
v___x_777_ = lean_uint64_to_usize(v___x_776_);
v___x_778_ = lean_usize_of_nat(v___x_768_);
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_sub(v___x_778_, v___x_779_);
v___x_781_ = lean_usize_land(v___x_777_, v___x_780_);
v___x_782_ = lean_array_uget_borrowed(v_buckets_767_, v___x_781_);
v___x_783_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_766_, v___x_782_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_m_786_);
return v_res_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_789_, lean_object* v_i_790_, lean_object* v_k_791_){
_start:
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = lean_array_get_size(v_keys_789_);
v___x_793_ = lean_nat_dec_lt(v_i_790_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v_i_790_);
return v___x_793_;
}
else
{
lean_object* v_k_x27_794_; uint8_t v___x_795_; 
v_k_x27_794_ = lean_array_fget_borrowed(v_keys_789_, v_i_790_);
v___x_795_ = l_Lean_instBEqExtraModUse_beq(v_k_791_, v_k_x27_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_add(v_i_790_, v___x_796_);
lean_dec(v_i_790_);
v_i_790_ = v___x_797_;
goto _start;
}
else
{
lean_dec(v_i_790_);
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_799_, lean_object* v_i_800_, lean_object* v_k_801_){
_start:
{
uint8_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_799_, v_i_800_, v_k_801_);
lean_dec_ref(v_k_801_);
lean_dec_ref(v_keys_799_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0(void){
_start:
{
size_t v___x_804_; size_t v___x_805_; size_t v___x_806_; 
v___x_804_ = ((size_t)5ULL);
v___x_805_ = ((size_t)1ULL);
v___x_806_ = lean_usize_shift_left(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1(void){
_start:
{
size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; 
v___x_807_ = ((size_t)1ULL);
v___x_808_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0);
v___x_809_ = lean_usize_sub(v___x_808_, v___x_807_);
return v___x_809_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_810_, size_t v_x_811_, lean_object* v_x_812_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
lean_object* v_es_813_; lean_object* v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; lean_object* v_j_818_; lean_object* v___x_819_; 
v_es_813_ = lean_ctor_get(v_x_810_, 0);
v___x_814_ = lean_box(2);
v___x_815_ = ((size_t)5ULL);
v___x_816_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1);
v___x_817_ = lean_usize_land(v_x_811_, v___x_816_);
v_j_818_ = lean_usize_to_nat(v___x_817_);
v___x_819_ = lean_array_get_borrowed(v___x_814_, v_es_813_, v_j_818_);
lean_dec(v_j_818_);
switch(lean_obj_tag(v___x_819_))
{
case 0:
{
lean_object* v_key_820_; uint8_t v___x_821_; 
v_key_820_ = lean_ctor_get(v___x_819_, 0);
v___x_821_ = l_Lean_instBEqExtraModUse_beq(v_x_812_, v_key_820_);
return v___x_821_;
}
case 1:
{
lean_object* v_node_822_; size_t v___x_823_; 
v_node_822_ = lean_ctor_get(v___x_819_, 0);
v___x_823_ = lean_usize_shift_right(v_x_811_, v___x_815_);
v_x_810_ = v_node_822_;
v_x_811_ = v___x_823_;
goto _start;
}
default: 
{
uint8_t v___x_825_; 
v___x_825_ = 0;
return v___x_825_;
}
}
}
else
{
lean_object* v_ks_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_ks_826_ = lean_ctor_get(v_x_810_, 0);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_826_, v___x_827_, v_x_812_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
size_t v_x_284783__boxed_832_; uint8_t v_res_833_; lean_object* v_r_834_; 
v_x_284783__boxed_832_ = lean_unbox_usize(v_x_830_);
lean_dec(v_x_830_);
v_res_833_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_829_, v_x_284783__boxed_832_, v_x_831_);
lean_dec_ref(v_x_831_);
lean_dec_ref(v_x_829_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
uint64_t v___x_837_; size_t v___x_838_; uint8_t v___x_839_; 
v___x_837_ = l_Lean_instHashableExtraModUse_hash(v_x_836_);
v___x_838_ = lean_uint64_to_usize(v___x_837_);
v___x_839_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_835_, v___x_838_, v_x_836_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_840_, v_x_841_);
lean_dec_ref(v_x_841_);
lean_dec_ref(v_x_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1));
v___x_847_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0));
v___x_848_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_847_, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_849_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_855_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_ctor_set(v___x_855_, 2, v___x_854_);
lean_ctor_set(v___x_855_, 3, v___x_854_);
lean_ctor_set(v___x_855_, 4, v___x_854_);
lean_ctor_set(v___x_855_, 5, v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_866_ = l_Lean_stringToMessageData(v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v_cls_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_cls_867_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_868_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_869_ = l_Lean_Name_append(v___x_868_, v_cls_867_);
return v___x_869_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_872_ = l_Lean_stringToMessageData(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_880_, uint8_t v_isMeta_881_, lean_object* v_hint_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; lean_object* v_env_891_; uint8_t v_isExporting_892_; lean_object* v___x_893_; lean_object* v_env_894_; lean_object* v___x_895_; lean_object* v_entry_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_890_ = lean_st_ref_get(v___y_888_);
v_env_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc_ref(v_env_891_);
lean_dec(v___x_890_);
v_isExporting_892_ = lean_ctor_get_uint8(v_env_891_, sizeof(void*)*8);
lean_dec_ref(v_env_891_);
v___x_893_ = lean_st_ref_get(v___y_888_);
v_env_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc_ref(v_env_894_);
lean_dec(v___x_893_);
v___x_895_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
lean_inc(v_mod_880_);
v_entry_896_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_896_, 0, v_mod_880_);
lean_ctor_set_uint8(v_entry_896_, sizeof(void*)*1, v_isExporting_892_);
lean_ctor_set_uint8(v_entry_896_, sizeof(void*)*1 + 1, v_isMeta_881_);
v___x_897_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_898_ = lean_box(1);
v___x_899_ = lean_box(0);
v___x_942_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_895_, v___x_897_, v_env_894_, v___x_898_, v___x_899_);
v___x_943_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_942_, v_entry_896_);
lean_dec(v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v_options_944_; uint8_t v_hasTrace_945_; 
v_options_944_ = lean_ctor_get(v___y_887_, 2);
v_hasTrace_945_ = lean_ctor_get_uint8(v_options_944_, sizeof(void*)*1);
if (v_hasTrace_945_ == 0)
{
lean_dec(v_hint_882_);
lean_dec(v_mod_880_);
v___y_901_ = v___y_886_;
v___y_902_ = v___y_888_;
goto v___jp_900_;
}
else
{
lean_object* v_inheritedTraceOptions_946_; lean_object* v_cls_947_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_inheritedTraceOptions_946_ = lean_ctor_get(v___y_887_, 13);
v_cls_947_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_967_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
v___x_968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_946_, v_options_944_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec(v_hint_882_);
lean_dec(v_mod_880_);
v___y_901_ = v___y_886_;
v___y_902_ = v___y_888_;
goto v___jp_900_;
}
else
{
lean_object* v___x_969_; lean_object* v___y_971_; 
v___x_969_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
if (v_isExporting_892_ == 0)
{
lean_object* v___x_978_; 
v___x_978_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21));
v___y_971_ = v___x_978_;
goto v___jp_970_;
}
else
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22));
v___y_971_ = v___x_979_;
goto v___jp_970_;
}
v___jp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc_ref(v___y_971_);
v___x_972_ = l_Lean_stringToMessageData(v___y_971_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_969_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
if (v_isMeta_881_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_954_ = v___x_975_;
v___y_955_ = v___x_976_;
goto v___jp_953_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_954_ = v___x_975_;
v___y_955_ = v___x_977_;
goto v___jp_953_;
}
}
}
v___jp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___y_949_);
lean_ctor_set(v___x_951_, 1, v___y_950_);
v___x_952_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_947_, v___x_951_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_dec_ref(v___x_952_);
v___y_901_ = v___y_886_;
v___y_902_ = v___y_888_;
goto v___jp_900_;
}
else
{
lean_dec_ref(v_entry_896_);
return v___x_952_;
}
}
v___jp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
lean_inc_ref(v___y_955_);
v___x_956_ = l_Lean_stringToMessageData(v___y_955_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___y_954_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Lean_MessageData_ofName(v_mod_880_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = l_Lean_Name_isAnonymous(v_hint_882_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_964_ = l_Lean_MessageData_ofName(v_hint_882_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___y_949_ = v___x_961_;
v___y_950_ = v___x_965_;
goto v___jp_948_;
}
else
{
lean_object* v___x_966_; 
lean_dec(v_hint_882_);
v___x_966_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13);
v___y_949_ = v___x_961_;
v___y_950_ = v___x_966_;
goto v___jp_948_;
}
}
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec_ref(v_entry_896_);
lean_dec(v_hint_882_);
lean_dec(v_mod_880_);
v___x_980_ = lean_box(0);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
v___jp_900_:
{
lean_object* v___x_903_; lean_object* v_toEnvExtension_904_; lean_object* v_env_905_; lean_object* v_nextMacroScope_906_; lean_object* v_ngen_907_; lean_object* v_auxDeclNGen_908_; lean_object* v_traceState_909_; lean_object* v_messages_910_; lean_object* v_infoState_911_; lean_object* v_snapshotTasks_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_940_; 
v___x_903_ = lean_st_ref_take(v___y_902_);
v_toEnvExtension_904_ = lean_ctor_get(v___x_897_, 0);
v_env_905_ = lean_ctor_get(v___x_903_, 0);
v_nextMacroScope_906_ = lean_ctor_get(v___x_903_, 1);
v_ngen_907_ = lean_ctor_get(v___x_903_, 2);
v_auxDeclNGen_908_ = lean_ctor_get(v___x_903_, 3);
v_traceState_909_ = lean_ctor_get(v___x_903_, 4);
v_messages_910_ = lean_ctor_get(v___x_903_, 6);
v_infoState_911_ = lean_ctor_get(v___x_903_, 7);
v_snapshotTasks_912_ = lean_ctor_get(v___x_903_, 8);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_903_, 5);
lean_dec(v_unused_941_);
v___x_914_ = v___x_903_;
v_isShared_915_ = v_isSharedCheck_940_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_snapshotTasks_912_);
lean_inc(v_infoState_911_);
lean_inc(v_messages_910_);
lean_inc(v_traceState_909_);
lean_inc(v_auxDeclNGen_908_);
lean_inc(v_ngen_907_);
lean_inc(v_nextMacroScope_906_);
lean_inc(v_env_905_);
lean_dec(v___x_903_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_940_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_asyncMode_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v_asyncMode_916_ = lean_ctor_get(v_toEnvExtension_904_, 2);
v___x_917_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_897_, v_env_905_, v_entry_896_, v_asyncMode_916_, v___x_899_);
v___x_918_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 5, v___x_918_);
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_920_ = v___x_914_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_nextMacroScope_906_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_ngen_907_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_auxDeclNGen_908_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v_traceState_909_);
lean_ctor_set(v_reuseFailAlloc_939_, 5, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_939_, 6, v_messages_910_);
lean_ctor_set(v_reuseFailAlloc_939_, 7, v_infoState_911_);
lean_ctor_set(v_reuseFailAlloc_939_, 8, v_snapshotTasks_912_);
v___x_920_ = v_reuseFailAlloc_939_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_mctx_923_; lean_object* v_zetaDeltaFVarIds_924_; lean_object* v_postponed_925_; lean_object* v_diag_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_937_; 
v___x_921_ = lean_st_ref_set(v___y_902_, v___x_920_);
v___x_922_ = lean_st_ref_take(v___y_901_);
v_mctx_923_ = lean_ctor_get(v___x_922_, 0);
v_zetaDeltaFVarIds_924_ = lean_ctor_get(v___x_922_, 2);
v_postponed_925_ = lean_ctor_get(v___x_922_, 3);
v_diag_926_ = lean_ctor_get(v___x_922_, 4);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v___x_922_, 1);
lean_dec(v_unused_938_);
v___x_928_ = v___x_922_;
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_diag_926_);
lean_inc(v_postponed_925_);
lean_inc(v_zetaDeltaFVarIds_924_);
lean_inc(v_mctx_923_);
lean_dec(v___x_922_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_930_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_930_);
v___x_932_ = v___x_928_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_mctx_923_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_zetaDeltaFVarIds_924_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_postponed_925_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v_diag_926_);
v___x_932_ = v_reuseFailAlloc_936_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_st_ref_set(v___y_901_, v___x_932_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_982_, lean_object* v_isMeta_983_, lean_object* v_hint_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v_isMeta_boxed_992_; lean_object* v_res_993_; 
v_isMeta_boxed_992_ = lean_unbox(v_isMeta_983_);
v_res_993_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_982_, v_isMeta_boxed_992_, v_hint_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_994_, lean_object* v_declName_995_, lean_object* v_as_996_, size_t v_sz_997_, size_t v_i_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = lean_usize_dec_lt(v_i_998_, v_sz_997_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_dec(v_declName_995_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_b_999_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v_modules_1010_; lean_object* v___x_1011_; lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v_toImport_1014_; lean_object* v_module_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1009_ = l_Lean_Environment_header(v___x_994_);
v_modules_1010_ = lean_ctor_get(v___x_1009_, 3);
lean_inc_ref(v_modules_1010_);
lean_dec_ref(v___x_1009_);
v___x_1011_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1012_ = lean_array_uget_borrowed(v_as_996_, v_i_998_);
v___x_1013_ = lean_array_get(v___x_1011_, v_modules_1010_, v_a_1012_);
lean_dec_ref(v_modules_1010_);
v_toImport_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_ref(v_toImport_1014_);
lean_dec(v___x_1013_);
v_module_1015_ = lean_ctor_get(v_toImport_1014_, 0);
lean_inc(v_module_1015_);
lean_dec_ref(v_toImport_1014_);
v___x_1016_ = 0;
lean_inc(v_declName_995_);
v___x_1017_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1015_, v___x_1016_, v_declName_995_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; 
lean_dec_ref(v___x_1017_);
v___x_1018_ = lean_box(0);
v___x_1019_ = ((size_t)1ULL);
v___x_1020_ = lean_usize_add(v_i_998_, v___x_1019_);
v_i_998_ = v___x_1020_;
v_b_999_ = v___x_1018_;
goto _start;
}
else
{
lean_dec(v_declName_995_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1022_, lean_object* v_declName_1023_, lean_object* v_as_1024_, lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1022_, v_declName_1023_, v_as_1024_, v_sz_boxed_1035_, v_i_boxed_1036_, v_b_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v_as_1024_);
lean_dec_ref(v___x_1022_);
return v_res_1037_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___x_1041_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0));
v___x_1042_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1041_, v___x_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1045_, uint8_t v_isMeta_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; lean_object* v_env_1058_; lean_object* v___y_1060_; lean_object* v___x_1073_; 
v___x_1054_ = lean_st_ref_get(v___y_1052_);
v_env_1058_ = lean_ctor_get(v___x_1054_, 0);
lean_inc_ref(v_env_1058_);
lean_dec(v___x_1054_);
v___x_1073_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1058_, v_declName_1045_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_dec_ref(v_env_1058_);
lean_dec(v_declName_1045_);
goto v___jp_1055_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1075_; lean_object* v_modules_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_val_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_val_1074_);
lean_dec_ref(v___x_1073_);
v___x_1075_ = l_Lean_Environment_header(v_env_1058_);
v_modules_1076_ = lean_ctor_get(v___x_1075_, 3);
lean_inc_ref(v_modules_1076_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = lean_array_get_size(v_modules_1076_);
v___x_1078_ = lean_nat_dec_lt(v_val_1074_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_dec_ref(v_modules_1076_);
lean_dec(v_val_1074_);
lean_dec_ref(v_env_1058_);
lean_dec(v_declName_1045_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1079_; lean_object* v_env_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___y_1084_; 
v___x_1079_ = lean_st_ref_get(v___y_1052_);
v_env_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_env_1080_);
lean_dec(v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2);
v___x_1082_ = lean_array_fget(v_modules_1076_, v_val_1074_);
lean_dec(v_val_1074_);
lean_dec_ref(v_modules_1076_);
if (v_isMeta_1046_ == 0)
{
lean_dec_ref(v_env_1080_);
v___y_1084_ = v_isMeta_1046_;
goto v___jp_1083_;
}
else
{
uint8_t v___x_1095_; 
lean_inc(v_declName_1045_);
v___x_1095_ = l_Lean_isMarkedMeta(v_env_1080_, v_declName_1045_);
if (v___x_1095_ == 0)
{
v___y_1084_ = v_isMeta_1046_;
goto v___jp_1083_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = 0;
v___y_1084_ = v___x_1096_;
goto v___jp_1083_;
}
}
v___jp_1083_:
{
lean_object* v_toImport_1085_; lean_object* v_module_1086_; lean_object* v___x_1087_; 
v_toImport_1085_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_toImport_1085_);
lean_dec(v___x_1082_);
v_module_1086_ = lean_ctor_get(v_toImport_1085_, 0);
lean_inc(v_module_1086_);
lean_dec_ref(v_toImport_1085_);
lean_inc(v_declName_1045_);
v___x_1087_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1086_, v___y_1084_, v_declName_1045_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v___x_1087_);
v___x_1088_ = l_Lean_indirectModUseExt;
v___x_1089_ = lean_box(1);
v___x_1090_ = lean_box(0);
lean_inc_ref(v_env_1058_);
v___x_1091_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1081_, v___x_1088_, v_env_1058_, v___x_1089_, v___x_1090_);
v___x_1092_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1091_, v_declName_1045_);
lean_dec(v___x_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3));
v___y_1060_ = v___x_1093_;
goto v___jp_1059_;
}
else
{
lean_object* v_val_1094_; 
v_val_1094_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_val_1094_);
lean_dec_ref(v___x_1092_);
v___y_1060_ = v_val_1094_;
goto v___jp_1059_;
}
}
else
{
lean_dec_ref(v_env_1058_);
lean_dec(v_declName_1045_);
return v___x_1087_;
}
}
}
}
v___jp_1055_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
v___jp_1059_:
{
lean_object* v___x_1061_; size_t v_sz_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = lean_box(0);
v_sz_1062_ = lean_array_size(v___y_1060_);
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1058_, v_declName_1045_, v___y_1060_, v_sz_1062_, v___x_1063_, v___x_1061_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_env_1058_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v___x_1064_, 0);
lean_dec(v_unused_1072_);
v___x_1066_ = v___x_1064_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_dec(v___x_1064_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1061_);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1061_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1097_, lean_object* v_isMeta_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_isMeta_boxed_1106_; lean_object* v_res_1107_; 
v_isMeta_boxed_1106_ = lean_unbox(v_isMeta_1098_);
v_res_1107_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1097_, v_isMeta_boxed_1106_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1108_, lean_object* v_b_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
if (lean_obj_tag(v_as_x27_1108_) == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_b_1109_);
return v___x_1117_;
}
else
{
lean_object* v_head_1118_; lean_object* v_tail_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; 
v_head_1118_ = lean_ctor_get(v_as_x27_1108_, 0);
lean_inc(v_head_1118_);
v_tail_1119_ = lean_ctor_get(v_as_x27_1108_, 1);
lean_inc(v_tail_1119_);
lean_dec_ref(v_as_x27_1108_);
v___x_1120_ = 1;
v___x_1121_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1118_, v___x_1120_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v___x_1121_);
v___x_1122_ = lean_box(0);
v_as_x27_1108_ = v_tail_1119_;
v_b_1109_ = v___x_1122_;
goto _start;
}
else
{
lean_dec(v_tail_1119_);
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1124_, v_b_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1134_, lean_object* v_currNamespace_1135_, lean_object* v_openDecls_1136_, lean_object* v_n_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = l_Lean_ResolveName_resolveNamespace(v_env_1134_, v_currNamespace_1135_, v_openDecls_1136_, v_n_1137_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___y_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1142_, lean_object* v_currNamespace_1143_, lean_object* v_openDecls_1144_, lean_object* v_n_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1142_, v_currNamespace_1143_, v_openDecls_1144_, v_n_1145_, v___y_1146_, v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_currNamespace_1149_);
lean_ctor_set(v___x_1152_, 1, v___y_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1153_, v___y_1154_, v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1157_, lean_object* v_options_1158_, lean_object* v_currNamespace_1159_, lean_object* v_openDecls_1160_, lean_object* v_n_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = l_Lean_ResolveName_resolveGlobalName(v_env_1157_, v_options_1158_, v_currNamespace_1159_, v_openDecls_1160_, v_n_1161_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___y_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1166_, lean_object* v_options_1167_, lean_object* v_currNamespace_1168_, lean_object* v_openDecls_1169_, lean_object* v_n_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1166_, v_options_1167_, v_currNamespace_1168_, v_openDecls_1169_, v_n_1170_, v___y_1171_, v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v_options_1167_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v_env_1184_; lean_object* v_options_1185_; lean_object* v_currRecDepth_1186_; lean_object* v_maxRecDepth_1187_; lean_object* v_ref_1188_; lean_object* v_currNamespace_1189_; lean_object* v_openDecls_1190_; lean_object* v_quotContext_1191_; lean_object* v_currMacroScope_1192_; lean_object* v___x_1193_; lean_object* v_nextMacroScope_1194_; lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v_methods_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1183_ = lean_st_ref_get(v___y_1181_);
v_env_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref_n(v_env_1184_, 4);
lean_dec(v___x_1183_);
v_options_1185_ = lean_ctor_get(v___y_1180_, 2);
v_currRecDepth_1186_ = lean_ctor_get(v___y_1180_, 3);
v_maxRecDepth_1187_ = lean_ctor_get(v___y_1180_, 4);
v_ref_1188_ = lean_ctor_get(v___y_1180_, 5);
v_currNamespace_1189_ = lean_ctor_get(v___y_1180_, 6);
v_openDecls_1190_ = lean_ctor_get(v___y_1180_, 7);
v_quotContext_1191_ = lean_ctor_get(v___y_1180_, 10);
v_currMacroScope_1192_ = lean_ctor_get(v___y_1180_, 11);
v___x_1193_ = lean_st_ref_get(v___y_1181_);
v_nextMacroScope_1194_ = lean_ctor_get(v___x_1193_, 1);
lean_inc(v_nextMacroScope_1194_);
lean_dec(v___x_1193_);
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1195_, 0, v_env_1184_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1196_, 0, v_env_1184_);
lean_inc_n(v_openDecls_1190_, 2);
lean_inc_n(v_currNamespace_1189_, 3);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1197_, 0, v_env_1184_);
lean_closure_set(v___f_1197_, 1, v_currNamespace_1189_);
lean_closure_set(v___f_1197_, 2, v_openDecls_1190_);
v___f_1198_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1198_, 0, v_currNamespace_1189_);
lean_inc_ref(v_options_1185_);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1199_, 0, v_env_1184_);
lean_closure_set(v___f_1199_, 1, v_options_1185_);
lean_closure_set(v___f_1199_, 2, v_currNamespace_1189_);
lean_closure_set(v___f_1199_, 3, v_openDecls_1190_);
v_methods_1200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1200_, 0, v___f_1195_);
lean_ctor_set(v_methods_1200_, 1, v___f_1198_);
lean_ctor_set(v_methods_1200_, 2, v___f_1196_);
lean_ctor_set(v_methods_1200_, 3, v___f_1197_);
lean_ctor_set(v_methods_1200_, 4, v___f_1199_);
lean_inc(v_ref_1188_);
lean_inc(v_maxRecDepth_1187_);
lean_inc(v_currRecDepth_1186_);
lean_inc(v_currMacroScope_1192_);
lean_inc(v_quotContext_1191_);
v___x_1201_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1201_, 0, v_methods_1200_);
lean_ctor_set(v___x_1201_, 1, v_quotContext_1191_);
lean_ctor_set(v___x_1201_, 2, v_currMacroScope_1192_);
lean_ctor_set(v___x_1201_, 3, v_currRecDepth_1186_);
lean_ctor_set(v___x_1201_, 4, v_maxRecDepth_1187_);
lean_ctor_set(v___x_1201_, 5, v_ref_1188_);
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1203_, 0, v_nextMacroScope_1194_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
lean_ctor_set(v___x_1203_, 2, v___x_1202_);
v___x_1204_ = lean_apply_2(v_x_1175_, v___x_1201_, v___x_1203_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v_a_1206_; lean_object* v_macroScope_1207_; lean_object* v_traceMsgs_1208_; lean_object* v_expandedMacroDecls_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 1);
lean_inc(v_a_1205_);
v_a_1206_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___x_1204_);
v_macroScope_1207_ = lean_ctor_get(v_a_1205_, 0);
lean_inc(v_macroScope_1207_);
v_traceMsgs_1208_ = lean_ctor_get(v_a_1205_, 1);
lean_inc(v_traceMsgs_1208_);
v_expandedMacroDecls_1209_ = lean_ctor_get(v_a_1205_, 2);
lean_inc(v_expandedMacroDecls_1209_);
lean_dec(v_a_1205_);
v___x_1210_ = lean_box(0);
v___x_1211_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1209_, v___x_1210_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v___x_1212_; lean_object* v_env_1213_; lean_object* v_ngen_1214_; lean_object* v_auxDeclNGen_1215_; lean_object* v_traceState_1216_; lean_object* v_cache_1217_; lean_object* v_messages_1218_; lean_object* v_infoState_1219_; lean_object* v_snapshotTasks_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v___x_1211_);
v___x_1212_ = lean_st_ref_take(v___y_1181_);
v_env_1213_ = lean_ctor_get(v___x_1212_, 0);
v_ngen_1214_ = lean_ctor_get(v___x_1212_, 2);
v_auxDeclNGen_1215_ = lean_ctor_get(v___x_1212_, 3);
v_traceState_1216_ = lean_ctor_get(v___x_1212_, 4);
v_cache_1217_ = lean_ctor_get(v___x_1212_, 5);
v_messages_1218_ = lean_ctor_get(v___x_1212_, 6);
v_infoState_1219_ = lean_ctor_get(v___x_1212_, 7);
v_snapshotTasks_1220_ = lean_ctor_get(v___x_1212_, 8);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1212_, 1);
lean_dec(v_unused_1247_);
v___x_1222_ = v___x_1212_;
v_isShared_1223_ = v_isSharedCheck_1246_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_snapshotTasks_1220_);
lean_inc(v_infoState_1219_);
lean_inc(v_messages_1218_);
lean_inc(v_cache_1217_);
lean_inc(v_traceState_1216_);
lean_inc(v_auxDeclNGen_1215_);
lean_inc(v_ngen_1214_);
lean_inc(v_env_1213_);
lean_dec(v___x_1212_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1246_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v_macroScope_1207_);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_env_1213_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_macroScope_1207_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_ngen_1214_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_auxDeclNGen_1215_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_traceState_1216_);
lean_ctor_set(v_reuseFailAlloc_1245_, 5, v_cache_1217_);
lean_ctor_set(v_reuseFailAlloc_1245_, 6, v_messages_1218_);
lean_ctor_set(v_reuseFailAlloc_1245_, 7, v_infoState_1219_);
lean_ctor_set(v_reuseFailAlloc_1245_, 8, v_snapshotTasks_1220_);
v___x_1225_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_st_ref_set(v___y_1181_, v___x_1225_);
v___x_1227_ = l_List_reverse___redArg(v_traceMsgs_1208_);
v___x_1228_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1227_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1228_, 0);
lean_dec(v_unused_1236_);
v___x_1230_ = v___x_1228_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v___x_1228_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v_a_1206_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1206_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_a_1206_);
v_a_1237_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1228_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1228_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_traceMsgs_1208_);
lean_dec(v_macroScope_1207_);
lean_dec(v_a_1206_);
v_a_1248_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1211_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1211_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; 
v_a_1256_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___x_1204_);
if (lean_obj_tag(v_a_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v_a_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_a_1257_ = lean_ctor_get(v_a_1256_, 0);
lean_inc(v_a_1257_);
v_a_1258_ = lean_ctor_get(v_a_1256_, 1);
lean_inc_ref(v_a_1258_);
lean_dec_ref(v_a_1256_);
v___x_1259_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1260_ = lean_string_dec_eq(v_a_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_a_1258_);
v___x_1262_ = l_Lean_MessageData_ofFormat(v___x_1261_);
v___x_1263_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1257_, v___x_1262_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v_a_1257_);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; 
lean_dec_ref(v_a_1258_);
v___x_1264_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1257_);
return v___x_1264_;
}
}
else
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1278_, size_t v_i_1279_, lean_object* v_bs_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_lt(v_i_1279_, v_sz_1278_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_bs_1280_);
return v___x_1282_;
}
else
{
lean_object* v_v_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_v_1283_ = lean_array_uget(v_bs_1280_, v_i_1279_);
v___x_1284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1283_);
v___x_1285_ = l_Lean_Syntax_isOfKind(v_v_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_dec(v_v_1283_);
lean_dec_ref(v_bs_1280_);
v___x_1286_ = lean_box(0);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = l_Lean_Syntax_getArg(v_v_1283_, v___x_1287_);
v___x_1289_ = l_Lean_Syntax_isOfKind(v___x_1288_, v___x_1284_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec(v_v_1283_);
lean_dec_ref(v_bs_1280_);
v___x_1290_ = lean_box(0);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v_bs_x27_1292_; lean_object* v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1291_ = lean_unsigned_to_nat(3u);
v_bs_x27_1292_ = lean_array_uset(v_bs_1280_, v_i_1279_, v___x_1287_);
v___x_1293_ = l_Lean_Syntax_getArg(v_v_1283_, v___x_1291_);
lean_dec(v_v_1283_);
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_i_1279_, v___x_1294_);
v___x_1296_ = lean_array_uset(v_bs_x27_1292_, v_i_1279_, v___x_1293_);
v_i_1279_ = v___x_1295_;
v_bs_1280_ = v___x_1296_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1298_, lean_object* v_i_1299_, lean_object* v_bs_1300_){
_start:
{
size_t v_sz_boxed_1301_; size_t v_i_boxed_1302_; lean_object* v_res_1303_; 
v_sz_boxed_1301_ = lean_unbox_usize(v_sz_1298_);
lean_dec(v_sz_1298_);
v_i_boxed_1302_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_res_1303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1301_, v_i_boxed_1302_, v_bs_1300_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1316_, size_t v_i_1317_, lean_object* v_bs_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1317_, v_sz_1316_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_bs_1318_);
return v___x_1320_;
}
else
{
lean_object* v_v_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_v_1321_ = lean_array_uget(v_bs_1318_, v_i_1317_);
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1321_);
v___x_1323_ = l_Lean_Syntax_isOfKind(v_v_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v_v_1321_);
lean_dec_ref(v_bs_1318_);
v___x_1324_ = lean_box(0);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1325_ = lean_unsigned_to_nat(1u);
v___x_1326_ = l_Lean_Syntax_getArg(v_v_1321_, v___x_1325_);
v___x_1327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1328_ = l_Lean_Syntax_isOfKind(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_dec(v_v_1321_);
lean_dec_ref(v_bs_1318_);
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v_bs_x27_1332_; lean_object* v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1330_ = lean_unsigned_to_nat(3u);
v___x_1331_ = lean_unsigned_to_nat(0u);
v_bs_x27_1332_ = lean_array_uset(v_bs_1318_, v_i_1317_, v___x_1331_);
v___x_1333_ = l_Lean_Syntax_getArg(v_v_1321_, v___x_1330_);
lean_dec(v_v_1321_);
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_add(v_i_1317_, v___x_1334_);
v___x_1336_ = lean_array_uset(v_bs_x27_1332_, v_i_1317_, v___x_1333_);
v_i_1317_ = v___x_1335_;
v_bs_1318_ = v___x_1336_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1338_, lean_object* v_i_1339_, lean_object* v_bs_1340_){
_start:
{
size_t v_sz_boxed_1341_; size_t v_i_boxed_1342_; lean_object* v_res_1343_; 
v_sz_boxed_1341_ = lean_unbox_usize(v_sz_1338_);
lean_dec(v_sz_1338_);
v_i_boxed_1342_ = lean_unbox_usize(v_i_1339_);
lean_dec(v_i_1339_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1341_, v_i_boxed_1342_, v_bs_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1350_, size_t v_i_1351_, lean_object* v_bs_1352_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_usize_dec_lt(v_i_1351_, v_sz_1350_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_bs_1352_);
return v___x_1354_;
}
else
{
lean_object* v_v_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_v_1355_ = lean_array_uget(v_bs_1352_, v_i_1351_);
v___x_1356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1355_);
v___x_1357_ = l_Lean_Syntax_isOfKind(v_v_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec(v_v_1355_);
lean_dec_ref(v_bs_1352_);
v___x_1358_ = lean_box(0);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v_bs_x27_1360_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v_bs_x27_1360_ = lean_array_uset(v_bs_1352_, v_i_1351_, v___x_1359_);
v___x_1367_ = l_Lean_Syntax_getArg(v_v_1355_, v___x_1359_);
lean_dec(v_v_1355_);
v___x_1368_ = l_Lean_Syntax_isNone(v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(2u);
v___x_1370_ = l_Lean_Syntax_matchesNull(v___x_1367_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec_ref(v_bs_x27_1360_);
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
else
{
goto v___jp_1361_;
}
}
else
{
lean_dec(v___x_1367_);
goto v___jp_1361_;
}
v___jp_1361_:
{
lean_object* v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1351_, v___x_1363_);
v___x_1365_ = lean_array_uset(v_bs_x27_1360_, v_i_1351_, v___x_1362_);
v_i_1351_ = v___x_1364_;
v_bs_1352_ = v___x_1365_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1372_, lean_object* v_i_1373_, lean_object* v_bs_1374_){
_start:
{
size_t v_sz_boxed_1375_; size_t v_i_boxed_1376_; lean_object* v_res_1377_; 
v_sz_boxed_1375_ = lean_unbox_usize(v_sz_1372_);
lean_dec(v_sz_1372_);
v_i_boxed_1376_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_res_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1375_, v_i_boxed_1376_, v_bs_1374_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1378_, size_t v_i_1379_, lean_object* v_bs_1380_){
_start:
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_usize_dec_lt(v_i_1379_, v_sz_1378_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_bs_1380_);
return v___x_1382_;
}
else
{
lean_object* v_v_1383_; lean_object* v___x_1384_; lean_object* v_bs_x27_1385_; size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v_v_1383_ = lean_array_uget(v_bs_1380_, v_i_1379_);
v___x_1384_ = lean_unsigned_to_nat(0u);
v_bs_x27_1385_ = lean_array_uset(v_bs_1380_, v_i_1379_, v___x_1384_);
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_add(v_i_1379_, v___x_1386_);
v___x_1388_ = lean_array_uset(v_bs_x27_1385_, v_i_1379_, v_v_1383_);
v_i_1379_ = v___x_1387_;
v_bs_1380_ = v___x_1388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1390_, lean_object* v_i_1391_, lean_object* v_bs_1392_){
_start:
{
size_t v_sz_boxed_1393_; size_t v_i_boxed_1394_; lean_object* v_res_1395_; 
v_sz_boxed_1393_ = lean_unbox_usize(v_sz_1390_);
lean_dec(v_sz_1390_);
v_i_boxed_1394_ = lean_unbox_usize(v_i_1391_);
lean_dec(v_i_1391_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1393_, v_i_boxed_1394_, v_bs_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1397_, v___y_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1401_, v_x_1402_, v___y_1403_, v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v_x_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1409_, lean_object* v_as_x27_1410_, lean_object* v_b_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
if (lean_obj_tag(v_as_x27_1410_) == 0)
{
lean_object* v___x_1419_; 
lean_dec(v_stx_1409_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_b_1411_);
return v___x_1419_;
}
else
{
lean_object* v_head_1420_; lean_object* v_tail_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1463_; 
lean_dec_ref(v_b_1411_);
v_head_1420_ = lean_ctor_get(v_as_x27_1410_, 0);
v_tail_1421_ = lean_ctor_get(v_as_x27_1410_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_as_x27_1410_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1423_ = v_as_x27_1410_;
v_isShared_1424_ = v_isSharedCheck_1463_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_tail_1421_);
lean_inc(v_head_1420_);
lean_dec(v_as_x27_1410_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1463_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_value_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_value_1425_ = lean_ctor_get(v_head_1420_, 1);
lean_inc(v_value_1425_);
lean_dec(v_head_1420_);
v___x_1426_ = lean_box(0);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
lean_inc(v___y_1415_);
lean_inc_ref(v___y_1414_);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc(v_stx_1409_);
v___x_1427_ = lean_apply_8(v_value_1425_, v_stx_1409_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, lean_box(0));
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_tail_1421_);
lean_dec(v_stx_1409_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1439_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1439_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1428_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 0);
lean_ctor_set(v___x_1423_, 1, v___x_1426_);
lean_ctor_set(v___x_1423_, 0, v___x_1432_);
v___x_1434_ = v___x_1423_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1426_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1434_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1462_; 
lean_del_object(v___x_1423_);
v_a_1440_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1442_ = v___x_1427_;
v_isShared_1443_ = v_isSharedCheck_1462_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1427_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1462_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___y_1447_; uint8_t v___x_1460_; 
v___x_1444_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1445_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1460_ = l_Lean_Exception_isInterrupt(v_a_1440_);
if (v___x_1460_ == 0)
{
uint8_t v___x_1461_; 
lean_inc(v_a_1440_);
v___x_1461_ = l_Lean_Exception_isRuntime(v_a_1440_);
v___y_1447_ = v___x_1461_;
goto v___jp_1446_;
}
else
{
v___y_1447_ = v___x_1460_;
goto v___jp_1446_;
}
v___jp_1446_:
{
if (v___y_1447_ == 0)
{
if (lean_obj_tag(v_a_1440_) == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_tail_1421_);
lean_dec(v_stx_1409_);
if (v_isShared_1443_ == 0)
{
v___x_1449_ = v___x_1442_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1440_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
else
{
lean_object* v_id_1451_; uint8_t v___x_1452_; 
v_id_1451_ = lean_ctor_get(v_a_1440_, 0);
v___x_1452_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1445_, v_id_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1454_; 
lean_dec(v_tail_1421_);
lean_dec(v_stx_1409_);
if (v_isShared_1443_ == 0)
{
v___x_1454_ = v___x_1442_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1440_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
else
{
lean_dec_ref(v_a_1440_);
lean_del_object(v___x_1442_);
v_as_x27_1410_ = v_tail_1421_;
v_b_1411_ = v___x_1444_;
goto _start;
}
}
}
else
{
lean_object* v___x_1458_; 
lean_dec(v_tail_1421_);
lean_dec(v_stx_1409_);
if (v_isShared_1443_ == 0)
{
v___x_1458_ = v___x_1442_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1440_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1464_, lean_object* v_as_x27_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1464_, v_as_x27_1465_, v_b_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1477_, lean_object* v_rhs_x3f_1478_, lean_object* v_otherwise_x3f_1479_, lean_object* v_body_x3f_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
uint8_t v___y_1489_; uint8_t v___y_1490_; lean_object* v___y_1491_; uint8_t v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v_body_1499_; lean_object* v___y_1519_; lean_object* v_otherwise_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v_rhs_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; 
if (lean_obj_tag(v_rhs_x3f_1478_) == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v_rhs_1532_ = v___x_1543_;
v___y_1533_ = v_a_1481_;
v___y_1534_ = v_a_1482_;
v___y_1535_ = v_a_1483_;
v___y_1536_ = v_a_1484_;
v___y_1537_ = v_a_1485_;
v___y_1538_ = v_a_1486_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1544_; lean_object* v___x_1545_; 
v_val_1544_ = lean_ctor_get(v_rhs_x3f_1478_, 0);
lean_inc(v_val_1544_);
lean_dec_ref(v_rhs_x3f_1478_);
v___x_1545_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1544_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v_rhs_1532_ = v_a_1546_;
v___y_1533_ = v_a_1481_;
v___y_1534_ = v_a_1482_;
v___y_1535_ = v_a_1483_;
v___y_1536_ = v_a_1484_;
v___y_1537_ = v_a_1485_;
v___y_1538_ = v_a_1486_;
goto v___jp_1531_;
}
else
{
lean_dec(v_body_x3f_1480_);
lean_dec(v_otherwise_x3f_1479_);
lean_dec_ref(v_reassigned_1477_);
return v___x_1545_;
}
}
v___jp_1488_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1494_, 0, v___y_1491_);
lean_ctor_set(v___x_1494_, 1, v___y_1493_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*2, v___y_1492_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*2 + 1, v___y_1490_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*2 + 2, v___y_1489_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
v___jp_1496_:
{
lean_object* v___x_1500_; lean_object* v_info_1501_; uint8_t v_breaks_1502_; uint8_t v_continues_1503_; uint8_t v_returnsEarly_1504_; lean_object* v_numRegularExits_1505_; lean_object* v_reassigns_1506_; size_t v_sz_1507_; size_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1500_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1499_, v___y_1498_);
v_info_1501_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1497_, v___x_1500_);
v_breaks_1502_ = lean_ctor_get_uint8(v_info_1501_, sizeof(void*)*2);
v_continues_1503_ = lean_ctor_get_uint8(v_info_1501_, sizeof(void*)*2 + 1);
v_returnsEarly_1504_ = lean_ctor_get_uint8(v_info_1501_, sizeof(void*)*2 + 2);
v_numRegularExits_1505_ = lean_ctor_get(v_info_1501_, 0);
lean_inc(v_numRegularExits_1505_);
v_reassigns_1506_ = lean_ctor_get(v_info_1501_, 1);
lean_inc(v_reassigns_1506_);
lean_dec_ref(v_info_1501_);
v_sz_1507_ = lean_array_size(v_reassigned_1477_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1507_, v___x_1508_, v_reassigned_1477_);
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = lean_array_get_size(v___x_1509_);
v___x_1512_ = lean_nat_dec_lt(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_dec_ref(v___x_1509_);
v___y_1489_ = v_returnsEarly_1504_;
v___y_1490_ = v_continues_1503_;
v___y_1491_ = v_numRegularExits_1505_;
v___y_1492_ = v_breaks_1502_;
v___y_1493_ = v_reassigns_1506_;
goto v___jp_1488_;
}
else
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_nat_dec_le(v___x_1511_, v___x_1511_);
if (v___x_1513_ == 0)
{
if (v___x_1512_ == 0)
{
lean_dec_ref(v___x_1509_);
v___y_1489_ = v_returnsEarly_1504_;
v___y_1490_ = v_continues_1503_;
v___y_1491_ = v_numRegularExits_1505_;
v___y_1492_ = v_breaks_1502_;
v___y_1493_ = v_reassigns_1506_;
goto v___jp_1488_;
}
else
{
size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_usize_of_nat(v___x_1511_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1509_, v___x_1508_, v___x_1514_, v_reassigns_1506_);
lean_dec_ref(v___x_1509_);
v___y_1489_ = v_returnsEarly_1504_;
v___y_1490_ = v_continues_1503_;
v___y_1491_ = v_numRegularExits_1505_;
v___y_1492_ = v_breaks_1502_;
v___y_1493_ = v___x_1515_;
goto v___jp_1488_;
}
}
else
{
size_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_usize_of_nat(v___x_1511_);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1509_, v___x_1508_, v___x_1516_, v_reassigns_1506_);
lean_dec_ref(v___x_1509_);
v___y_1489_ = v_returnsEarly_1504_;
v___y_1490_ = v_continues_1503_;
v___y_1491_ = v_numRegularExits_1505_;
v___y_1492_ = v_breaks_1502_;
v___y_1493_ = v___x_1517_;
goto v___jp_1488_;
}
}
}
v___jp_1518_:
{
if (lean_obj_tag(v_body_x3f_1480_) == 0)
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___y_1497_ = v___y_1519_;
v___y_1498_ = v_otherwise_1520_;
v_body_1499_ = v___x_1527_;
goto v___jp_1496_;
}
else
{
lean_object* v_val_1528_; lean_object* v___x_1529_; 
v_val_1528_ = lean_ctor_get(v_body_x3f_1480_, 0);
lean_inc(v_val_1528_);
lean_dec_ref(v_body_x3f_1480_);
v___x_1529_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1528_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v___y_1497_ = v___y_1519_;
v___y_1498_ = v_otherwise_1520_;
v_body_1499_ = v_a_1530_;
goto v___jp_1496_;
}
else
{
lean_dec_ref(v_otherwise_1520_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v_reassigned_1477_);
return v___x_1529_;
}
}
}
v___jp_1531_:
{
if (lean_obj_tag(v_otherwise_x3f_1479_) == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___y_1519_ = v_rhs_1532_;
v_otherwise_1520_ = v___x_1539_;
v___y_1521_ = v___y_1533_;
v___y_1522_ = v___y_1534_;
v___y_1523_ = v___y_1535_;
v___y_1524_ = v___y_1536_;
v___y_1525_ = v___y_1537_;
v___y_1526_ = v___y_1538_;
goto v___jp_1518_;
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1541_; 
v_val_1540_ = lean_ctor_get(v_otherwise_x3f_1479_, 0);
lean_inc(v_val_1540_);
lean_dec_ref(v_otherwise_x3f_1479_);
v___x_1541_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1540_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v___y_1519_ = v_rhs_1532_;
v_otherwise_1520_ = v_a_1542_;
v___y_1521_ = v___y_1533_;
v___y_1522_ = v___y_1534_;
v___y_1523_ = v___y_1535_;
v___y_1524_ = v___y_1536_;
v___y_1525_ = v___y_1537_;
v___y_1526_ = v___y_1538_;
goto v___jp_1518_;
}
else
{
lean_dec_ref(v_rhs_1532_);
lean_dec(v_body_x3f_1480_);
lean_dec_ref(v_reassigned_1477_);
return v___x_1541_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1564_ = l_Lean_stringToMessageData(v___x_1563_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1639_ = l_Lean_stringToMessageData(v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1649_, lean_object* v_decl_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v_reassigns_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1650_);
v___x_1687_ = l_Lean_Syntax_isOfKind(v_decl_1650_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1650_);
v___x_1689_ = l_Lean_Syntax_isOfKind(v_decl_1650_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1690_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1691_ = lean_box(0);
v___x_1692_ = l_Lean_Syntax_formatStx(v_decl_1650_, v___x_1691_, v___x_1689_);
v___x_1693_ = l_Std_Format_defWidth;
v___x_1694_ = lean_unsigned_to_nat(0u);
v___x_1695_ = l_Std_Format_pretty(v___x_1692_, v___x_1693_, v___x_1694_, v___x_1694_);
v___x_1696_ = l_Lean_stringToMessageData(v___x_1695_);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1690_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1697_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; lean_object* v_pattern_1700_; lean_object* v___y_1702_; lean_object* v_otherwise_x3f_1703_; lean_object* v_body_x3f_x3f_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v_body_x3f_x3f_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___x_1734_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1699_ = lean_unsigned_to_nat(0u);
v_pattern_1700_ = l_Lean_Syntax_getArg(v_decl_1650_, v___x_1699_);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1773_ = l_Lean_Syntax_getArg(v_decl_1650_, v___x_1734_);
v___x_1774_ = l_Lean_Syntax_isNone(v___x_1773_);
if (v___x_1774_ == 0)
{
uint8_t v___x_1775_; 
lean_inc(v___x_1773_);
v___x_1775_ = l_Lean_Syntax_matchesNull(v___x_1773_, v___x_1734_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1773_);
lean_dec(v_pattern_1700_);
v___x_1776_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Lean_Syntax_formatStx(v_decl_1650_, v___x_1777_, v___x_1775_);
v___x_1779_ = l_Std_Format_defWidth;
v___x_1780_ = l_Std_Format_pretty(v___x_1778_, v___x_1779_, v___x_1699_, v___x_1699_);
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1776_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1782_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1784_ = l_Lean_Syntax_getArg(v___x_1773_, v___x_1699_);
lean_dec(v___x_1773_);
v___x_1785_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1786_ = l_Lean_Syntax_isOfKind(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec(v_pattern_1700_);
v___x_1787_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1788_ = lean_box(0);
v___x_1789_ = l_Lean_Syntax_formatStx(v_decl_1650_, v___x_1788_, v___x_1786_);
v___x_1790_ = l_Std_Format_defWidth;
v___x_1791_ = l_Std_Format_pretty(v___x_1789_, v___x_1790_, v___x_1699_, v___x_1699_);
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1787_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1793_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
return v___x_1794_;
}
else
{
v___y_1736_ = v_a_1651_;
v___y_1737_ = v_a_1652_;
v___y_1738_ = v_a_1653_;
v___y_1739_ = v_a_1654_;
v___y_1740_ = v_a_1655_;
v___y_1741_ = v_a_1656_;
goto v___jp_1735_;
}
}
}
else
{
lean_dec(v___x_1773_);
v___y_1736_ = v_a_1651_;
v___y_1737_ = v_a_1652_;
v___y_1738_ = v_a_1653_;
v___y_1739_ = v_a_1654_;
v___y_1740_ = v_a_1655_;
v___y_1741_ = v_a_1656_;
goto v___jp_1735_;
}
v___jp_1701_:
{
if (v_reassignment_1649_ == 0)
{
lean_object* v___x_1711_; 
lean_dec(v_pattern_1700_);
v___x_1711_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1671_ = v_otherwise_x3f_1703_;
v___y_1672_ = v_body_x3f_x3f_1704_;
v___y_1673_ = v___y_1702_;
v_reassigns_1674_ = v___x_1711_;
v___y_1675_ = v___y_1705_;
v___y_1676_ = v___y_1706_;
v___y_1677_ = v___y_1707_;
v___y_1678_ = v___y_1708_;
v___y_1679_ = v___y_1709_;
v___y_1680_ = v___y_1710_;
goto v___jp_1670_;
}
else
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1700_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v___x_1712_);
v___y_1671_ = v_otherwise_x3f_1703_;
v___y_1672_ = v_body_x3f_x3f_1704_;
v___y_1673_ = v___y_1702_;
v_reassigns_1674_ = v_a_1713_;
v___y_1675_ = v___y_1705_;
v___y_1676_ = v___y_1706_;
v___y_1677_ = v___y_1707_;
v___y_1678_ = v___y_1708_;
v___y_1679_ = v___y_1709_;
v___y_1680_ = v___y_1710_;
goto v___jp_1670_;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_body_x3f_x3f_1704_);
lean_dec(v_otherwise_x3f_1703_);
lean_dec(v___y_1702_);
v_a_1714_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1712_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1712_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
v___jp_1722_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___y_1724_);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_body_x3f_x3f_1725_);
v___y_1702_ = v___y_1723_;
v_otherwise_x3f_1703_ = v___x_1732_;
v_body_x3f_x3f_1704_ = v___x_1733_;
v___y_1705_ = v___y_1726_;
v___y_1706_ = v___y_1727_;
v___y_1707_ = v___y_1728_;
v___y_1708_ = v___y_1729_;
v___y_1709_ = v___y_1730_;
v___y_1710_ = v___y_1731_;
goto v___jp_1701_;
}
v___jp_1735_:
{
lean_object* v___x_1742_; lean_object* v_rhs_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1742_ = lean_unsigned_to_nat(3u);
v_rhs_1743_ = l_Lean_Syntax_getArg(v_decl_1650_, v___x_1742_);
v___x_1744_ = lean_unsigned_to_nat(4u);
v___x_1745_ = l_Lean_Syntax_getArg(v_decl_1650_, v___x_1744_);
v___x_1746_ = l_Lean_Syntax_isNone(v___x_1745_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; 
lean_inc(v___x_1745_);
v___x_1747_ = l_Lean_Syntax_matchesNull(v___x_1745_, v___x_1742_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v___x_1745_);
lean_dec(v_rhs_1743_);
lean_dec(v_pattern_1700_);
v___x_1748_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1749_ = lean_box(0);
v___x_1750_ = l_Lean_Syntax_formatStx(v_decl_1650_, v___x_1749_, v___x_1747_);
v___x_1751_ = l_Std_Format_defWidth;
v___x_1752_ = l_Std_Format_pretty(v___x_1750_, v___x_1751_, v___x_1699_, v___x_1699_);
v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1748_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1754_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; lean_object* v_otherwise_x3f_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1756_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1757_ = l_Lean_Syntax_getArg(v___x_1745_, v___x_1734_);
v___x_1758_ = l_Lean_Syntax_getArg(v___x_1745_, v___x_1756_);
lean_dec(v___x_1745_);
v___x_1759_ = l_Lean_Syntax_isNone(v___x_1758_);
if (v___x_1759_ == 0)
{
uint8_t v___x_1760_; 
lean_inc(v___x_1758_);
v___x_1760_ = l_Lean_Syntax_matchesNull(v___x_1758_, v___x_1734_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v___x_1758_);
lean_dec(v_otherwise_x3f_1757_);
lean_dec(v_rhs_1743_);
lean_dec(v_pattern_1700_);
v___x_1761_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1762_ = lean_box(0);
v___x_1763_ = l_Lean_Syntax_formatStx(v_decl_1650_, v___x_1762_, v___x_1760_);
v___x_1764_ = l_Std_Format_defWidth;
v___x_1765_ = l_Std_Format_pretty(v___x_1763_, v___x_1764_, v___x_1699_, v___x_1699_);
v___x_1766_ = l_Lean_stringToMessageData(v___x_1765_);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1761_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1767_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
return v___x_1768_;
}
else
{
lean_object* v_body_x3f_x3f_1769_; lean_object* v___x_1770_; 
lean_dec(v_decl_1650_);
v_body_x3f_x3f_1769_ = l_Lean_Syntax_getArg(v___x_1758_, v___x_1699_);
lean_dec(v___x_1758_);
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_body_x3f_x3f_1769_);
v___y_1723_ = v_rhs_1743_;
v___y_1724_ = v_otherwise_x3f_1757_;
v_body_x3f_x3f_1725_ = v___x_1770_;
v___y_1726_ = v___y_1736_;
v___y_1727_ = v___y_1737_;
v___y_1728_ = v___y_1738_;
v___y_1729_ = v___y_1739_;
v___y_1730_ = v___y_1740_;
v___y_1731_ = v___y_1741_;
goto v___jp_1722_;
}
}
else
{
lean_object* v___x_1771_; 
lean_dec(v___x_1758_);
lean_dec(v_decl_1650_);
v___x_1771_ = lean_box(0);
v___y_1723_ = v_rhs_1743_;
v___y_1724_ = v_otherwise_x3f_1757_;
v_body_x3f_x3f_1725_ = v___x_1771_;
v___y_1726_ = v___y_1736_;
v___y_1727_ = v___y_1737_;
v___y_1728_ = v___y_1738_;
v___y_1729_ = v___y_1739_;
v___y_1730_ = v___y_1740_;
v___y_1731_ = v___y_1741_;
goto v___jp_1722_;
}
}
}
else
{
lean_object* v___x_1772_; 
lean_dec(v___x_1745_);
lean_dec(v_decl_1650_);
v___x_1772_ = lean_box(0);
v___y_1702_ = v_rhs_1743_;
v_otherwise_x3f_1703_ = v___x_1772_;
v_body_x3f_x3f_1704_ = v___x_1772_;
v___y_1705_ = v___y_1736_;
v___y_1706_ = v___y_1737_;
v___y_1707_ = v___y_1738_;
v___y_1708_ = v___y_1739_;
v___y_1709_ = v___y_1740_;
v___y_1710_ = v___y_1741_;
goto v___jp_1701_;
}
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v_x_1796_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1795_ = lean_unsigned_to_nat(0u);
v_x_1796_ = l_Lean_Syntax_getArg(v_decl_1650_, v___x_1795_);
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1796_);
v___x_1811_ = l_Lean_Syntax_isOfKind(v_x_1796_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec(v_x_1796_);
v___x_1812_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1813_ = lean_box(0);
v___x_1814_ = l_Lean_Syntax_formatStx(v_decl_1650_, v___x_1813_, v___x_1811_);
v___x_1815_ = l_Std_Format_defWidth;
v___x_1816_ = l_Std_Format_pretty(v___x_1814_, v___x_1815_, v___x_1795_, v___x_1795_);
v___x_1817_ = l_Lean_stringToMessageData(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1812_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1818_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = l_Lean_Syntax_getArg(v_decl_1650_, v___x_1820_);
v___x_1822_ = l_Lean_Syntax_isNone(v___x_1821_);
if (v___x_1822_ == 0)
{
uint8_t v___x_1823_; 
lean_inc(v___x_1821_);
v___x_1823_ = l_Lean_Syntax_matchesNull(v___x_1821_, v___x_1820_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec(v___x_1821_);
lean_dec(v_x_1796_);
v___x_1824_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1825_ = lean_box(0);
v___x_1826_ = l_Lean_Syntax_formatStx(v_decl_1650_, v___x_1825_, v___x_1823_);
v___x_1827_ = l_Std_Format_defWidth;
v___x_1828_ = l_Std_Format_pretty(v___x_1826_, v___x_1827_, v___x_1795_, v___x_1795_);
v___x_1829_ = l_Lean_stringToMessageData(v___x_1828_);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1824_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1830_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1832_ = l_Lean_Syntax_getArg(v___x_1821_, v___x_1795_);
lean_dec(v___x_1821_);
v___x_1833_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1834_ = l_Lean_Syntax_isOfKind(v___x_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec(v_x_1796_);
v___x_1835_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1836_ = lean_box(0);
v___x_1837_ = l_Lean_Syntax_formatStx(v_decl_1650_, v___x_1836_, v___x_1834_);
v___x_1838_ = l_Std_Format_defWidth;
v___x_1839_ = l_Std_Format_pretty(v___x_1837_, v___x_1838_, v___x_1795_, v___x_1795_);
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1835_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1841_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
return v___x_1842_;
}
else
{
v___y_1798_ = v_a_1651_;
v___y_1799_ = v_a_1652_;
v___y_1800_ = v_a_1653_;
v___y_1801_ = v_a_1654_;
v___y_1802_ = v_a_1655_;
v___y_1803_ = v_a_1656_;
goto v___jp_1797_;
}
}
}
else
{
lean_dec(v___x_1821_);
v___y_1798_ = v_a_1651_;
v___y_1799_ = v_a_1652_;
v___y_1800_ = v_a_1653_;
v___y_1801_ = v_a_1654_;
v___y_1802_ = v_a_1655_;
v___y_1803_ = v_a_1656_;
goto v___jp_1797_;
}
}
v___jp_1797_:
{
lean_object* v___x_1804_; lean_object* v_rhs_1805_; 
v___x_1804_ = lean_unsigned_to_nat(3u);
v_rhs_1805_ = l_Lean_Syntax_getArg(v_decl_1650_, v___x_1804_);
lean_dec(v_decl_1650_);
if (v_reassignment_1649_ == 0)
{
lean_object* v___x_1806_; 
lean_dec(v_x_1796_);
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1659_ = v___y_1798_;
v___y_1660_ = v___y_1801_;
v___y_1661_ = v___y_1799_;
v___y_1662_ = v___y_1803_;
v___y_1663_ = v_rhs_1805_;
v___y_1664_ = v___y_1800_;
v___y_1665_ = v___y_1802_;
v___y_1666_ = v___x_1806_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = lean_unsigned_to_nat(1u);
v___x_1808_ = lean_mk_empty_array_with_capacity(v___x_1807_);
v___x_1809_ = lean_array_push(v___x_1808_, v_x_1796_);
v___y_1659_ = v___y_1798_;
v___y_1660_ = v___y_1801_;
v___y_1661_ = v___y_1799_;
v___y_1662_ = v___y_1803_;
v___y_1663_ = v_rhs_1805_;
v___y_1664_ = v___y_1800_;
v___y_1665_ = v___y_1802_;
v___y_1666_ = v___x_1809_;
goto v___jp_1658_;
}
}
}
v___jp_1658_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___y_1663_);
v___x_1668_ = lean_box(0);
v___x_1669_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1666_, v___x_1667_, v___x_1668_, v___x_1668_, v___y_1659_, v___y_1661_, v___y_1664_, v___y_1660_, v___y_1665_, v___y_1662_);
return v___x_1669_;
}
v___jp_1670_:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___y_1673_);
if (lean_obj_tag(v___y_1672_) == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_box(0);
v___x_1683_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1674_, v___x_1681_, v___y_1671_, v___x_1682_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1683_;
}
else
{
lean_object* v_val_1684_; lean_object* v___x_1685_; 
v_val_1684_ = lean_ctor_get(v___y_1672_, 0);
lean_inc(v_val_1684_);
lean_dec_ref(v___y_1672_);
v___x_1685_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1674_, v___x_1681_, v___y_1671_, v_val_1684_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1951_, size_t v_sz_1952_, size_t v_i_1953_, lean_object* v_b_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_usize_dec_lt(v_i_1953_, v_sz_1952_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v_b_1954_);
return v___x_1963_;
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1965_; 
v_a_1964_ = lean_array_uget_borrowed(v_as_1951_, v_i_1953_);
lean_inc(v_a_1964_);
v___x_1965_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1964_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; size_t v___x_1968_; size_t v___x_1969_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1966_, v_b_1954_);
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_add(v_i_1953_, v___x_1968_);
v_i_1953_ = v___x_1969_;
v_b_1954_ = v___x_1967_;
goto _start;
}
else
{
lean_dec_ref(v_b_1954_);
return v___x_1965_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_1985_ = l_Lean_stringToMessageData(v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2000_, lean_object* v_as_2001_, size_t v_sz_2002_, size_t v_i_2003_, lean_object* v_b_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_a_2013_; uint8_t v___x_2017_; 
v___x_2017_ = lean_usize_dec_lt(v_i_2003_, v_sz_2002_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_b_2004_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; lean_object* v_a_2020_; uint8_t v___x_2021_; 
v___x_2019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2020_ = lean_array_uget_borrowed(v_as_2001_, v_i_2003_);
lean_inc(v_a_2020_);
v___x_2021_ = l_Lean_Syntax_isOfKind(v_a_2020_, v___x_2019_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_dec_ref(v___x_2022_);
v_a_2013_ = v_b_2004_;
goto v___jp_2012_;
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_b_2004_);
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___y_2034_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2031_ = lean_unsigned_to_nat(1u);
v___x_2032_ = lean_unsigned_to_nat(3u);
v___x_2051_ = l_Lean_Syntax_getArg(v_a_2020_, v___x_2031_);
v___x_2052_ = l_Lean_Syntax_getArgs(v___x_2051_);
lean_dec(v___x_2051_);
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2055_ = lean_array_get_size(v___x_2052_);
v___x_2056_ = lean_nat_dec_lt(v___x_2053_, v___x_2055_);
if (v___x_2056_ == 0)
{
lean_dec_ref(v___x_2052_);
v___y_2034_ = v___x_2054_;
goto v___jp_2033_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_box(v___x_2021_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v___x_2054_);
v___x_2059_ = lean_nat_dec_le(v___x_2055_, v___x_2055_);
if (v___x_2059_ == 0)
{
if (v___x_2056_ == 0)
{
lean_dec_ref(v___x_2058_);
lean_dec_ref(v___x_2052_);
v___y_2034_ = v___x_2054_;
goto v___jp_2033_;
}
else
{
size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; lean_object* v_snd_2063_; 
v___x_2060_ = ((size_t)0ULL);
v___x_2061_ = lean_usize_of_nat(v___x_2055_);
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2021_, v___x_2000_, v___x_2052_, v___x_2060_, v___x_2061_, v___x_2058_);
lean_dec_ref(v___x_2052_);
v_snd_2063_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_snd_2063_);
lean_dec_ref(v___x_2062_);
v___y_2034_ = v_snd_2063_;
goto v___jp_2033_;
}
}
else
{
size_t v___x_2064_; size_t v___x_2065_; lean_object* v___x_2066_; lean_object* v_snd_2067_; 
v___x_2064_ = ((size_t)0ULL);
v___x_2065_ = lean_usize_of_nat(v___x_2055_);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2021_, v___x_2000_, v___x_2052_, v___x_2064_, v___x_2065_, v___x_2058_);
lean_dec_ref(v___x_2052_);
v_snd_2067_ = lean_ctor_get(v___x_2066_, 1);
lean_inc(v_snd_2067_);
lean_dec_ref(v___x_2066_);
v___y_2034_ = v_snd_2067_;
goto v___jp_2033_;
}
}
v___jp_2033_:
{
size_t v_sz_2035_; size_t v___x_2036_; lean_object* v___x_2037_; 
v_sz_2035_ = lean_array_size(v___y_2034_);
v___x_2036_ = ((size_t)0ULL);
v___x_2037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2035_, v___x_2036_, v___y_2034_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_dec_ref(v___x_2038_);
v_a_2013_ = v_b_2004_;
goto v___jp_2012_;
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_b_2004_);
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v___x_2037_);
v___x_2047_ = l_Lean_Syntax_getArg(v_a_2020_, v___x_2032_);
v___x_2048_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2047_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2004_, v_a_2049_);
v_a_2013_ = v___x_2050_;
goto v___jp_2012_;
}
else
{
lean_dec_ref(v_b_2004_);
return v___x_2048_;
}
}
}
}
}
v___jp_2012_:
{
size_t v___x_2014_; size_t v___x_2015_; 
v___x_2014_ = ((size_t)1ULL);
v___x_2015_ = lean_usize_add(v_i_2003_, v___x_2014_);
v_i_2003_ = v___x_2015_;
v_b_2004_ = v_a_2013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2068_, size_t v_sz_2069_, size_t v_i_2070_, lean_object* v_b_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_a_2080_; uint8_t v___x_2084_; 
v___x_2084_ = lean_usize_dec_lt(v_i_2070_, v_sz_2069_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_b_2071_);
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; lean_object* v_a_2087_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2086_ = lean_unsigned_to_nat(0u);
v_a_2087_ = lean_array_uget_borrowed(v_as_2068_, v_i_2070_);
v___x_2100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2087_);
v___x_2101_ = l_Lean_Syntax_isOfKind(v_a_2087_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2087_);
v___x_2103_ = l_Lean_Syntax_isOfKind(v_a_2087_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2104_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2105_ = lean_box(0);
lean_inc(v_a_2087_);
v___x_2106_ = l_Lean_Syntax_formatStx(v_a_2087_, v___x_2105_, v___x_2103_);
v___x_2107_ = l_Std_Format_defWidth;
v___x_2108_ = l_Std_Format_pretty(v___x_2106_, v___x_2107_, v___x_2086_, v___x_2086_);
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2104_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2110_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_dec_ref(v___x_2111_);
v_a_2080_ = v_b_2071_;
goto v___jp_2079_;
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_b_2071_);
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2120_ = lean_unsigned_to_nat(1u);
v___x_2121_ = l_Lean_Syntax_getArg(v_a_2087_, v___x_2120_);
v___x_2122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2121_);
v___x_2123_ = l_Lean_Syntax_isOfKind(v___x_2121_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec(v___x_2121_);
v___x_2124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2125_ = lean_box(0);
lean_inc(v_a_2087_);
v___x_2126_ = l_Lean_Syntax_formatStx(v_a_2087_, v___x_2125_, v___x_2123_);
v___x_2127_ = l_Std_Format_defWidth;
v___x_2128_ = l_Std_Format_pretty(v___x_2126_, v___x_2127_, v___x_2086_, v___x_2086_);
v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2124_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2130_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_dec_ref(v___x_2131_);
v_a_2080_ = v_b_2071_;
goto v___jp_2079_;
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v_b_2071_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; size_t v_sz_2142_; size_t v___x_2143_; lean_object* v___x_2144_; 
v___x_2140_ = l_Lean_Syntax_getArg(v___x_2121_, v___x_2086_);
lean_dec(v___x_2121_);
v___x_2141_ = l_Lean_Syntax_getArgs(v___x_2140_);
lean_dec(v___x_2140_);
v_sz_2142_ = lean_array_size(v___x_2141_);
v___x_2143_ = ((size_t)0ULL);
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2101_, v___x_2141_, v_sz_2142_, v___x_2143_, v_b_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec_ref(v___x_2141_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
v_a_2080_ = v_a_2145_;
goto v___jp_2079_;
}
else
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2146_ = lean_unsigned_to_nat(2u);
v___x_2147_ = l_Lean_Syntax_getArg(v_a_2087_, v___x_2146_);
v___x_2148_ = l_Lean_Syntax_isNone(v___x_2147_);
if (v___x_2148_ == 0)
{
uint8_t v___x_2149_; 
v___x_2149_ = l_Lean_Syntax_matchesNull(v___x_2147_, v___x_2146_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2150_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2151_ = lean_box(0);
lean_inc(v_a_2087_);
v___x_2152_ = l_Lean_Syntax_formatStx(v_a_2087_, v___x_2151_, v___x_2149_);
v___x_2153_ = l_Std_Format_defWidth;
v___x_2154_ = l_Std_Format_pretty(v___x_2152_, v___x_2153_, v___x_2086_, v___x_2086_);
v___x_2155_ = l_Lean_stringToMessageData(v___x_2154_);
v___x_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2150_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2156_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_dec_ref(v___x_2157_);
v_a_2080_ = v_b_2071_;
goto v___jp_2079_;
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec_ref(v_b_2071_);
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
v___y_2089_ = v___y_2072_;
v___y_2090_ = v___y_2073_;
v___y_2091_ = v___y_2074_;
v___y_2092_ = v___y_2075_;
v___y_2093_ = v___y_2076_;
v___y_2094_ = v___y_2077_;
goto v___jp_2088_;
}
}
else
{
lean_dec(v___x_2147_);
v___y_2089_ = v___y_2072_;
v___y_2090_ = v___y_2073_;
v___y_2091_ = v___y_2074_;
v___y_2092_ = v___y_2075_;
v___y_2093_ = v___y_2076_;
v___y_2094_ = v___y_2077_;
goto v___jp_2088_;
}
}
v___jp_2088_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = lean_unsigned_to_nat(4u);
v___x_2096_ = l_Lean_Syntax_getArg(v_a_2087_, v___x_2095_);
v___x_2097_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2096_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2097_);
v___x_2099_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2098_, v_b_2071_);
v_a_2080_ = v___x_2099_;
goto v___jp_2079_;
}
else
{
lean_dec_ref(v_b_2071_);
return v___x_2097_;
}
}
}
v___jp_2079_:
{
size_t v___x_2081_; size_t v___x_2082_; 
v___x_2081_ = ((size_t)1ULL);
v___x_2082_ = lean_usize_add(v_i_2070_, v___x_2081_);
v_i_2070_ = v___x_2082_;
v_b_2071_ = v_a_2080_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2166_) == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
return v___x_2175_;
}
else
{
lean_object* v_val_2176_; lean_object* v___x_2177_; 
v_val_2176_ = lean_ctor_get(v_stx_x3f_2166_, 0);
lean_inc(v_val_2176_);
lean_dec_ref(v_stx_x3f_2166_);
v___x_2177_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2176_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2184_, lean_object* v_as_2185_, size_t v_sz_2186_, size_t v_i_2187_, lean_object* v_b_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_a_2197_; uint8_t v___x_2201_; 
v___x_2201_ = lean_usize_dec_lt(v_i_2187_, v_sz_2186_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v_b_2188_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v_a_2204_; uint8_t v___x_2205_; 
v___x_2203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2204_ = lean_array_uget_borrowed(v_as_2185_, v_i_2187_);
lean_inc(v_a_2204_);
v___x_2205_ = l_Lean_Syntax_isOfKind(v_a_2204_, v___x_2203_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_dec_ref(v___x_2206_);
v_a_2197_ = v_b_2188_;
goto v___jp_2196_;
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v_b_2188_);
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___y_2218_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2215_ = lean_unsigned_to_nat(1u);
v___x_2216_ = lean_unsigned_to_nat(3u);
v___x_2235_ = l_Lean_Syntax_getArg(v_a_2204_, v___x_2215_);
v___x_2236_ = l_Lean_Syntax_getArgs(v___x_2235_);
lean_dec(v___x_2235_);
v___x_2237_ = lean_unsigned_to_nat(0u);
v___x_2238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2239_ = lean_array_get_size(v___x_2236_);
v___x_2240_ = lean_nat_dec_lt(v___x_2237_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_dec_ref(v___x_2236_);
v___y_2218_ = v___x_2238_;
goto v___jp_2217_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2241_ = lean_box(v___x_2205_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2238_);
v___x_2243_ = lean_nat_dec_le(v___x_2239_, v___x_2239_);
if (v___x_2243_ == 0)
{
if (v___x_2240_ == 0)
{
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2236_);
v___y_2218_ = v___x_2238_;
goto v___jp_2217_;
}
else
{
size_t v___x_2244_; size_t v___x_2245_; lean_object* v___x_2246_; lean_object* v_snd_2247_; 
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = lean_usize_of_nat(v___x_2239_);
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2205_, v___x_2184_, v___x_2236_, v___x_2244_, v___x_2245_, v___x_2242_);
lean_dec_ref(v___x_2236_);
v_snd_2247_ = lean_ctor_get(v___x_2246_, 1);
lean_inc(v_snd_2247_);
lean_dec_ref(v___x_2246_);
v___y_2218_ = v_snd_2247_;
goto v___jp_2217_;
}
}
else
{
size_t v___x_2248_; size_t v___x_2249_; lean_object* v___x_2250_; lean_object* v_snd_2251_; 
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = lean_usize_of_nat(v___x_2239_);
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2205_, v___x_2184_, v___x_2236_, v___x_2248_, v___x_2249_, v___x_2242_);
lean_dec_ref(v___x_2236_);
v_snd_2251_ = lean_ctor_get(v___x_2250_, 1);
lean_inc(v_snd_2251_);
lean_dec_ref(v___x_2250_);
v___y_2218_ = v_snd_2251_;
goto v___jp_2217_;
}
}
v___jp_2217_:
{
size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v_sz_2219_ = lean_array_size(v___y_2218_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2219_, v___x_2220_, v___y_2218_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_dec_ref(v___x_2222_);
v_a_2197_ = v_b_2188_;
goto v___jp_2196_;
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_b_2188_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_dec_ref(v___x_2221_);
v___x_2231_ = l_Lean_Syntax_getArg(v_a_2204_, v___x_2216_);
v___x_2232_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2231_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2188_, v_a_2233_);
v_a_2197_ = v___x_2234_;
goto v___jp_2196_;
}
else
{
lean_dec_ref(v_b_2188_);
return v___x_2232_;
}
}
}
}
}
v___jp_2196_:
{
size_t v___x_2198_; size_t v___x_2199_; 
v___x_2198_ = ((size_t)1ULL);
v___x_2199_ = lean_usize_add(v_i_2187_, v___x_2198_);
v_i_2187_ = v___x_2199_;
v_b_2188_ = v_a_2197_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; 
v___x_2288_ = l_Lean_NameSet_empty;
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = 0;
v___x_2291_ = 1;
v___x_2292_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2292_, 0, v___x_2289_);
lean_ctor_set(v___x_2292_, 1, v___x_2288_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*2, v___x_2291_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*2 + 1, v___x_2290_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*2 + 2, v___x_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2315_; lean_object* v_bodyInfo_2316_; lean_object* v___y_2320_; lean_object* v_bodyInfo_2321_; lean_object* v___x_2324_; lean_object* v_env_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2324_ = lean_st_ref_get(v_a_2299_);
v_env_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc_ref(v_env_2325_);
lean_dec(v___x_2324_);
lean_inc(v_stx_2293_);
v___x_2326_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2326_, 0, v_env_2325_);
lean_closure_set(v___x_2326_, 1, v_stx_2293_);
v___x_2327_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2326_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_4380_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_4380_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_4380_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
if (lean_obj_tag(v_a_2328_) == 1)
{
lean_object* v_val_2332_; lean_object* v_snd_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_del_object(v___x_2330_);
lean_dec(v_stx_2293_);
v_val_2332_ = lean_ctor_get(v_a_2328_, 0);
lean_inc(v_val_2332_);
lean_dec_ref(v_a_2328_);
v_snd_2333_ = lean_ctor_get(v_val_2332_, 1);
lean_inc(v_snd_2333_);
lean_dec(v_val_2332_);
v___x_2334_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2334_, 0, lean_box(0));
lean_closure_set(v___x_2334_, 1, v_snd_2333_);
v___x_2335_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2334_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v___x_2335_);
v_stx_2293_ = v_a_2336_;
goto _start;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
v_a_2338_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2335_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2335_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___x_2528_; uint8_t v___x_2529_; uint8_t v___x_2530_; 
lean_dec(v_a_2328_);
v___x_2528_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2293_);
v___x_2529_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2528_);
v___x_2530_ = 1;
if (v___x_2529_ == 0)
{
lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2293_);
v___x_2532_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2293_);
v___x_2534_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2535_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2293_);
v___x_2536_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2293_);
v___x_2538_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2293_);
v___x_2540_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
lean_del_object(v___x_2330_);
v___x_2541_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2293_);
v___x_2542_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2543_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2293_);
v___x_2544_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; uint8_t v___x_2546_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; 
v___x_2545_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2293_);
v___x_2546_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2293_);
v___x_2608_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2293_);
v___x_2610_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2611_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2293_);
v___x_2612_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2613_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2293_);
v___x_2614_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2293_);
v___x_2616_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2293_);
v___x_2618_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; uint8_t v___x_2620_; 
v___x_2619_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2293_);
v___x_2620_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2293_);
v___x_2622_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2293_);
v___x_2624_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2625_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2293_);
v___x_2626_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51));
lean_inc(v_stx_2293_);
v___x_2628_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53));
lean_inc(v_stx_2293_);
v___x_2630_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55));
lean_inc(v_stx_2293_);
v___x_2632_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57));
lean_inc(v_stx_2293_);
v___x_2634_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59));
lean_inc(v_stx_2293_);
v___x_2636_ = l_Lean_Syntax_isOfKind(v_stx_2293_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; lean_object* v_env_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2637_ = lean_st_ref_get(v_a_2299_);
v_env_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc_ref(v_env_2638_);
lean_dec(v___x_2637_);
lean_inc_n(v_stx_2293_, 2);
v___x_2639_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2640_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2641_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2640_, v_env_2638_, v___x_2639_);
v___x_2642_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2643_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2641_, v___x_2642_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2674_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2674_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2674_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_fst_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2672_; 
v_fst_2648_ = lean_ctor_get(v_a_2644_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_a_2644_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; 
v_unused_2673_ = lean_ctor_get(v_a_2644_, 1);
lean_dec(v_unused_2673_);
v___x_2650_ = v_a_2644_;
v_isShared_2651_ = v_isSharedCheck_2672_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_fst_2648_);
lean_dec(v_a_2644_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2672_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
if (lean_obj_tag(v_fst_2648_) == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
lean_del_object(v___x_2646_);
v___x_2652_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2653_ = l_Lean_MessageData_ofName(v___x_2639_);
lean_inc_ref(v___x_2653_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set_tag(v___x_2650_, 7);
lean_ctor_set(v___x_2650_, 1, v___x_2653_);
lean_ctor_set(v___x_2650_, 0, v___x_2652_);
v___x_2655_ = v___x_2650_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2656_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2659_ = l_Lean_indentD(v___x_2658_);
v___x_2660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2657_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2660_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
lean_ctor_set(v___x_2663_, 1, v___x_2653_);
v___x_2664_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2665_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2666_;
}
}
else
{
lean_object* v_val_2668_; lean_object* v___x_2670_; 
lean_del_object(v___x_2650_);
lean_dec(v___x_2639_);
lean_dec(v_stx_2293_);
v_val_2668_ = lean_ctor_get(v_fst_2648_, 0);
lean_inc(v_val_2668_);
lean_dec_ref(v_fst_2648_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v_val_2668_);
v___x_2670_ = v___x_2646_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_val_2668_);
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
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v___x_2639_);
lean_dec(v_stx_2293_);
v_a_2675_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2643_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2643_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___y_2687_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2683_ = lean_unsigned_to_nat(1u);
v___x_2684_ = lean_unsigned_to_nat(5u);
v___x_2685_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2684_);
v___x_2696_ = lean_unsigned_to_nat(6u);
v___x_2697_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2696_);
lean_dec(v_stx_2293_);
v___x_2698_ = l_Lean_Syntax_getOptional_x3f(v___x_2697_);
lean_dec(v___x_2697_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_box(0);
v___y_2687_ = v___x_2699_;
goto v___jp_2686_;
}
else
{
lean_object* v_val_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
v_val_2700_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2698_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_val_2700_);
lean_dec(v___x_2698_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_val_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
v___y_2687_ = v___x_2705_;
goto v___jp_2686_;
}
}
}
v___jp_2686_:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2685_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2688_) == 0)
{
if (lean_obj_tag(v___y_2687_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref(v___x_2688_);
v___x_2690_ = l_Lean_NameSet_empty;
v___x_2691_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2691_, 0, v___x_2683_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
lean_ctor_set_uint8(v___x_2691_, sizeof(void*)*2, v___x_2634_);
lean_ctor_set_uint8(v___x_2691_, sizeof(void*)*2 + 1, v___x_2634_);
lean_ctor_set_uint8(v___x_2691_, sizeof(void*)*2 + 2, v___x_2634_);
v___y_2315_ = v_a_2689_;
v_bodyInfo_2316_ = v___x_2691_;
goto v___jp_2314_;
}
else
{
lean_object* v_a_2692_; lean_object* v_val_2693_; lean_object* v___x_2694_; 
v_a_2692_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2688_);
v_val_2693_ = lean_ctor_get(v___y_2687_, 0);
lean_inc(v_val_2693_);
lean_dec_ref(v___y_2687_);
v___x_2694_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2693_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref(v___x_2694_);
v___y_2315_ = v_a_2692_;
v_bodyInfo_2316_ = v_a_2695_;
goto v___jp_2314_;
}
else
{
lean_dec(v_a_2692_);
return v___x_2694_;
}
}
}
else
{
lean_dec(v___y_2687_);
return v___x_2688_;
}
}
}
}
else
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___y_2712_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2709_ = lean_unsigned_to_nat(5u);
v___x_2710_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2709_);
v___x_2721_ = lean_unsigned_to_nat(6u);
v___x_2722_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2721_);
lean_dec(v_stx_2293_);
v___x_2723_ = l_Lean_Syntax_getOptional_x3f(v___x_2722_);
lean_dec(v___x_2722_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_box(0);
v___y_2712_ = v___x_2724_;
goto v___jp_2711_;
}
else
{
lean_object* v_val_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
v_val_2725_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2723_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_val_2725_);
lean_dec(v___x_2723_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_val_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
v___y_2712_ = v___x_2730_;
goto v___jp_2711_;
}
}
}
v___jp_2711_:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2710_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2713_) == 0)
{
if (lean_obj_tag(v___y_2712_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref(v___x_2713_);
v___x_2715_ = l_Lean_NameSet_empty;
v___x_2716_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_2716_, 0, v___x_2708_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*2, v___x_2632_);
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*2 + 1, v___x_2632_);
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*2 + 2, v___x_2632_);
v___y_2320_ = v_a_2714_;
v_bodyInfo_2321_ = v___x_2716_;
goto v___jp_2319_;
}
else
{
lean_object* v_a_2717_; lean_object* v_val_2718_; lean_object* v___x_2719_; 
v_a_2717_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2717_);
lean_dec_ref(v___x_2713_);
v_val_2718_ = lean_ctor_get(v___y_2712_, 0);
lean_inc(v_val_2718_);
lean_dec_ref(v___y_2712_);
v___x_2719_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2718_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref(v___x_2719_);
v___y_2320_ = v_a_2717_;
v_bodyInfo_2321_ = v_a_2720_;
goto v___jp_2319_;
}
else
{
lean_dec(v_a_2717_);
return v___x_2719_;
}
}
}
else
{
lean_dec(v___y_2712_);
return v___x_2713_;
}
}
}
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2733_ = lean_unsigned_to_nat(0u);
v___x_2734_ = lean_unsigned_to_nat(1u);
v___x_2948_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2734_);
v___x_2949_ = l_Lean_Syntax_isNone(v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2950_ = lean_unsigned_to_nat(5u);
v___x_2951_ = l_Lean_Syntax_matchesNull(v___x_2948_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v_env_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2952_ = lean_st_ref_get(v_a_2299_);
v_env_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc_ref(v_env_2953_);
lean_dec(v___x_2952_);
lean_inc_n(v_stx_2293_, 2);
v___x_2954_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2955_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2956_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2955_, v_env_2953_, v___x_2954_);
v___x_2957_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2958_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2956_, v___x_2957_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2989_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2989_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2989_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v_fst_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2987_; 
v_fst_2963_ = lean_ctor_get(v_a_2959_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_a_2959_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v_a_2959_, 1);
lean_dec(v_unused_2988_);
v___x_2965_ = v_a_2959_;
v_isShared_2966_ = v_isSharedCheck_2987_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_fst_2963_);
lean_dec(v_a_2959_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2987_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
if (lean_obj_tag(v_fst_2963_) == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2970_; 
lean_del_object(v___x_2961_);
v___x_2967_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2968_ = l_Lean_MessageData_ofName(v___x_2954_);
lean_inc_ref(v___x_2968_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 7);
lean_ctor_set(v___x_2965_, 1, v___x_2968_);
lean_ctor_set(v___x_2965_, 0, v___x_2967_);
v___x_2970_ = v___x_2965_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2971_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2974_ = l_Lean_indentD(v___x_2973_);
v___x_2975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2972_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2975_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v___x_2968_);
v___x_2979_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2978_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2980_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2981_;
}
}
else
{
lean_object* v_val_2983_; lean_object* v___x_2985_; 
lean_del_object(v___x_2965_);
lean_dec(v___x_2954_);
lean_dec(v_stx_2293_);
v_val_2983_ = lean_ctor_get(v_fst_2963_, 0);
lean_inc(v_val_2983_);
lean_dec_ref(v_fst_2963_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v_val_2983_);
v___x_2985_ = v___x_2961_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_val_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v___x_2954_);
lean_dec(v_stx_2293_);
v_a_2990_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2958_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2958_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
v___y_2736_ = v_a_2294_;
v___y_2737_ = v_a_2295_;
v___y_2738_ = v_a_2296_;
v___y_2739_ = v_a_2297_;
v___y_2740_ = v_a_2298_;
v___y_2741_ = v_a_2299_;
goto v___jp_2735_;
}
}
else
{
lean_dec(v___x_2948_);
v___y_2736_ = v_a_2294_;
v___y_2737_ = v_a_2295_;
v___y_2738_ = v_a_2296_;
v___y_2739_ = v_a_2297_;
v___y_2740_ = v_a_2298_;
v___y_2741_ = v_a_2299_;
goto v___jp_2735_;
}
v___jp_2735_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v___x_2742_ = lean_unsigned_to_nat(4u);
v___x_2743_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2742_);
v___x_2744_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61));
lean_inc(v___x_2743_);
v___x_2745_ = l_Lean_Syntax_isOfKind(v___x_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; lean_object* v_env_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec(v___x_2743_);
v___x_2746_ = lean_st_ref_get(v___y_2741_);
v_env_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc_ref(v_env_2747_);
lean_dec(v___x_2746_);
lean_inc_n(v_stx_2293_, 2);
v___x_2748_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2749_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2750_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2749_, v_env_2747_, v___x_2748_);
v___x_2751_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2752_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2750_, v___x_2751_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2783_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2755_ = v___x_2752_;
v_isShared_2756_ = v_isSharedCheck_2783_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2783_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v_fst_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2781_; 
v_fst_2757_ = lean_ctor_get(v_a_2753_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_a_2753_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; 
v_unused_2782_ = lean_ctor_get(v_a_2753_, 1);
lean_dec(v_unused_2782_);
v___x_2759_ = v_a_2753_;
v_isShared_2760_ = v_isSharedCheck_2781_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_fst_2757_);
lean_dec(v_a_2753_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2781_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
if (lean_obj_tag(v_fst_2757_) == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
lean_del_object(v___x_2755_);
v___x_2761_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2762_ = l_Lean_MessageData_ofName(v___x_2748_);
lean_inc_ref(v___x_2762_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 7);
lean_ctor_set(v___x_2759_, 1, v___x_2762_);
lean_ctor_set(v___x_2759_, 0, v___x_2761_);
v___x_2764_ = v___x_2759_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2765_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2768_ = l_Lean_indentD(v___x_2767_);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2766_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v___x_2762_);
v___x_2773_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2774_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2775_;
}
}
else
{
lean_object* v_val_2777_; lean_object* v___x_2779_; 
lean_del_object(v___x_2759_);
lean_dec(v___x_2748_);
lean_dec(v_stx_2293_);
v_val_2777_ = lean_ctor_get(v_fst_2757_, 0);
lean_inc(v_val_2777_);
lean_dec_ref(v_fst_2757_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v_val_2777_);
v___x_2779_ = v___x_2755_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_val_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v___x_2748_);
lean_dec(v_stx_2293_);
v_a_2784_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2752_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2752_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; size_t v_sz_2794_; size_t v___x_2795_; lean_object* v___x_2796_; 
v___x_2792_ = l_Lean_Syntax_getArg(v___x_2743_, v___x_2733_);
v___x_2793_ = l_Lean_Syntax_getArgs(v___x_2792_);
lean_dec(v___x_2792_);
v_sz_2794_ = lean_array_size(v___x_2793_);
v___x_2795_ = ((size_t)0ULL);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2794_, v___x_2795_, v___x_2793_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v___x_2797_; lean_object* v_env_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
lean_dec(v___x_2743_);
v___x_2797_ = lean_st_ref_get(v___y_2741_);
v_env_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc_ref(v_env_2798_);
lean_dec(v___x_2797_);
lean_inc_n(v_stx_2293_, 2);
v___x_2799_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2800_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2801_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2800_, v_env_2798_, v___x_2799_);
v___x_2802_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2803_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2801_, v___x_2802_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2834_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2834_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2834_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v_fst_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2832_; 
v_fst_2808_ = lean_ctor_get(v_a_2804_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_a_2804_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v_a_2804_, 1);
lean_dec(v_unused_2833_);
v___x_2810_ = v_a_2804_;
v_isShared_2811_ = v_isSharedCheck_2832_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_fst_2808_);
lean_dec(v_a_2804_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2832_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
if (lean_obj_tag(v_fst_2808_) == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
lean_del_object(v___x_2806_);
v___x_2812_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2813_ = l_Lean_MessageData_ofName(v___x_2799_);
lean_inc_ref(v___x_2813_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 7);
lean_ctor_set(v___x_2810_, 1, v___x_2813_);
lean_ctor_set(v___x_2810_, 0, v___x_2812_);
v___x_2815_ = v___x_2810_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2816_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2819_ = l_Lean_indentD(v___x_2818_);
v___x_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2817_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v___x_2813_);
v___x_2824_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2825_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2826_;
}
}
else
{
lean_object* v_val_2828_; lean_object* v___x_2830_; 
lean_del_object(v___x_2810_);
lean_dec(v___x_2799_);
lean_dec(v_stx_2293_);
v_val_2828_ = lean_ctor_get(v_fst_2808_, 0);
lean_inc(v_val_2828_);
lean_dec_ref(v_fst_2808_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v_val_2828_);
v___x_2830_ = v___x_2806_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_val_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v___x_2799_);
lean_dec(v_stx_2293_);
v_a_2835_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2803_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2803_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_val_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v_val_2843_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_val_2843_);
lean_dec_ref(v___x_2796_);
v___x_2844_ = l_Lean_Syntax_getArg(v___x_2743_, v___x_2734_);
lean_dec(v___x_2743_);
v___x_2845_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63));
lean_inc(v___x_2844_);
v___x_2846_ = l_Lean_Syntax_isOfKind(v___x_2844_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v_env_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec(v___x_2844_);
lean_dec(v_val_2843_);
v___x_2847_ = lean_st_ref_get(v___y_2741_);
v_env_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc_ref(v_env_2848_);
lean_dec(v___x_2847_);
lean_inc_n(v_stx_2293_, 2);
v___x_2849_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2850_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2851_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2850_, v_env_2848_, v___x_2849_);
v___x_2852_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2853_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2851_, v___x_2852_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2884_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2884_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2884_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v_fst_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2882_; 
v_fst_2858_ = lean_ctor_get(v_a_2854_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_a_2854_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; 
v_unused_2883_ = lean_ctor_get(v_a_2854_, 1);
lean_dec(v_unused_2883_);
v___x_2860_ = v_a_2854_;
v_isShared_2861_ = v_isSharedCheck_2882_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_fst_2858_);
lean_dec(v_a_2854_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2882_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
if (lean_obj_tag(v_fst_2858_) == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
lean_del_object(v___x_2856_);
v___x_2862_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2863_ = l_Lean_MessageData_ofName(v___x_2849_);
lean_inc_ref(v___x_2863_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 7);
lean_ctor_set(v___x_2860_, 1, v___x_2863_);
lean_ctor_set(v___x_2860_, 0, v___x_2862_);
v___x_2865_ = v___x_2860_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2866_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2869_ = l_Lean_indentD(v___x_2868_);
v___x_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2867_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v___x_2863_);
v___x_2874_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2875_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2876_;
}
}
else
{
lean_object* v_val_2878_; lean_object* v___x_2880_; 
lean_del_object(v___x_2860_);
lean_dec(v___x_2849_);
lean_dec(v_stx_2293_);
v_val_2878_ = lean_ctor_get(v_fst_2858_, 0);
lean_inc(v_val_2878_);
lean_dec_ref(v_fst_2858_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v_val_2878_);
v___x_2880_ = v___x_2856_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_val_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v___x_2849_);
lean_dec(v_stx_2293_);
v_a_2885_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2853_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2853_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2893_ = l_Lean_Syntax_getArg(v___x_2844_, v___x_2734_);
v___x_2894_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65));
v___x_2895_ = l_Lean_Syntax_isOfKind(v___x_2893_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; lean_object* v_env_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec(v___x_2844_);
lean_dec(v_val_2843_);
v___x_2896_ = lean_st_ref_get(v___y_2741_);
v_env_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc_ref(v_env_2897_);
lean_dec(v___x_2896_);
lean_inc_n(v_stx_2293_, 2);
v___x_2898_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2899_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2900_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2899_, v_env_2897_, v___x_2898_);
v___x_2901_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2902_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2900_, v___x_2901_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2933_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2933_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2933_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_fst_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2931_; 
v_fst_2907_ = lean_ctor_get(v_a_2903_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_a_2903_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; 
v_unused_2932_ = lean_ctor_get(v_a_2903_, 1);
lean_dec(v_unused_2932_);
v___x_2909_ = v_a_2903_;
v_isShared_2910_ = v_isSharedCheck_2931_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_fst_2907_);
lean_dec(v_a_2903_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2931_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
if (lean_obj_tag(v_fst_2907_) == 0)
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
lean_del_object(v___x_2905_);
v___x_2911_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2912_ = l_Lean_MessageData_ofName(v___x_2898_);
lean_inc_ref(v___x_2912_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set_tag(v___x_2909_, 7);
lean_ctor_set(v___x_2909_, 1, v___x_2912_);
lean_ctor_set(v___x_2909_, 0, v___x_2911_);
v___x_2914_ = v___x_2909_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2915_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2918_ = l_Lean_indentD(v___x_2917_);
v___x_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2916_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2919_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
lean_ctor_set(v___x_2922_, 1, v___x_2912_);
v___x_2923_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2922_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2924_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2925_;
}
}
else
{
lean_object* v_val_2927_; lean_object* v___x_2929_; 
lean_del_object(v___x_2909_);
lean_dec(v___x_2898_);
lean_dec(v_stx_2293_);
v_val_2927_ = lean_ctor_get(v_fst_2907_, 0);
lean_inc(v_val_2927_);
lean_dec_ref(v_fst_2907_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v_val_2927_);
v___x_2929_ = v___x_2905_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_val_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v___x_2898_);
lean_dec(v_stx_2293_);
v_a_2934_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2902_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2902_);
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
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
lean_dec(v_stx_2293_);
v___x_2942_ = lean_unsigned_to_nat(3u);
v___x_2943_ = l_Lean_Syntax_getArg(v___x_2844_, v___x_2942_);
lean_dec(v___x_2844_);
v___x_2944_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2943_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; size_t v_sz_2946_; lean_object* v___x_2947_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2944_);
v_sz_2946_ = lean_array_size(v_val_2843_);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2843_, v_sz_2946_, v___x_2795_, v_a_2945_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v_val_2843_);
return v___x_2947_;
}
else
{
lean_dec(v_val_2843_);
return v___x_2944_;
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
lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_dec(v_stx_2293_);
v___x_2998_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
return v___x_2999_;
}
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_dec(v_stx_2293_);
v___x_3000_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec(v_stx_2293_);
v___x_3002_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; size_t v_sz_3007_; size_t v___x_3008_; lean_object* v___x_3009_; 
v___x_3004_ = lean_unsigned_to_nat(2u);
v___x_3005_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3004_);
v___x_3006_ = l_Lean_Syntax_getArgs(v___x_3005_);
lean_dec(v___x_3005_);
v_sz_3007_ = lean_array_size(v___x_3006_);
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3007_, v___x_3008_, v___x_3006_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3010_; lean_object* v_env_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3010_ = lean_st_ref_get(v_a_2299_);
v_env_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc_ref(v_env_3011_);
lean_dec(v___x_3010_);
lean_inc_n(v_stx_2293_, 2);
v___x_3012_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3013_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3014_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3013_, v_env_3011_, v___x_3012_);
v___x_3015_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3016_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3014_, v___x_3015_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3047_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3047_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3047_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v_fst_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3045_; 
v_fst_3021_ = lean_ctor_get(v_a_3017_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_a_3017_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; 
v_unused_3046_ = lean_ctor_get(v_a_3017_, 1);
lean_dec(v_unused_3046_);
v___x_3023_ = v_a_3017_;
v_isShared_3024_ = v_isSharedCheck_3045_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_fst_3021_);
lean_dec(v_a_3017_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3045_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
if (lean_obj_tag(v_fst_3021_) == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3028_; 
lean_del_object(v___x_3019_);
v___x_3025_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3026_ = l_Lean_MessageData_ofName(v___x_3012_);
lean_inc_ref(v___x_3026_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set_tag(v___x_3023_, 7);
lean_ctor_set(v___x_3023_, 1, v___x_3026_);
lean_ctor_set(v___x_3023_, 0, v___x_3025_);
v___x_3028_ = v___x_3023_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3029_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3032_ = l_Lean_indentD(v___x_3031_);
v___x_3033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3030_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3033_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v___x_3026_);
v___x_3037_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3038_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3039_;
}
}
else
{
lean_object* v_val_3041_; lean_object* v___x_3043_; 
lean_del_object(v___x_3023_);
lean_dec(v___x_3012_);
lean_dec(v_stx_2293_);
v_val_3041_ = lean_ctor_get(v_fst_3021_, 0);
lean_inc(v_val_3041_);
lean_dec_ref(v_fst_3021_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v_val_3041_);
v___x_3043_ = v___x_3019_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_val_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v___x_3012_);
lean_dec(v_stx_2293_);
v_a_3048_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3016_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3016_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_val_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3190_; 
v_val_3056_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3058_ = v___x_3009_;
v_isShared_3059_ = v_isSharedCheck_3190_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_val_3056_);
lean_dec(v___x_3009_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3190_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v_finSeq_x3f_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3060_ = lean_unsigned_to_nat(1u);
v___x_3061_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3060_);
v___x_3085_ = lean_unsigned_to_nat(3u);
v___x_3086_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3085_);
v___x_3087_ = l_Lean_Syntax_isNone(v___x_3086_);
if (v___x_3087_ == 0)
{
uint8_t v___x_3088_; 
lean_inc(v___x_3086_);
v___x_3088_ = l_Lean_Syntax_matchesNull(v___x_3086_, v___x_3060_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; lean_object* v_env_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec(v___x_3086_);
lean_dec(v___x_3061_);
lean_del_object(v___x_3058_);
lean_dec(v_val_3056_);
v___x_3089_ = lean_st_ref_get(v_a_2299_);
v_env_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc_ref(v_env_3090_);
lean_dec(v___x_3089_);
lean_inc_n(v_stx_2293_, 2);
v___x_3091_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3092_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3093_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3092_, v_env_3090_, v___x_3091_);
v___x_3094_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3095_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3093_, v___x_3094_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3126_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3126_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3126_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v_fst_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3124_; 
v_fst_3100_ = lean_ctor_get(v_a_3096_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_a_3096_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_a_3096_, 1);
lean_dec(v_unused_3125_);
v___x_3102_ = v_a_3096_;
v_isShared_3103_ = v_isSharedCheck_3124_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_fst_3100_);
lean_dec(v_a_3096_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3124_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
if (lean_obj_tag(v_fst_3100_) == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; 
lean_del_object(v___x_3098_);
v___x_3104_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3105_ = l_Lean_MessageData_ofName(v___x_3091_);
lean_inc_ref(v___x_3105_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 7);
lean_ctor_set(v___x_3102_, 1, v___x_3105_);
lean_ctor_set(v___x_3102_, 0, v___x_3104_);
v___x_3107_ = v___x_3102_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3108_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3111_ = l_Lean_indentD(v___x_3110_);
v___x_3112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3109_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3112_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
lean_ctor_set(v___x_3115_, 1, v___x_3105_);
v___x_3116_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3117_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3118_;
}
}
else
{
lean_object* v_val_3120_; lean_object* v___x_3122_; 
lean_del_object(v___x_3102_);
lean_dec(v___x_3091_);
lean_dec(v_stx_2293_);
v_val_3120_ = lean_ctor_get(v_fst_3100_, 0);
lean_inc(v_val_3120_);
lean_dec_ref(v_fst_3100_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v_val_3120_);
v___x_3122_ = v___x_3098_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_val_3120_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v___x_3091_);
lean_dec(v_stx_2293_);
v_a_3127_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3095_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3095_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3135_ = lean_unsigned_to_nat(0u);
v___x_3136_ = l_Lean_Syntax_getArg(v___x_3086_, v___x_3135_);
lean_dec(v___x_3086_);
v___x_3137_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67));
lean_inc(v___x_3136_);
v___x_3138_ = l_Lean_Syntax_isOfKind(v___x_3136_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v_env_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_dec(v___x_3136_);
lean_dec(v___x_3061_);
lean_del_object(v___x_3058_);
lean_dec(v_val_3056_);
v___x_3139_ = lean_st_ref_get(v_a_2299_);
v_env_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc_ref(v_env_3140_);
lean_dec(v___x_3139_);
lean_inc_n(v_stx_2293_, 2);
v___x_3141_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3142_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3143_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3142_, v_env_3140_, v___x_3141_);
v___x_3144_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3145_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3143_, v___x_3144_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3176_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3176_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3176_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v_fst_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3174_; 
v_fst_3150_ = lean_ctor_get(v_a_3146_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_a_3146_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v_a_3146_, 1);
lean_dec(v_unused_3175_);
v___x_3152_ = v_a_3146_;
v_isShared_3153_ = v_isSharedCheck_3174_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_fst_3150_);
lean_dec(v_a_3146_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3174_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
if (lean_obj_tag(v_fst_3150_) == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
lean_del_object(v___x_3148_);
v___x_3154_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3155_ = l_Lean_MessageData_ofName(v___x_3141_);
lean_inc_ref(v___x_3155_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 7);
lean_ctor_set(v___x_3152_, 1, v___x_3155_);
lean_ctor_set(v___x_3152_, 0, v___x_3154_);
v___x_3157_ = v___x_3152_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3158_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3157_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3161_ = l_Lean_indentD(v___x_3160_);
v___x_3162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3159_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v___x_3155_);
v___x_3166_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3167_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3168_;
}
}
else
{
lean_object* v_val_3170_; lean_object* v___x_3172_; 
lean_del_object(v___x_3152_);
lean_dec(v___x_3141_);
lean_dec(v_stx_2293_);
v_val_3170_ = lean_ctor_get(v_fst_3150_, 0);
lean_inc(v_val_3170_);
lean_dec_ref(v_fst_3150_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 0, v_val_3170_);
v___x_3172_ = v___x_3148_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_val_3170_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v___x_3141_);
lean_dec(v_stx_2293_);
v_a_3177_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3145_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3145_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
lean_dec(v_stx_2293_);
v___x_3185_ = l_Lean_Syntax_getArg(v___x_3136_, v___x_3060_);
lean_dec(v___x_3136_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3185_);
v___x_3187_ = v___x_3058_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
v_finSeq_x3f_3063_ = v___x_3187_;
v___y_3064_ = v_a_2294_;
v___y_3065_ = v_a_2295_;
v___y_3066_ = v_a_2296_;
v___y_3067_ = v_a_2297_;
v___y_3068_ = v_a_2298_;
v___y_3069_ = v_a_2299_;
goto v___jp_3062_;
}
}
}
}
else
{
lean_object* v___x_3189_; 
lean_dec(v___x_3086_);
lean_del_object(v___x_3058_);
lean_dec(v_stx_2293_);
v___x_3189_ = lean_box(0);
v_finSeq_x3f_3063_ = v___x_3189_;
v___y_3064_ = v_a_2294_;
v___y_3065_ = v_a_2295_;
v___y_3066_ = v_a_2296_;
v___y_3067_ = v_a_2297_;
v___y_3068_ = v_a_2298_;
v___y_3069_ = v_a_2299_;
goto v___jp_3062_;
}
v___jp_3062_:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3061_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; size_t v_sz_3072_; lean_object* v___x_3073_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref(v___x_3070_);
v_sz_3072_ = lean_array_size(v_val_3056_);
v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3056_, v_sz_3072_, v___x_3008_, v_a_3071_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v_val_3056_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref(v___x_3073_);
v___x_3075_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3084_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3074_, v_a_3076_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3080_);
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
else
{
lean_dec(v_a_3074_);
return v___x_3075_;
}
}
else
{
lean_dec(v_finSeq_x3f_3063_);
return v___x_3073_;
}
}
else
{
lean_dec(v_finSeq_x3f_3063_);
lean_dec(v_val_3056_);
return v___x_3070_;
}
}
}
}
}
}
else
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = lean_unsigned_to_nat(1u);
v___x_3192_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3191_);
lean_dec(v_stx_2293_);
v___x_3193_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3192_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3215_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3215_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3215_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
uint8_t v_breaks_3198_; uint8_t v_returnsEarly_3199_; lean_object* v_reassigns_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3213_; 
v_breaks_3198_ = lean_ctor_get_uint8(v_a_3194_, sizeof(void*)*2);
v_returnsEarly_3199_ = lean_ctor_get_uint8(v_a_3194_, sizeof(void*)*2 + 2);
v_reassigns_3200_ = lean_ctor_get(v_a_3194_, 1);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_a_3194_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; 
v_unused_3214_ = lean_ctor_get(v_a_3194_, 0);
lean_dec(v_unused_3214_);
v___x_3202_ = v_a_3194_;
v_isShared_3203_ = v_isSharedCheck_3213_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_reassigns_3200_);
lean_dec(v_a_3194_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3213_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___y_3205_; 
if (v_breaks_3198_ == 0)
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_unsigned_to_nat(0u);
v___y_3205_ = v___x_3212_;
goto v___jp_3204_;
}
else
{
v___y_3205_ = v___x_3191_;
goto v___jp_3204_;
}
v___jp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___y_3205_);
v___x_3207_ = v___x_3202_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___y_3205_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_reassigns_3200_);
lean_ctor_set_uint8(v_reuseFailAlloc_3211_, sizeof(void*)*2 + 2, v_returnsEarly_3199_);
v___x_3207_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3209_; 
lean_ctor_set_uint8(v___x_3207_, sizeof(void*)*2, v___x_2620_);
lean_ctor_set_uint8(v___x_3207_, sizeof(void*)*2 + 1, v___x_2620_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3207_);
v___x_3209_ = v___x_3196_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
}
else
{
return v___x_3193_;
}
}
}
else
{
lean_object* v___x_3216_; lean_object* v___y_3218_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
v___x_3216_ = lean_unsigned_to_nat(1u);
v___x_3289_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3216_);
v___x_3290_ = l_Lean_Syntax_getArgs(v___x_3289_);
lean_dec(v___x_3289_);
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3293_ = lean_array_get_size(v___x_3290_);
v___x_3294_ = lean_nat_dec_lt(v___x_3291_, v___x_3293_);
if (v___x_3294_ == 0)
{
lean_dec_ref(v___x_3290_);
v___y_3218_ = v___x_3292_;
goto v___jp_3217_;
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v___x_3295_ = lean_box(v___x_2620_);
v___x_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
lean_ctor_set(v___x_3296_, 1, v___x_3292_);
v___x_3297_ = lean_nat_dec_le(v___x_3293_, v___x_3293_);
if (v___x_3297_ == 0)
{
if (v___x_3294_ == 0)
{
lean_dec_ref(v___x_3296_);
lean_dec_ref(v___x_3290_);
v___y_3218_ = v___x_3292_;
goto v___jp_3217_;
}
else
{
size_t v___x_3298_; size_t v___x_3299_; lean_object* v___x_3300_; lean_object* v_snd_3301_; 
v___x_3298_ = ((size_t)0ULL);
v___x_3299_ = lean_usize_of_nat(v___x_3293_);
v___x_3300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2620_, v___x_2618_, v___x_3290_, v___x_3298_, v___x_3299_, v___x_3296_);
lean_dec_ref(v___x_3290_);
v_snd_3301_ = lean_ctor_get(v___x_3300_, 1);
lean_inc(v_snd_3301_);
lean_dec_ref(v___x_3300_);
v___y_3218_ = v_snd_3301_;
goto v___jp_3217_;
}
}
else
{
size_t v___x_3302_; size_t v___x_3303_; lean_object* v___x_3304_; lean_object* v_snd_3305_; 
v___x_3302_ = ((size_t)0ULL);
v___x_3303_ = lean_usize_of_nat(v___x_3293_);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2620_, v___x_2618_, v___x_3290_, v___x_3302_, v___x_3303_, v___x_3296_);
lean_dec_ref(v___x_3290_);
v_snd_3305_ = lean_ctor_get(v___x_3304_, 1);
lean_inc(v_snd_3305_);
lean_dec_ref(v___x_3304_);
v___y_3218_ = v_snd_3305_;
goto v___jp_3217_;
}
}
v___jp_3217_:
{
size_t v_sz_3219_; size_t v___x_3220_; lean_object* v___x_3221_; 
v_sz_3219_ = lean_array_size(v___y_3218_);
v___x_3220_ = ((size_t)0ULL);
v___x_3221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3219_, v___x_3220_, v___y_3218_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3222_; lean_object* v_env_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3222_ = lean_st_ref_get(v_a_2299_);
v_env_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc_ref(v_env_3223_);
lean_dec(v___x_3222_);
lean_inc_n(v_stx_2293_, 2);
v___x_3224_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3225_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3226_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3225_, v_env_3223_, v___x_3224_);
v___x_3227_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3228_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3226_, v___x_3227_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3259_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3259_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3259_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v_fst_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3257_; 
v_fst_3233_ = lean_ctor_get(v_a_3229_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_a_3229_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; 
v_unused_3258_ = lean_ctor_get(v_a_3229_, 1);
lean_dec(v_unused_3258_);
v___x_3235_ = v_a_3229_;
v_isShared_3236_ = v_isSharedCheck_3257_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_fst_3233_);
lean_dec(v_a_3229_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3257_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
if (lean_obj_tag(v_fst_3233_) == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
lean_del_object(v___x_3231_);
v___x_3237_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3238_ = l_Lean_MessageData_ofName(v___x_3224_);
lean_inc_ref(v___x_3238_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set_tag(v___x_3235_, 7);
lean_ctor_set(v___x_3235_, 1, v___x_3238_);
lean_ctor_set(v___x_3235_, 0, v___x_3237_);
v___x_3240_ = v___x_3235_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3241_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3244_ = l_Lean_indentD(v___x_3243_);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3242_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3247_);
lean_ctor_set(v___x_3248_, 1, v___x_3238_);
v___x_3249_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3250_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3251_;
}
}
else
{
lean_object* v_val_3253_; lean_object* v___x_3255_; 
lean_del_object(v___x_3235_);
lean_dec(v___x_3224_);
lean_dec(v_stx_2293_);
v_val_3253_ = lean_ctor_get(v_fst_3233_, 0);
lean_inc(v_val_3253_);
lean_dec_ref(v_fst_3233_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v_val_3253_);
v___x_3255_ = v___x_3231_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_val_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v___x_3224_);
lean_dec(v_stx_2293_);
v_a_3260_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3228_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3228_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_dec_ref(v___x_3221_);
v___x_3268_ = lean_unsigned_to_nat(3u);
v___x_3269_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3268_);
lean_dec(v_stx_2293_);
v___x_3270_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3269_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3288_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3288_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3288_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
uint8_t v_returnsEarly_3275_; lean_object* v_reassigns_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3286_; 
v_returnsEarly_3275_ = lean_ctor_get_uint8(v_a_3271_, sizeof(void*)*2 + 2);
v_reassigns_3276_ = lean_ctor_get(v_a_3271_, 1);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_a_3271_);
if (v_isSharedCheck_3286_ == 0)
{
lean_object* v_unused_3287_; 
v_unused_3287_ = lean_ctor_get(v_a_3271_, 0);
lean_dec(v_unused_3287_);
v___x_3278_ = v_a_3271_;
v_isShared_3279_ = v_isSharedCheck_3286_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_reassigns_3276_);
lean_dec(v_a_3271_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3286_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3216_);
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3216_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_reassigns_3276_);
lean_ctor_set_uint8(v_reuseFailAlloc_3285_, sizeof(void*)*2 + 2, v_returnsEarly_3275_);
v___x_3281_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3283_; 
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*2, v___x_2618_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*2 + 1, v___x_2618_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3281_);
v___x_3283_ = v___x_3273_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
}
else
{
return v___x_3270_;
}
}
}
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3306_ = lean_unsigned_to_nat(1u);
v___x_3307_ = lean_unsigned_to_nat(3u);
v___x_3308_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3307_);
lean_dec(v_stx_2293_);
v___x_3309_ = l_Lean_NameSet_empty;
v___x_3310_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3310_, 0, v___x_3306_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*2, v___x_2616_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*2 + 1, v___x_2616_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*2 + 2, v___x_2616_);
v___x_3311_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3308_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3320_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3320_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3320_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3316_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3310_, v_a_3312_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3316_);
v___x_3318_ = v___x_3314_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
else
{
lean_dec_ref(v___x_3310_);
return v___x_3311_;
}
}
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; size_t v_sz_3324_; size_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3321_ = lean_unsigned_to_nat(4u);
v___x_3322_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3321_);
v___x_3323_ = l_Lean_Syntax_getArgs(v___x_3322_);
lean_dec(v___x_3322_);
v_sz_3324_ = lean_array_size(v___x_3323_);
v___x_3325_ = ((size_t)0ULL);
v___x_3326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3324_, v___x_3325_, v___x_3323_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v___x_3327_; lean_object* v_env_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3327_ = lean_st_ref_get(v_a_2299_);
v_env_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc_ref(v_env_3328_);
lean_dec(v___x_3327_);
lean_inc_n(v_stx_2293_, 2);
v___x_3329_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3330_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3331_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3330_, v_env_3328_, v___x_3329_);
v___x_3332_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3333_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3331_, v___x_3332_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3364_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3364_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3364_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_fst_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3362_; 
v_fst_3338_ = lean_ctor_get(v_a_3334_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_a_3334_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v_a_3334_, 1);
lean_dec(v_unused_3363_);
v___x_3340_ = v_a_3334_;
v_isShared_3341_ = v_isSharedCheck_3362_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_fst_3338_);
lean_dec(v_a_3334_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3362_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
if (lean_obj_tag(v_fst_3338_) == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
lean_del_object(v___x_3336_);
v___x_3342_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3343_ = l_Lean_MessageData_ofName(v___x_3329_);
lean_inc_ref(v___x_3343_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 7);
lean_ctor_set(v___x_3340_, 1, v___x_3343_);
lean_ctor_set(v___x_3340_, 0, v___x_3342_);
v___x_3345_ = v___x_3340_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3346_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3345_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3349_ = l_Lean_indentD(v___x_3348_);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3347_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
lean_ctor_set(v___x_3353_, 1, v___x_3343_);
v___x_3354_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3355_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3356_;
}
}
else
{
lean_object* v_val_3358_; lean_object* v___x_3360_; 
lean_del_object(v___x_3340_);
lean_dec(v___x_3329_);
lean_dec(v_stx_2293_);
v_val_3358_ = lean_ctor_get(v_fst_3338_, 0);
lean_inc(v_val_3358_);
lean_dec_ref(v_fst_3338_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v_val_3358_);
v___x_3360_ = v___x_3336_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_val_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v___x_3329_);
lean_dec(v_stx_2293_);
v_a_3365_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3333_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3333_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3460_; 
v_val_3373_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3375_ = v___x_3326_;
v_isShared_3376_ = v_isSharedCheck_3460_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_val_3373_);
lean_dec(v___x_3326_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3460_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v_elseSeq_x3f_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v___x_3377_ = lean_unsigned_to_nat(3u);
v___x_3378_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3377_);
v___x_3403_ = lean_unsigned_to_nat(5u);
v___x_3404_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3403_);
v___x_3405_ = l_Lean_Syntax_isNone(v___x_3404_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3406_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3404_);
v___x_3407_ = l_Lean_Syntax_matchesNull(v___x_3404_, v___x_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v_env_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec(v___x_3404_);
lean_dec(v___x_3378_);
lean_del_object(v___x_3375_);
lean_dec(v_val_3373_);
v___x_3408_ = lean_st_ref_get(v_a_2299_);
v_env_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc_ref(v_env_3409_);
lean_dec(v___x_3408_);
lean_inc_n(v_stx_2293_, 2);
v___x_3410_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3411_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3412_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3411_, v_env_3409_, v___x_3410_);
v___x_3413_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3414_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3412_, v___x_3413_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3445_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3445_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3445_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v_fst_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3443_; 
v_fst_3419_ = lean_ctor_get(v_a_3415_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_a_3415_);
if (v_isSharedCheck_3443_ == 0)
{
lean_object* v_unused_3444_; 
v_unused_3444_ = lean_ctor_get(v_a_3415_, 1);
lean_dec(v_unused_3444_);
v___x_3421_ = v_a_3415_;
v_isShared_3422_ = v_isSharedCheck_3443_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_fst_3419_);
lean_dec(v_a_3415_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3443_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
if (lean_obj_tag(v_fst_3419_) == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
lean_del_object(v___x_3417_);
v___x_3423_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3424_ = l_Lean_MessageData_ofName(v___x_3410_);
lean_inc_ref(v___x_3424_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set_tag(v___x_3421_, 7);
lean_ctor_set(v___x_3421_, 1, v___x_3424_);
lean_ctor_set(v___x_3421_, 0, v___x_3423_);
v___x_3426_ = v___x_3421_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3427_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3430_ = l_Lean_indentD(v___x_3429_);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3428_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v___x_3424_);
v___x_3435_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3434_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3436_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3437_;
}
}
else
{
lean_object* v_val_3439_; lean_object* v___x_3441_; 
lean_del_object(v___x_3421_);
lean_dec(v___x_3410_);
lean_dec(v_stx_2293_);
v_val_3439_ = lean_ctor_get(v_fst_3419_, 0);
lean_inc(v_val_3439_);
lean_dec_ref(v_fst_3419_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v_val_3439_);
v___x_3441_ = v___x_3417_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_val_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v___x_3410_);
lean_dec(v_stx_2293_);
v_a_3446_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3414_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3414_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
lean_dec(v_stx_2293_);
v___x_3454_ = lean_unsigned_to_nat(1u);
v___x_3455_ = l_Lean_Syntax_getArg(v___x_3404_, v___x_3454_);
lean_dec(v___x_3404_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3455_);
v___x_3457_ = v___x_3375_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
v_elseSeq_x3f_3380_ = v___x_3457_;
v___y_3381_ = v_a_2294_;
v___y_3382_ = v_a_2295_;
v___y_3383_ = v_a_2296_;
v___y_3384_ = v_a_2297_;
v___y_3385_ = v_a_2298_;
v___y_3386_ = v_a_2299_;
goto v___jp_3379_;
}
}
}
else
{
lean_object* v___x_3459_; 
lean_dec(v___x_3404_);
lean_del_object(v___x_3375_);
lean_dec(v_stx_2293_);
v___x_3459_ = lean_box(0);
v_elseSeq_x3f_3380_ = v___x_3459_;
v___y_3381_ = v_a_2294_;
v___y_3382_ = v_a_2295_;
v___y_3383_ = v_a_2296_;
v___y_3384_ = v_a_2297_;
v___y_3385_ = v_a_2298_;
v___y_3386_ = v_a_2299_;
goto v___jp_3379_;
}
v___jp_3379_:
{
lean_object* v___x_3387_; 
v___x_3387_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; size_t v_sz_3390_; lean_object* v___x_3391_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref(v___x_3387_);
v___x_3389_ = l_Array_reverse___redArg(v_val_3373_);
v_sz_3390_ = lean_array_size(v___x_3389_);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3389_, v_sz_3390_, v___x_3325_, v_a_3388_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec_ref(v___x_3389_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref(v___x_3391_);
v___x_3393_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3378_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3402_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3402_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3402_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3398_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3394_, v_a_3392_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3398_);
v___x_3400_ = v___x_3396_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
else
{
lean_dec(v_a_3392_);
return v___x_3393_;
}
}
else
{
lean_dec(v___x_3378_);
return v___x_3391_;
}
}
else
{
lean_dec(v___x_3378_);
lean_dec(v_val_3373_);
return v___x_3387_;
}
}
}
}
}
}
else
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3461_ = lean_unsigned_to_nat(0u);
v___x_3462_ = lean_unsigned_to_nat(1u);
v___x_3633_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3462_);
v___x_3634_ = l_Lean_Syntax_isNone(v___x_3633_);
if (v___x_3634_ == 0)
{
uint8_t v___x_3635_; 
lean_inc(v___x_3633_);
v___x_3635_ = l_Lean_Syntax_matchesNull(v___x_3633_, v___x_3462_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; lean_object* v_env_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
lean_dec(v___x_3633_);
v___x_3636_ = lean_st_ref_get(v_a_2299_);
v_env_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc_ref(v_env_3637_);
lean_dec(v___x_3636_);
lean_inc_n(v_stx_2293_, 2);
v___x_3638_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3639_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3640_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3639_, v_env_3637_, v___x_3638_);
v___x_3641_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3642_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3640_, v___x_3641_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3673_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3645_ = v___x_3642_;
v_isShared_3646_ = v_isSharedCheck_3673_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3673_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v_fst_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3671_; 
v_fst_3647_ = lean_ctor_get(v_a_3643_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v_a_3643_);
if (v_isSharedCheck_3671_ == 0)
{
lean_object* v_unused_3672_; 
v_unused_3672_ = lean_ctor_get(v_a_3643_, 1);
lean_dec(v_unused_3672_);
v___x_3649_ = v_a_3643_;
v_isShared_3650_ = v_isSharedCheck_3671_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_fst_3647_);
lean_dec(v_a_3643_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3671_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
if (lean_obj_tag(v_fst_3647_) == 0)
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
lean_del_object(v___x_3645_);
v___x_3651_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3652_ = l_Lean_MessageData_ofName(v___x_3638_);
lean_inc_ref(v___x_3652_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set_tag(v___x_3649_, 7);
lean_ctor_set(v___x_3649_, 1, v___x_3652_);
lean_ctor_set(v___x_3649_, 0, v___x_3651_);
v___x_3654_ = v___x_3649_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3655_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3658_ = l_Lean_indentD(v___x_3657_);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3656_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
lean_ctor_set(v___x_3662_, 1, v___x_3652_);
v___x_3663_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3664_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3665_;
}
}
else
{
lean_object* v_val_3667_; lean_object* v___x_3669_; 
lean_del_object(v___x_3649_);
lean_dec(v___x_3638_);
lean_dec(v_stx_2293_);
v_val_3667_ = lean_ctor_get(v_fst_3647_, 0);
lean_inc(v_val_3667_);
lean_dec_ref(v_fst_3647_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v_val_3667_);
v___x_3669_ = v___x_3645_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_val_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v___x_3638_);
lean_dec(v_stx_2293_);
v_a_3674_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3642_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3642_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3682_ = l_Lean_Syntax_getArg(v___x_3633_, v___x_3461_);
lean_dec(v___x_3633_);
v___x_3683_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71));
v___x_3684_ = l_Lean_Syntax_isOfKind(v___x_3682_, v___x_3683_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v_env_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3685_ = lean_st_ref_get(v_a_2299_);
v_env_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc_ref(v_env_3686_);
lean_dec(v___x_3685_);
lean_inc_n(v_stx_2293_, 2);
v___x_3687_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3688_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3689_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3688_, v_env_3686_, v___x_3687_);
v___x_3690_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3691_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3689_, v___x_3690_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3722_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3694_ = v___x_3691_;
v_isShared_3695_ = v_isSharedCheck_3722_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3691_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3722_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_fst_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3720_; 
v_fst_3696_ = lean_ctor_get(v_a_3692_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_a_3692_);
if (v_isSharedCheck_3720_ == 0)
{
lean_object* v_unused_3721_; 
v_unused_3721_ = lean_ctor_get(v_a_3692_, 1);
lean_dec(v_unused_3721_);
v___x_3698_ = v_a_3692_;
v_isShared_3699_ = v_isSharedCheck_3720_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_fst_3696_);
lean_dec(v_a_3692_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3720_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
if (lean_obj_tag(v_fst_3696_) == 0)
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
lean_del_object(v___x_3694_);
v___x_3700_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3701_ = l_Lean_MessageData_ofName(v___x_3687_);
lean_inc_ref(v___x_3701_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set_tag(v___x_3698_, 7);
lean_ctor_set(v___x_3698_, 1, v___x_3701_);
lean_ctor_set(v___x_3698_, 0, v___x_3700_);
v___x_3703_ = v___x_3698_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3704_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3703_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3707_ = l_Lean_indentD(v___x_3706_);
v___x_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3705_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3708_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
lean_ctor_set(v___x_3711_, 1, v___x_3701_);
v___x_3712_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3713_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3714_;
}
}
else
{
lean_object* v_val_3716_; lean_object* v___x_3718_; 
lean_del_object(v___x_3698_);
lean_dec(v___x_3687_);
lean_dec(v_stx_2293_);
v_val_3716_ = lean_ctor_get(v_fst_3696_, 0);
lean_inc(v_val_3716_);
lean_dec_ref(v_fst_3696_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v_val_3716_);
v___x_3718_ = v___x_3694_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_val_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec(v___x_3687_);
lean_dec(v_stx_2293_);
v_a_3723_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3691_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3691_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
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
else
{
v___y_3528_ = v_a_2294_;
v___y_3529_ = v_a_2295_;
v___y_3530_ = v_a_2296_;
v___y_3531_ = v_a_2297_;
v___y_3532_ = v_a_2298_;
v___y_3533_ = v_a_2299_;
goto v___jp_3527_;
}
}
}
else
{
lean_dec(v___x_3633_);
v___y_3528_ = v_a_2294_;
v___y_3529_ = v_a_2295_;
v___y_3530_ = v_a_2296_;
v___y_3531_ = v_a_2297_;
v___y_3532_ = v_a_2298_;
v___y_3533_ = v_a_2299_;
goto v___jp_3527_;
}
v___jp_3463_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3470_ = lean_unsigned_to_nat(6u);
v___x_3471_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3470_);
v___x_3472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3471_);
v___x_3473_ = l_Lean_Syntax_isOfKind(v___x_3471_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; lean_object* v_env_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_dec(v___x_3471_);
v___x_3474_ = lean_st_ref_get(v___y_3469_);
v_env_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc_ref(v_env_3475_);
lean_dec(v___x_3474_);
lean_inc_n(v_stx_2293_, 2);
v___x_3476_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3477_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3478_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3477_, v_env_3475_, v___x_3476_);
v___x_3479_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3480_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3478_, v___x_3479_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3511_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3511_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3511_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v_fst_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3509_; 
v_fst_3485_ = lean_ctor_get(v_a_3481_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_a_3481_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; 
v_unused_3510_ = lean_ctor_get(v_a_3481_, 1);
lean_dec(v_unused_3510_);
v___x_3487_ = v_a_3481_;
v_isShared_3488_ = v_isSharedCheck_3509_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_fst_3485_);
lean_dec(v_a_3481_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3509_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
if (lean_obj_tag(v_fst_3485_) == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
lean_del_object(v___x_3483_);
v___x_3489_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3490_ = l_Lean_MessageData_ofName(v___x_3476_);
lean_inc_ref(v___x_3490_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set_tag(v___x_3487_, 7);
lean_ctor_set(v___x_3487_, 1, v___x_3490_);
lean_ctor_set(v___x_3487_, 0, v___x_3489_);
v___x_3492_ = v___x_3487_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3493_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3496_ = l_Lean_indentD(v___x_3495_);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3494_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3497_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3490_);
v___x_3501_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3502_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v___x_3503_;
}
}
else
{
lean_object* v_val_3505_; lean_object* v___x_3507_; 
lean_del_object(v___x_3487_);
lean_dec(v___x_3476_);
lean_dec(v_stx_2293_);
v_val_3505_ = lean_ctor_get(v_fst_3485_, 0);
lean_inc(v_val_3505_);
lean_dec_ref(v_fst_3485_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v_val_3505_);
v___x_3507_ = v___x_3483_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_val_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec(v___x_3476_);
lean_dec(v_stx_2293_);
v_a_3512_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3480_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3480_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; size_t v_sz_3524_; size_t v___x_3525_; lean_object* v___x_3526_; 
lean_dec(v_stx_2293_);
v___x_3520_ = l_Lean_Syntax_getArg(v___x_3471_, v___x_3461_);
lean_dec(v___x_3471_);
v___x_3521_ = l_Lean_Syntax_getArgs(v___x_3520_);
lean_dec(v___x_3520_);
v___x_3522_ = l_Lean_NameSet_empty;
v___x_3523_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_3523_, 0, v___x_3462_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*2, v___x_2612_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*2 + 1, v___x_2612_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*2 + 2, v___x_2612_);
v_sz_3524_ = lean_array_size(v___x_3521_);
v___x_3525_ = ((size_t)0ULL);
v___x_3526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2612_, v___x_3521_, v_sz_3524_, v___x_3525_, v___x_3523_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec_ref(v___x_3521_);
return v___x_3526_;
}
}
v___jp_3527_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3534_ = lean_unsigned_to_nat(2u);
v___x_3535_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3534_);
v___x_3536_ = l_Lean_Syntax_isNone(v___x_3535_);
if (v___x_3536_ == 0)
{
uint8_t v___x_3537_; 
lean_inc(v___x_3535_);
v___x_3537_ = l_Lean_Syntax_matchesNull(v___x_3535_, v___x_3462_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; lean_object* v_env_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec(v___x_3535_);
v___x_3538_ = lean_st_ref_get(v___y_3533_);
v_env_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc_ref(v_env_3539_);
lean_dec(v___x_3538_);
lean_inc_n(v_stx_2293_, 2);
v___x_3540_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3541_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3542_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3541_, v_env_3539_, v___x_3540_);
v___x_3543_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3544_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3542_, v___x_3543_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3575_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3575_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3575_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v_fst_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3573_; 
v_fst_3549_ = lean_ctor_get(v_a_3545_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_a_3545_);
if (v_isSharedCheck_3573_ == 0)
{
lean_object* v_unused_3574_; 
v_unused_3574_ = lean_ctor_get(v_a_3545_, 1);
lean_dec(v_unused_3574_);
v___x_3551_ = v_a_3545_;
v_isShared_3552_ = v_isSharedCheck_3573_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_fst_3549_);
lean_dec(v_a_3545_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3573_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
if (lean_obj_tag(v_fst_3549_) == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
lean_del_object(v___x_3547_);
v___x_3553_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3554_ = l_Lean_MessageData_ofName(v___x_3540_);
lean_inc_ref(v___x_3554_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set_tag(v___x_3551_, 7);
lean_ctor_set(v___x_3551_, 1, v___x_3554_);
lean_ctor_set(v___x_3551_, 0, v___x_3553_);
v___x_3556_ = v___x_3551_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3557_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3556_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3560_ = l_Lean_indentD(v___x_3559_);
v___x_3561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3558_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
v___x_3562_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3561_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v___x_3554_);
v___x_3565_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3566_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
return v___x_3567_;
}
}
else
{
lean_object* v_val_3569_; lean_object* v___x_3571_; 
lean_del_object(v___x_3551_);
lean_dec(v___x_3540_);
lean_dec(v_stx_2293_);
v_val_3569_ = lean_ctor_get(v_fst_3549_, 0);
lean_inc(v_val_3569_);
lean_dec_ref(v_fst_3549_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v_val_3569_);
v___x_3571_ = v___x_3547_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_val_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec(v___x_3540_);
lean_dec(v_stx_2293_);
v_a_3576_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3544_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3544_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v___x_3584_ = l_Lean_Syntax_getArg(v___x_3535_, v___x_3461_);
lean_dec(v___x_3535_);
v___x_3585_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69));
v___x_3586_ = l_Lean_Syntax_isOfKind(v___x_3584_, v___x_3585_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; lean_object* v_env_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3587_ = lean_st_ref_get(v___y_3533_);
v_env_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc_ref(v_env_3588_);
lean_dec(v___x_3587_);
lean_inc_n(v_stx_2293_, 2);
v___x_3589_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3590_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3591_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3590_, v_env_3588_, v___x_3589_);
v___x_3592_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3593_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3591_, v___x_3592_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3624_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3596_ = v___x_3593_;
v_isShared_3597_ = v_isSharedCheck_3624_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3593_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3624_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v_fst_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3622_; 
v_fst_3598_ = lean_ctor_get(v_a_3594_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_a_3594_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v_a_3594_, 1);
lean_dec(v_unused_3623_);
v___x_3600_ = v_a_3594_;
v_isShared_3601_ = v_isSharedCheck_3622_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_fst_3598_);
lean_dec(v_a_3594_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3622_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
if (lean_obj_tag(v_fst_3598_) == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
lean_del_object(v___x_3596_);
v___x_3602_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3603_ = l_Lean_MessageData_ofName(v___x_3589_);
lean_inc_ref(v___x_3603_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set_tag(v___x_3600_, 7);
lean_ctor_set(v___x_3600_, 1, v___x_3603_);
lean_ctor_set(v___x_3600_, 0, v___x_3602_);
v___x_3605_ = v___x_3600_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3606_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3609_ = l_Lean_indentD(v___x_3608_);
v___x_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3607_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set(v___x_3613_, 1, v___x_3603_);
v___x_3614_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3615_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
return v___x_3616_;
}
}
else
{
lean_object* v_val_3618_; lean_object* v___x_3620_; 
lean_del_object(v___x_3600_);
lean_dec(v___x_3589_);
lean_dec(v_stx_2293_);
v_val_3618_ = lean_ctor_get(v_fst_3598_, 0);
lean_inc(v_val_3618_);
lean_dec_ref(v_fst_3598_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 0, v_val_3618_);
v___x_3620_ = v___x_3596_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_val_3618_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v___x_3589_);
lean_dec(v_stx_2293_);
v_a_3625_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3593_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3593_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
v___y_3464_ = v___y_3528_;
v___y_3465_ = v___y_3529_;
v___y_3466_ = v___y_3530_;
v___y_3467_ = v___y_3531_;
v___y_3468_ = v___y_3532_;
v___y_3469_ = v___y_3533_;
goto v___jp_3463_;
}
}
}
else
{
lean_dec(v___x_3535_);
v___y_3464_ = v___y_3528_;
v___y_3465_ = v___y_3529_;
v___y_3466_ = v___y_3530_;
v___y_3467_ = v___y_3531_;
v___y_3468_ = v___y_3532_;
v___y_3469_ = v___y_3533_;
goto v___jp_3463_;
}
}
}
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v___x_3731_ = lean_unsigned_to_nat(0u);
v___x_3732_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3731_);
v___x_3733_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_3732_);
v___x_3734_ = l_Lean_Syntax_isOfKind(v___x_3732_, v___x_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3735_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_3732_);
v___x_3736_ = l_Lean_Syntax_isOfKind(v___x_3732_, v___x_3735_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; lean_object* v_env_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
lean_dec(v___x_3732_);
v___x_3737_ = lean_st_ref_get(v_a_2299_);
v_env_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc_ref(v_env_3738_);
lean_dec(v___x_3737_);
lean_inc_n(v_stx_2293_, 2);
v___x_3739_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3740_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3741_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3740_, v_env_3738_, v___x_3739_);
v___x_3742_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3743_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3741_, v___x_3742_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3774_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_3774_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3774_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v_fst_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3772_; 
v_fst_3748_ = lean_ctor_get(v_a_3744_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_a_3744_);
if (v_isSharedCheck_3772_ == 0)
{
lean_object* v_unused_3773_; 
v_unused_3773_ = lean_ctor_get(v_a_3744_, 1);
lean_dec(v_unused_3773_);
v___x_3750_ = v_a_3744_;
v_isShared_3751_ = v_isSharedCheck_3772_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_fst_3748_);
lean_dec(v_a_3744_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3772_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
if (lean_obj_tag(v_fst_3748_) == 0)
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
lean_del_object(v___x_3746_);
v___x_3752_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3753_ = l_Lean_MessageData_ofName(v___x_3739_);
lean_inc_ref(v___x_3753_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set_tag(v___x_3750_, 7);
lean_ctor_set(v___x_3750_, 1, v___x_3753_);
lean_ctor_set(v___x_3750_, 0, v___x_3752_);
v___x_3755_ = v___x_3750_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3767_, 1, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3756_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3755_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3759_ = l_Lean_indentD(v___x_3758_);
v___x_3760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3757_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
lean_ctor_set(v___x_3763_, 1, v___x_3753_);
v___x_3764_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3765_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3766_;
}
}
else
{
lean_object* v_val_3768_; lean_object* v___x_3770_; 
lean_del_object(v___x_3750_);
lean_dec(v___x_3739_);
lean_dec(v_stx_2293_);
v_val_3768_ = lean_ctor_get(v_fst_3748_, 0);
lean_inc(v_val_3768_);
lean_dec_ref(v_fst_3748_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v_val_3768_);
v___x_3770_ = v___x_3746_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_val_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec(v___x_3739_);
lean_dec(v_stx_2293_);
v_a_3775_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3743_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3743_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v___x_3783_; 
lean_dec(v_stx_2293_);
v___x_3783_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2530_, v___x_3732_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3783_;
}
}
else
{
lean_object* v___x_3784_; 
lean_dec(v_stx_2293_);
v___x_3784_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2530_, v___x_3732_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3784_;
}
}
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3785_);
v___x_3787_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73));
lean_inc(v___x_3786_);
v___x_3788_ = l_Lean_Syntax_isOfKind(v___x_3786_, v___x_3787_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; uint8_t v___x_3790_; 
v___x_3789_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75));
lean_inc(v___x_3786_);
v___x_3790_ = l_Lean_Syntax_isOfKind(v___x_3786_, v___x_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; lean_object* v_env_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_dec(v___x_3786_);
v___x_3791_ = lean_st_ref_get(v_a_2299_);
v_env_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc_ref(v_env_3792_);
lean_dec(v___x_3791_);
lean_inc_n(v_stx_2293_, 2);
v___x_3793_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3794_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3795_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3794_, v_env_3792_, v___x_3793_);
v___x_3796_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3797_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3795_, v___x_3796_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
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
v___x_3812_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
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
v___x_3820_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3819_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3820_;
}
}
else
{
lean_object* v_val_3822_; lean_object* v___x_3824_; 
lean_del_object(v___x_3804_);
lean_dec(v___x_3793_);
lean_dec(v_stx_2293_);
v_val_3822_ = lean_ctor_get(v_fst_3802_, 0);
lean_inc(v_val_3822_);
lean_dec_ref(v_fst_3802_);
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
lean_dec(v_stx_2293_);
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
lean_object* v___x_3837_; 
lean_dec(v_stx_2293_);
v___x_3837_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_3786_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v___x_3786_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref(v___x_3837_);
v___x_3839_ = lean_box(0);
v___x_3840_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3838_, v___x_3839_, v___x_3839_, v___x_3839_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3840_;
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
v_a_3841_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3837_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3837_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
else
{
lean_object* v___x_3849_; 
lean_dec(v_stx_2293_);
v___x_3849_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_3786_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v___x_3786_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref(v___x_3849_);
v___x_3851_ = lean_box(0);
v___x_3852_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3850_, v___x_3851_, v___x_3851_, v___x_3851_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3852_;
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
v_a_3853_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3849_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3849_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
}
}
else
{
lean_object* v___x_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; 
v___x_3861_ = lean_unsigned_to_nat(1u);
v___x_3862_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3861_);
v___x_3863_ = l_Lean_Syntax_isNone(v___x_3862_);
if (v___x_3863_ == 0)
{
uint8_t v___x_3864_; 
v___x_3864_ = l_Lean_Syntax_matchesNull(v___x_3862_, v___x_3861_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; lean_object* v_env_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3865_ = lean_st_ref_get(v_a_2299_);
v_env_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc_ref(v_env_3866_);
lean_dec(v___x_3865_);
lean_inc_n(v_stx_2293_, 2);
v___x_3867_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3868_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3869_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3868_, v_env_3866_, v___x_3867_);
v___x_3870_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3871_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3869_, v___x_3870_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3902_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3902_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3902_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v_fst_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3900_; 
v_fst_3876_ = lean_ctor_get(v_a_3872_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v_a_3872_);
if (v_isSharedCheck_3900_ == 0)
{
lean_object* v_unused_3901_; 
v_unused_3901_ = lean_ctor_get(v_a_3872_, 1);
lean_dec(v_unused_3901_);
v___x_3878_ = v_a_3872_;
v_isShared_3879_ = v_isSharedCheck_3900_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_fst_3876_);
lean_dec(v_a_3872_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3900_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
if (lean_obj_tag(v_fst_3876_) == 0)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3883_; 
lean_del_object(v___x_3874_);
v___x_3880_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3881_ = l_Lean_MessageData_ofName(v___x_3867_);
lean_inc_ref(v___x_3881_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set_tag(v___x_3878_, 7);
lean_ctor_set(v___x_3878_, 1, v___x_3881_);
lean_ctor_set(v___x_3878_, 0, v___x_3880_);
v___x_3883_ = v___x_3878_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3880_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v___x_3881_);
v___x_3883_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3884_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3883_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3887_ = l_Lean_indentD(v___x_3886_);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3885_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v___x_3881_);
v___x_3892_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3893_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3894_;
}
}
else
{
lean_object* v_val_3896_; lean_object* v___x_3898_; 
lean_del_object(v___x_3878_);
lean_dec(v___x_3867_);
lean_dec(v_stx_2293_);
v_val_3896_ = lean_ctor_get(v_fst_3876_, 0);
lean_inc(v_val_3896_);
lean_dec_ref(v_fst_3876_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v_val_3896_);
v___x_3898_ = v___x_3874_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_val_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v___x_3867_);
lean_dec(v_stx_2293_);
v_a_3903_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3871_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3871_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
else
{
v___y_2548_ = v_a_2294_;
v___y_2549_ = v_a_2295_;
v___y_2550_ = v_a_2296_;
v___y_2551_ = v_a_2297_;
v___y_2552_ = v_a_2298_;
v___y_2553_ = v_a_2299_;
goto v___jp_2547_;
}
}
else
{
lean_dec(v___x_3862_);
v___y_2548_ = v_a_2294_;
v___y_2549_ = v_a_2295_;
v___y_2550_ = v_a_2296_;
v___y_2551_ = v_a_2297_;
v___y_2552_ = v_a_2298_;
v___y_2553_ = v_a_2299_;
goto v___jp_2547_;
}
}
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; 
v___x_3911_ = lean_unsigned_to_nat(1u);
v___x_3912_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3911_);
v___x_3913_ = l_Lean_Syntax_isNone(v___x_3912_);
if (v___x_3913_ == 0)
{
uint8_t v___x_3914_; 
v___x_3914_ = l_Lean_Syntax_matchesNull(v___x_3912_, v___x_3911_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; lean_object* v_env_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3915_ = lean_st_ref_get(v_a_2299_);
v_env_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc_ref(v_env_3916_);
lean_dec(v___x_3915_);
lean_inc_n(v_stx_2293_, 2);
v___x_3917_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3918_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3919_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3918_, v_env_3916_, v___x_3917_);
v___x_3920_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3921_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3919_, v___x_3920_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3952_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3924_ = v___x_3921_;
v_isShared_3925_ = v_isSharedCheck_3952_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3921_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3952_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v_fst_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3950_; 
v_fst_3926_ = lean_ctor_get(v_a_3922_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_a_3922_);
if (v_isSharedCheck_3950_ == 0)
{
lean_object* v_unused_3951_; 
v_unused_3951_ = lean_ctor_get(v_a_3922_, 1);
lean_dec(v_unused_3951_);
v___x_3928_ = v_a_3922_;
v_isShared_3929_ = v_isSharedCheck_3950_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_fst_3926_);
lean_dec(v_a_3922_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3950_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
if (lean_obj_tag(v_fst_3926_) == 0)
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3933_; 
lean_del_object(v___x_3924_);
v___x_3930_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3931_ = l_Lean_MessageData_ofName(v___x_3917_);
lean_inc_ref(v___x_3931_);
if (v_isShared_3929_ == 0)
{
lean_ctor_set_tag(v___x_3928_, 7);
lean_ctor_set(v___x_3928_, 1, v___x_3931_);
lean_ctor_set(v___x_3928_, 0, v___x_3930_);
v___x_3933_ = v___x_3928_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3934_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3933_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3937_ = l_Lean_indentD(v___x_3936_);
v___x_3938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3935_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3938_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
v___x_3941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
lean_ctor_set(v___x_3941_, 1, v___x_3931_);
v___x_3942_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3941_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3943_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3944_;
}
}
else
{
lean_object* v_val_3946_; lean_object* v___x_3948_; 
lean_del_object(v___x_3928_);
lean_dec(v___x_3917_);
lean_dec(v_stx_2293_);
v_val_3946_ = lean_ctor_get(v_fst_3926_, 0);
lean_inc(v_val_3946_);
lean_dec_ref(v_fst_3926_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 0, v_val_3946_);
v___x_3948_ = v___x_3924_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_val_3946_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec(v___x_3917_);
lean_dec(v_stx_2293_);
v_a_3953_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3921_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3921_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
else
{
v___y_2347_ = v_a_2294_;
v___y_2348_ = v_a_2295_;
v___y_2349_ = v_a_2296_;
v___y_2350_ = v_a_2297_;
v___y_2351_ = v_a_2298_;
v___y_2352_ = v_a_2299_;
goto v___jp_2346_;
}
}
else
{
lean_dec(v___x_3912_);
v___y_2347_ = v_a_2294_;
v___y_2348_ = v_a_2295_;
v___y_2349_ = v_a_2296_;
v___y_2350_ = v_a_2297_;
v___y_2351_ = v_a_2298_;
v___y_2352_ = v_a_2299_;
goto v___jp_2346_;
}
}
v___jp_2547_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2554_ = lean_unsigned_to_nat(2u);
v___x_2555_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2554_);
v___x_2556_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2557_ = l_Lean_Syntax_isOfKind(v___x_2555_, v___x_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v_env_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2558_ = lean_st_ref_get(v___y_2553_);
v_env_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc_ref(v_env_2559_);
lean_dec(v___x_2558_);
lean_inc_n(v_stx_2293_, 2);
v___x_2560_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2561_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2562_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2561_, v_env_2559_, v___x_2560_);
v___x_2563_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2564_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2562_, v___x_2563_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2595_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2595_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2595_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v_fst_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2593_; 
v_fst_2569_ = lean_ctor_get(v_a_2565_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_a_2565_);
if (v_isSharedCheck_2593_ == 0)
{
lean_object* v_unused_2594_; 
v_unused_2594_ = lean_ctor_get(v_a_2565_, 1);
lean_dec(v_unused_2594_);
v___x_2571_ = v_a_2565_;
v_isShared_2572_ = v_isSharedCheck_2593_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_fst_2569_);
lean_dec(v_a_2565_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2593_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
if (lean_obj_tag(v_fst_2569_) == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_del_object(v___x_2567_);
v___x_2573_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2574_ = l_Lean_MessageData_ofName(v___x_2560_);
lean_inc_ref(v___x_2574_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 7);
lean_ctor_set(v___x_2571_, 1, v___x_2574_);
lean_ctor_set(v___x_2571_, 0, v___x_2573_);
v___x_2576_ = v___x_2571_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2577_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2580_ = l_Lean_indentD(v___x_2579_);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2578_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2574_);
v___x_2585_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2586_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
return v___x_2587_;
}
}
else
{
lean_object* v_val_2589_; lean_object* v___x_2591_; 
lean_del_object(v___x_2571_);
lean_dec(v___x_2560_);
lean_dec(v_stx_2293_);
v_val_2589_ = lean_ctor_get(v_fst_2569_, 0);
lean_inc(v_val_2589_);
lean_dec_ref(v_fst_2569_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v_val_2589_);
v___x_2591_ = v___x_2567_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_val_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v___x_2560_);
lean_dec(v_stx_2293_);
v_a_2596_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2564_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2564_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = lean_unsigned_to_nat(3u);
v___x_2605_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2604_);
lean_dec(v_stx_2293_);
v___x_2606_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2546_, v___x_2605_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
return v___x_2606_;
}
}
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v___x_3961_ = lean_unsigned_to_nat(0u);
v___x_3962_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_3961_);
v___x_3963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_3964_ = l_Lean_Syntax_isOfKind(v___x_3962_, v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v_env_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3965_ = lean_st_ref_get(v_a_2299_);
v_env_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc_ref(v_env_3966_);
lean_dec(v___x_3965_);
lean_inc_n(v_stx_2293_, 2);
v___x_3967_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_3968_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3969_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3968_, v_env_3966_, v___x_3967_);
v___x_3970_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3971_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_3969_, v___x_3970_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4002_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3974_ = v___x_3971_;
v_isShared_3975_ = v_isSharedCheck_4002_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3971_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4002_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v_fst_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_4000_; 
v_fst_3976_ = lean_ctor_get(v_a_3972_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_a_3972_);
if (v_isSharedCheck_4000_ == 0)
{
lean_object* v_unused_4001_; 
v_unused_4001_ = lean_ctor_get(v_a_3972_, 1);
lean_dec(v_unused_4001_);
v___x_3978_ = v_a_3972_;
v_isShared_3979_ = v_isSharedCheck_4000_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_fst_3976_);
lean_dec(v_a_3972_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_4000_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
if (lean_obj_tag(v_fst_3976_) == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3983_; 
lean_del_object(v___x_3974_);
v___x_3980_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3981_ = l_Lean_MessageData_ofName(v___x_3967_);
lean_inc_ref(v___x_3981_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set_tag(v___x_3978_, 7);
lean_ctor_set(v___x_3978_, 1, v___x_3981_);
lean_ctor_set(v___x_3978_, 0, v___x_3980_);
v___x_3983_ = v___x_3978_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3980_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3984_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_3987_ = l_Lean_indentD(v___x_3986_);
v___x_3988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3985_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3988_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set(v___x_3991_, 1, v___x_3981_);
v___x_3992_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3991_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3993_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_3994_;
}
}
else
{
lean_object* v_val_3996_; lean_object* v___x_3998_; 
lean_del_object(v___x_3978_);
lean_dec(v___x_3967_);
lean_dec(v_stx_2293_);
v_val_3996_ = lean_ctor_get(v_fst_3976_, 0);
lean_inc(v_val_3996_);
lean_dec_ref(v_fst_3976_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v_val_3996_);
v___x_3998_ = v___x_3974_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_val_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec(v___x_3967_);
lean_dec(v_stx_2293_);
v_a_4003_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3971_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3971_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4011_ = lean_unsigned_to_nat(1u);
v___x_4012_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_4011_);
v___x_4013_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77));
lean_inc(v___x_4012_);
v___x_4014_ = l_Lean_Syntax_isOfKind(v___x_4012_, v___x_4013_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; lean_object* v_env_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
lean_dec(v___x_4012_);
v___x_4015_ = lean_st_ref_get(v_a_2299_);
v_env_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc_ref(v_env_4016_);
lean_dec(v___x_4015_);
lean_inc_n(v_stx_2293_, 2);
v___x_4017_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_4018_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4019_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4018_, v_env_4016_, v___x_4017_);
v___x_4020_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4021_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_4019_, v___x_4020_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4052_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4052_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4052_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v_fst_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4050_; 
v_fst_4026_ = lean_ctor_get(v_a_4022_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_a_4022_);
if (v_isSharedCheck_4050_ == 0)
{
lean_object* v_unused_4051_; 
v_unused_4051_ = lean_ctor_get(v_a_4022_, 1);
lean_dec(v_unused_4051_);
v___x_4028_ = v_a_4022_;
v_isShared_4029_ = v_isSharedCheck_4050_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_fst_4026_);
lean_dec(v_a_4022_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4050_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
if (lean_obj_tag(v_fst_4026_) == 0)
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
lean_del_object(v___x_4024_);
v___x_4030_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4031_ = l_Lean_MessageData_ofName(v___x_4017_);
lean_inc_ref(v___x_4031_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set_tag(v___x_4028_, 7);
lean_ctor_set(v___x_4028_, 1, v___x_4031_);
lean_ctor_set(v___x_4028_, 0, v___x_4030_);
v___x_4033_ = v___x_4028_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4030_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4034_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4033_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
v___x_4036_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_4037_ = l_Lean_indentD(v___x_4036_);
v___x_4038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4035_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
v___x_4039_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4038_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4040_);
lean_ctor_set(v___x_4041_, 1, v___x_4031_);
v___x_4042_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4041_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4043_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_4044_;
}
}
else
{
lean_object* v_val_4046_; lean_object* v___x_4048_; 
lean_del_object(v___x_4028_);
lean_dec(v___x_4017_);
lean_dec(v_stx_2293_);
v_val_4046_ = lean_ctor_get(v_fst_4026_, 0);
lean_inc(v_val_4046_);
lean_dec_ref(v_fst_4026_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v_val_4046_);
v___x_4048_ = v___x_4024_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_val_4046_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec(v___x_4017_);
lean_dec(v_stx_2293_);
v_a_4053_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4021_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4021_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
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
else
{
lean_object* v___x_4061_; uint8_t v___x_4062_; 
v___x_4061_ = l_Lean_Syntax_getArg(v___x_4012_, v___x_3961_);
lean_dec(v___x_4012_);
lean_inc(v___x_4061_);
v___x_4062_ = l_Lean_Syntax_matchesNull(v___x_4061_, v___x_4011_);
if (v___x_4062_ == 0)
{
lean_object* v___x_4063_; lean_object* v_env_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
lean_dec(v___x_4061_);
v___x_4063_ = lean_st_ref_get(v_a_2299_);
v_env_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc_ref(v_env_4064_);
lean_dec(v___x_4063_);
lean_inc_n(v_stx_2293_, 2);
v___x_4065_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_4066_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4067_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4066_, v_env_4064_, v___x_4065_);
v___x_4068_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4069_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_4067_, v___x_4068_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4100_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4072_ = v___x_4069_;
v_isShared_4073_ = v_isSharedCheck_4100_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4069_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4100_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v_fst_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4098_; 
v_fst_4074_ = lean_ctor_get(v_a_4070_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_a_4070_);
if (v_isSharedCheck_4098_ == 0)
{
lean_object* v_unused_4099_; 
v_unused_4099_ = lean_ctor_get(v_a_4070_, 1);
lean_dec(v_unused_4099_);
v___x_4076_ = v_a_4070_;
v_isShared_4077_ = v_isSharedCheck_4098_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_fst_4074_);
lean_dec(v_a_4070_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4098_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
if (lean_obj_tag(v_fst_4074_) == 0)
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4081_; 
lean_del_object(v___x_4072_);
v___x_4078_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4079_ = l_Lean_MessageData_ofName(v___x_4065_);
lean_inc_ref(v___x_4079_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set_tag(v___x_4076_, 7);
lean_ctor_set(v___x_4076_, 1, v___x_4079_);
lean_ctor_set(v___x_4076_, 0, v___x_4078_);
v___x_4081_ = v___x_4076_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4078_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4082_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_4085_ = l_Lean_indentD(v___x_4084_);
v___x_4086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4083_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
v___x_4087_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4086_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set(v___x_4089_, 1, v___x_4079_);
v___x_4090_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4091_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_4092_;
}
}
else
{
lean_object* v_val_4094_; lean_object* v___x_4096_; 
lean_del_object(v___x_4076_);
lean_dec(v___x_4065_);
lean_dec(v_stx_2293_);
v_val_4094_ = lean_ctor_get(v_fst_4074_, 0);
lean_inc(v_val_4094_);
lean_dec_ref(v_fst_4074_);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 0, v_val_4094_);
v___x_4096_ = v___x_4072_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_val_4094_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec(v___x_4065_);
lean_dec(v_stx_2293_);
v_a_4101_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4069_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4069_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; 
v___x_4109_ = l_Lean_Syntax_getArg(v___x_4061_, v___x_3961_);
lean_dec(v___x_4061_);
v___x_4110_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79));
v___x_4111_ = l_Lean_Syntax_isOfKind(v___x_4109_, v___x_4110_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; lean_object* v_env_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4112_ = lean_st_ref_get(v_a_2299_);
v_env_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc_ref(v_env_4113_);
lean_dec(v___x_4112_);
lean_inc_n(v_stx_2293_, 2);
v___x_4114_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_4115_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4116_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4115_, v_env_4113_, v___x_4114_);
v___x_4117_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4118_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_4116_, v___x_4117_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4149_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4149_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4149_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v_fst_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4147_; 
v_fst_4123_ = lean_ctor_get(v_a_4119_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v_a_4119_);
if (v_isSharedCheck_4147_ == 0)
{
lean_object* v_unused_4148_; 
v_unused_4148_ = lean_ctor_get(v_a_4119_, 1);
lean_dec(v_unused_4148_);
v___x_4125_ = v_a_4119_;
v_isShared_4126_ = v_isSharedCheck_4147_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_fst_4123_);
lean_dec(v_a_4119_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4147_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
if (lean_obj_tag(v_fst_4123_) == 0)
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
lean_del_object(v___x_4121_);
v___x_4127_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4128_ = l_Lean_MessageData_ofName(v___x_4114_);
lean_inc_ref(v___x_4128_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set_tag(v___x_4125_, 7);
lean_ctor_set(v___x_4125_, 1, v___x_4128_);
lean_ctor_set(v___x_4125_, 0, v___x_4127_);
v___x_4130_ = v___x_4125_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4127_);
lean_ctor_set(v_reuseFailAlloc_4142_, 1, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4131_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4130_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_4134_ = l_Lean_indentD(v___x_4133_);
v___x_4135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4132_);
lean_ctor_set(v___x_4135_, 1, v___x_4134_);
v___x_4136_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4135_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
lean_ctor_set(v___x_4138_, 1, v___x_4128_);
v___x_4139_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4140_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_4141_;
}
}
else
{
lean_object* v_val_4143_; lean_object* v___x_4145_; 
lean_del_object(v___x_4125_);
lean_dec(v___x_4114_);
lean_dec(v_stx_2293_);
v_val_4143_ = lean_ctor_get(v_fst_4123_, 0);
lean_inc(v_val_4143_);
lean_dec_ref(v_fst_4123_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v_val_4143_);
v___x_4145_ = v___x_4121_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_val_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec(v___x_4114_);
lean_dec(v_stx_2293_);
v_a_4150_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4118_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4118_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
lean_dec(v_stx_2293_);
v___x_4158_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
return v___x_4159_;
}
}
}
}
}
}
else
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; 
v___x_4160_ = lean_unsigned_to_nat(1u);
v___x_4161_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_4160_);
v___x_4162_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4163_ = l_Lean_Syntax_isOfKind(v___x_4161_, v___x_4162_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; lean_object* v_env_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4164_ = lean_st_ref_get(v_a_2299_);
v_env_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc_ref(v_env_4165_);
lean_dec(v___x_4164_);
lean_inc_n(v_stx_2293_, 2);
v___x_4166_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_4167_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4168_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4167_, v_env_4165_, v___x_4166_);
v___x_4169_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4170_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_4168_, v___x_4169_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4201_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4173_ = v___x_4170_;
v_isShared_4174_ = v_isSharedCheck_4201_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4201_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v_fst_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4199_; 
v_fst_4175_ = lean_ctor_get(v_a_4171_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v_a_4171_);
if (v_isSharedCheck_4199_ == 0)
{
lean_object* v_unused_4200_; 
v_unused_4200_ = lean_ctor_get(v_a_4171_, 1);
lean_dec(v_unused_4200_);
v___x_4177_ = v_a_4171_;
v_isShared_4178_ = v_isSharedCheck_4199_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_fst_4175_);
lean_dec(v_a_4171_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4199_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
if (lean_obj_tag(v_fst_4175_) == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4182_; 
lean_del_object(v___x_4173_);
v___x_4179_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4180_ = l_Lean_MessageData_ofName(v___x_4166_);
lean_inc_ref(v___x_4180_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set_tag(v___x_4177_, 7);
lean_ctor_set(v___x_4177_, 1, v___x_4180_);
lean_ctor_set(v___x_4177_, 0, v___x_4179_);
v___x_4182_ = v___x_4177_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4183_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4182_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
v___x_4185_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_4186_ = l_Lean_indentD(v___x_4185_);
v___x_4187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4184_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4187_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set(v___x_4190_, 1, v___x_4180_);
v___x_4191_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4190_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4192_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_4193_;
}
}
else
{
lean_object* v_val_4195_; lean_object* v___x_4197_; 
lean_del_object(v___x_4177_);
lean_dec(v___x_4166_);
lean_dec(v_stx_2293_);
v_val_4195_ = lean_ctor_get(v_fst_4175_, 0);
lean_inc(v_val_4195_);
lean_dec_ref(v_fst_4175_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v_val_4195_);
v___x_4197_ = v___x_4173_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_val_4195_);
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
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec(v___x_4166_);
lean_dec(v_stx_2293_);
v_a_4202_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4170_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4170_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
else
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4210_ = lean_unsigned_to_nat(2u);
v___x_4211_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_4210_);
v___x_4212_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4213_ = l_Lean_Syntax_isOfKind(v___x_4211_, v___x_4212_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v_env_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4214_ = lean_st_ref_get(v_a_2299_);
v_env_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc_ref(v_env_4215_);
lean_dec(v___x_4214_);
lean_inc_n(v_stx_2293_, 2);
v___x_4216_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_4217_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4218_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4217_, v_env_4215_, v___x_4216_);
v___x_4219_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4220_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_4218_, v___x_4219_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4251_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4251_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4251_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v_fst_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4249_; 
v_fst_4225_ = lean_ctor_get(v_a_4221_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v_a_4221_);
if (v_isSharedCheck_4249_ == 0)
{
lean_object* v_unused_4250_; 
v_unused_4250_ = lean_ctor_get(v_a_4221_, 1);
lean_dec(v_unused_4250_);
v___x_4227_ = v_a_4221_;
v_isShared_4228_ = v_isSharedCheck_4249_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_fst_4225_);
lean_dec(v_a_4221_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4249_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
if (lean_obj_tag(v_fst_4225_) == 0)
{
lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4232_; 
lean_del_object(v___x_4223_);
v___x_4229_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4230_ = l_Lean_MessageData_ofName(v___x_4216_);
lean_inc_ref(v___x_4230_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set_tag(v___x_4227_, 7);
lean_ctor_set(v___x_4227_, 1, v___x_4230_);
lean_ctor_set(v___x_4227_, 0, v___x_4229_);
v___x_4232_ = v___x_4227_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4229_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v___x_4230_);
v___x_4232_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4233_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4232_);
lean_ctor_set(v___x_4234_, 1, v___x_4233_);
v___x_4235_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_4236_ = l_Lean_indentD(v___x_4235_);
v___x_4237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4234_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
lean_ctor_set(v___x_4240_, 1, v___x_4230_);
v___x_4241_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4240_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
v___x_4243_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4242_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_4243_;
}
}
else
{
lean_object* v_val_4245_; lean_object* v___x_4247_; 
lean_del_object(v___x_4227_);
lean_dec(v___x_4216_);
lean_dec(v_stx_2293_);
v_val_4245_ = lean_ctor_get(v_fst_4225_, 0);
lean_inc(v_val_4245_);
lean_dec_ref(v_fst_4225_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v_val_4245_);
v___x_4247_ = v___x_4223_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_val_4245_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v___x_4216_);
lean_dec(v_stx_2293_);
v_a_4252_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4220_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4220_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_dec(v_stx_2293_);
v___x_4260_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
return v___x_4261_;
}
}
}
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; uint8_t v___x_4264_; 
v___x_4262_ = lean_unsigned_to_nat(1u);
v___x_4263_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_4262_);
v___x_4264_ = l_Lean_Syntax_isNone(v___x_4263_);
if (v___x_4264_ == 0)
{
uint8_t v___x_4265_; 
v___x_4265_ = l_Lean_Syntax_matchesNull(v___x_4263_, v___x_4262_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; lean_object* v_env_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
lean_del_object(v___x_2330_);
v___x_4266_ = lean_st_ref_get(v_a_2299_);
v_env_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc_ref(v_env_4267_);
lean_dec(v___x_4266_);
lean_inc_n(v_stx_2293_, 2);
v___x_4268_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_4269_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4270_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4269_, v_env_4267_, v___x_4268_);
v___x_4271_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4272_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_4270_, v___x_4271_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4303_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4275_ = v___x_4272_;
v_isShared_4276_ = v_isSharedCheck_4303_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4272_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4303_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v_fst_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4301_; 
v_fst_4277_ = lean_ctor_get(v_a_4273_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v_a_4273_);
if (v_isSharedCheck_4301_ == 0)
{
lean_object* v_unused_4302_; 
v_unused_4302_ = lean_ctor_get(v_a_4273_, 1);
lean_dec(v_unused_4302_);
v___x_4279_ = v_a_4273_;
v_isShared_4280_ = v_isSharedCheck_4301_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_fst_4277_);
lean_dec(v_a_4273_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4301_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
if (lean_obj_tag(v_fst_4277_) == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4284_; 
lean_del_object(v___x_4275_);
v___x_4281_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4282_ = l_Lean_MessageData_ofName(v___x_4268_);
lean_inc_ref(v___x_4282_);
if (v_isShared_4280_ == 0)
{
lean_ctor_set_tag(v___x_4279_, 7);
lean_ctor_set(v___x_4279_, 1, v___x_4282_);
lean_ctor_set(v___x_4279_, 0, v___x_4281_);
v___x_4284_ = v___x_4279_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4281_);
lean_ctor_set(v_reuseFailAlloc_4296_, 1, v___x_4282_);
v___x_4284_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4285_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4284_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_4288_ = l_Lean_indentD(v___x_4287_);
v___x_4289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4286_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
v___x_4290_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4289_);
lean_ctor_set(v___x_4291_, 1, v___x_4290_);
v___x_4292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4291_);
lean_ctor_set(v___x_4292_, 1, v___x_4282_);
v___x_4293_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4292_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4294_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_4295_;
}
}
else
{
lean_object* v_val_4297_; lean_object* v___x_4299_; 
lean_del_object(v___x_4279_);
lean_dec(v___x_4268_);
lean_dec(v_stx_2293_);
v_val_4297_ = lean_ctor_get(v_fst_4277_, 0);
lean_inc(v_val_4297_);
lean_dec_ref(v_fst_4277_);
if (v_isShared_4276_ == 0)
{
lean_ctor_set(v___x_4275_, 0, v_val_4297_);
v___x_4299_ = v___x_4275_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_val_4297_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec(v___x_4268_);
lean_dec(v_stx_2293_);
v_a_4304_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4272_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4272_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
else
{
v___y_2418_ = v_a_2294_;
v___y_2419_ = v_a_2295_;
v___y_2420_ = v_a_2296_;
v___y_2421_ = v_a_2297_;
v___y_2422_ = v_a_2298_;
v___y_2423_ = v_a_2299_;
goto v___jp_2417_;
}
}
else
{
lean_dec(v___x_4263_);
v___y_2418_ = v_a_2294_;
v___y_2419_ = v_a_2295_;
v___y_2420_ = v_a_2296_;
v___y_2421_ = v_a_2297_;
v___y_2422_ = v_a_2298_;
v___y_2423_ = v_a_2299_;
goto v___jp_2417_;
}
}
}
else
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
lean_del_object(v___x_2330_);
v___x_4312_ = lean_unsigned_to_nat(1u);
v___x_4313_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_4312_);
lean_dec(v_stx_2293_);
v___x_4314_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4313_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_4314_;
}
}
else
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
lean_del_object(v___x_2330_);
lean_dec(v_stx_2293_);
v___x_4315_ = lean_unsigned_to_nat(1u);
v___x_4316_ = l_Lean_NameSet_empty;
v___x_4317_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4317_, 0, v___x_4315_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
lean_ctor_set_uint8(v___x_4317_, sizeof(void*)*2, v___x_2534_);
lean_ctor_set_uint8(v___x_4317_, sizeof(void*)*2 + 1, v___x_2534_);
lean_ctor_set_uint8(v___x_4317_, sizeof(void*)*2 + 2, v___x_2534_);
v___x_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4317_);
return v___x_4318_;
}
}
else
{
lean_object* v___x_4319_; lean_object* v___x_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
lean_del_object(v___x_2330_);
v___x_4319_ = lean_unsigned_to_nat(0u);
v___x_4324_ = lean_unsigned_to_nat(1u);
v___x_4325_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_4324_);
v___x_4326_ = l_Lean_Syntax_isNone(v___x_4325_);
if (v___x_4326_ == 0)
{
uint8_t v___x_4327_; 
v___x_4327_ = l_Lean_Syntax_matchesNull(v___x_4325_, v___x_4324_);
if (v___x_4327_ == 0)
{
lean_object* v___x_4328_; lean_object* v_env_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4328_ = lean_st_ref_get(v_a_2299_);
v_env_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc_ref(v_env_4329_);
lean_dec(v___x_4328_);
lean_inc_n(v_stx_2293_, 2);
v___x_4330_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_4331_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4332_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4331_, v_env_4329_, v___x_4330_);
v___x_4333_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4334_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_4332_, v___x_4333_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4365_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4337_ = v___x_4334_;
v_isShared_4338_ = v_isSharedCheck_4365_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4334_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4365_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v_fst_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4363_; 
v_fst_4339_ = lean_ctor_get(v_a_4335_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v_a_4335_);
if (v_isSharedCheck_4363_ == 0)
{
lean_object* v_unused_4364_; 
v_unused_4364_ = lean_ctor_get(v_a_4335_, 1);
lean_dec(v_unused_4364_);
v___x_4341_ = v_a_4335_;
v_isShared_4342_ = v_isSharedCheck_4363_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_fst_4339_);
lean_dec(v_a_4335_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4363_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
if (lean_obj_tag(v_fst_4339_) == 0)
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4346_; 
lean_del_object(v___x_4337_);
v___x_4343_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4344_ = l_Lean_MessageData_ofName(v___x_4330_);
lean_inc_ref(v___x_4344_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set_tag(v___x_4341_, 7);
lean_ctor_set(v___x_4341_, 1, v___x_4344_);
lean_ctor_set(v___x_4341_, 0, v___x_4343_);
v___x_4346_ = v___x_4341_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4343_);
lean_ctor_set(v_reuseFailAlloc_4358_, 1, v___x_4344_);
v___x_4346_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4347_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4346_);
lean_ctor_set(v___x_4348_, 1, v___x_4347_);
v___x_4349_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_4350_ = l_Lean_indentD(v___x_4349_);
v___x_4351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4348_);
lean_ctor_set(v___x_4351_, 1, v___x_4350_);
v___x_4352_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4351_);
lean_ctor_set(v___x_4353_, 1, v___x_4352_);
v___x_4354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4353_);
lean_ctor_set(v___x_4354_, 1, v___x_4344_);
v___x_4355_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4354_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
v___x_4357_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4356_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_4357_;
}
}
else
{
lean_object* v_val_4359_; lean_object* v___x_4361_; 
lean_del_object(v___x_4341_);
lean_dec(v___x_4330_);
lean_dec(v_stx_2293_);
v_val_4359_ = lean_ctor_get(v_fst_4339_, 0);
lean_inc(v_val_4359_);
lean_dec_ref(v_fst_4339_);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 0, v_val_4359_);
v___x_4361_ = v___x_4337_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_val_4359_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec(v___x_4330_);
lean_dec(v_stx_2293_);
v_a_4366_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4334_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4334_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
else
{
lean_dec(v_stx_2293_);
goto v___jp_4320_;
}
}
else
{
lean_dec(v___x_4325_);
lean_dec(v_stx_2293_);
goto v___jp_4320_;
}
v___jp_4320_:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4321_ = l_Lean_NameSet_empty;
v___x_4322_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4322_, 0, v___x_4319_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
lean_ctor_set_uint8(v___x_4322_, sizeof(void*)*2, v___x_2532_);
lean_ctor_set_uint8(v___x_4322_, sizeof(void*)*2 + 1, v___x_2532_);
lean_ctor_set_uint8(v___x_4322_, sizeof(void*)*2 + 2, v___x_2530_);
v___x_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
return v___x_4323_;
}
}
}
else
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
lean_del_object(v___x_2330_);
lean_dec(v_stx_2293_);
v___x_4374_ = lean_unsigned_to_nat(0u);
v___x_4375_ = l_Lean_NameSet_empty;
v___x_4376_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4376_, 0, v___x_4374_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
lean_ctor_set_uint8(v___x_4376_, sizeof(void*)*2, v___x_2529_);
lean_ctor_set_uint8(v___x_4376_, sizeof(void*)*2 + 1, v___x_2530_);
lean_ctor_set_uint8(v___x_4376_, sizeof(void*)*2 + 2, v___x_2529_);
v___x_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
return v___x_4377_;
}
}
else
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
lean_del_object(v___x_2330_);
lean_dec(v_stx_2293_);
v___x_4378_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80);
v___x_4379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
return v___x_4379_;
}
v___jp_2346_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2353_ = lean_unsigned_to_nat(2u);
v___x_2354_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2353_);
v___x_2355_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2356_ = l_Lean_Syntax_isOfKind(v___x_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v_env_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2357_ = lean_st_ref_get(v___y_2352_);
v_env_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc_ref(v_env_2358_);
lean_dec(v___x_2357_);
lean_inc_n(v_stx_2293_, 2);
v___x_2359_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2360_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2361_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2360_, v_env_2358_, v___x_2359_);
v___x_2362_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2363_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2361_, v___x_2362_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2394_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2394_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2394_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_fst_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2392_; 
v_fst_2368_ = lean_ctor_get(v_a_2364_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_a_2364_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v_a_2364_, 1);
lean_dec(v_unused_2393_);
v___x_2370_ = v_a_2364_;
v_isShared_2371_ = v_isSharedCheck_2392_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_fst_2368_);
lean_dec(v_a_2364_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2392_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
if (lean_obj_tag(v_fst_2368_) == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
lean_del_object(v___x_2366_);
v___x_2372_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2373_ = l_Lean_MessageData_ofName(v___x_2359_);
lean_inc_ref(v___x_2373_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set_tag(v___x_2370_, 7);
lean_ctor_set(v___x_2370_, 1, v___x_2373_);
lean_ctor_set(v___x_2370_, 0, v___x_2372_);
v___x_2375_ = v___x_2370_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2376_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2379_ = l_Lean_indentD(v___x_2378_);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2377_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v___x_2373_);
v___x_2384_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2385_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
return v___x_2386_;
}
}
else
{
lean_object* v_val_2388_; lean_object* v___x_2390_; 
lean_del_object(v___x_2370_);
lean_dec(v___x_2359_);
lean_dec(v_stx_2293_);
v_val_2388_ = lean_ctor_get(v_fst_2368_, 0);
lean_inc(v_val_2388_);
lean_dec_ref(v_fst_2368_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v_val_2388_);
v___x_2390_ = v___x_2366_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_val_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v___x_2359_);
lean_dec(v_stx_2293_);
v_a_2395_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2363_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2363_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2403_ = lean_unsigned_to_nat(7u);
v___x_2404_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2403_);
v___x_2405_ = lean_unsigned_to_nat(8u);
v___x_2406_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2405_);
lean_dec(v_stx_2293_);
v___x_2407_ = l_Lean_Syntax_getOptional_x3f(v___x_2406_);
lean_dec(v___x_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_box(0);
v___y_2302_ = v___y_2349_;
v___y_2303_ = v___y_2347_;
v___y_2304_ = v___x_2404_;
v___y_2305_ = v___y_2348_;
v___y_2306_ = v___y_2350_;
v___y_2307_ = v___y_2352_;
v___y_2308_ = v___y_2351_;
v___y_2309_ = v___x_2408_;
goto v___jp_2301_;
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_val_2409_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2407_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_val_2409_);
lean_dec(v___x_2407_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_val_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
v___y_2302_ = v___y_2349_;
v___y_2303_ = v___y_2347_;
v___y_2304_ = v___x_2404_;
v___y_2305_ = v___y_2348_;
v___y_2306_ = v___y_2350_;
v___y_2307_ = v___y_2352_;
v___y_2308_ = v___y_2351_;
v___y_2309_ = v___x_2414_;
goto v___jp_2301_;
}
}
}
}
}
v___jp_2417_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2424_ = lean_unsigned_to_nat(2u);
v___x_2425_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2424_);
v___x_2426_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2427_ = l_Lean_Syntax_isOfKind(v___x_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v_env_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_del_object(v___x_2330_);
v___x_2428_ = lean_st_ref_get(v___y_2423_);
v_env_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc_ref(v_env_2429_);
lean_dec(v___x_2428_);
lean_inc_n(v_stx_2293_, 2);
v___x_2430_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2431_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2432_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2431_, v_env_2429_, v___x_2430_);
v___x_2433_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2434_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2432_, v___x_2433_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2465_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2465_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2465_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v_fst_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2463_; 
v_fst_2439_ = lean_ctor_get(v_a_2435_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_a_2435_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v_a_2435_, 1);
lean_dec(v_unused_2464_);
v___x_2441_ = v_a_2435_;
v_isShared_2442_ = v_isSharedCheck_2463_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_fst_2439_);
lean_dec(v_a_2435_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2463_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
if (lean_obj_tag(v_fst_2439_) == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_del_object(v___x_2437_);
v___x_2443_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2444_ = l_Lean_MessageData_ofName(v___x_2430_);
lean_inc_ref(v___x_2444_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set_tag(v___x_2441_, 7);
lean_ctor_set(v___x_2441_, 1, v___x_2444_);
lean_ctor_set(v___x_2441_, 0, v___x_2443_);
v___x_2446_ = v___x_2441_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2447_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2450_ = l_Lean_indentD(v___x_2449_);
v___x_2451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2448_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
lean_ctor_set(v___x_2454_, 1, v___x_2444_);
v___x_2455_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2456_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2457_;
}
}
else
{
lean_object* v_val_2459_; lean_object* v___x_2461_; 
lean_del_object(v___x_2441_);
lean_dec(v___x_2430_);
lean_dec(v_stx_2293_);
v_val_2459_ = lean_ctor_get(v_fst_2439_, 0);
lean_inc(v_val_2459_);
lean_dec_ref(v_fst_2439_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v_val_2459_);
v___x_2461_ = v___x_2437_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_val_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v___x_2430_);
lean_dec(v_stx_2293_);
v_a_2466_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2434_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2434_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2474_ = lean_unsigned_to_nat(3u);
v___x_2475_ = l_Lean_Syntax_getArg(v_stx_2293_, v___x_2474_);
v___x_2476_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2477_ = l_Lean_Syntax_isOfKind(v___x_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; lean_object* v_env_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_del_object(v___x_2330_);
v___x_2478_ = lean_st_ref_get(v___y_2423_);
v_env_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc_ref(v_env_2479_);
lean_dec(v___x_2478_);
lean_inc_n(v_stx_2293_, 2);
v___x_2480_ = l_Lean_Syntax_getKind(v_stx_2293_);
v___x_2481_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2482_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2481_, v_env_2479_, v___x_2480_);
v___x_2483_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2484_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2293_, v___x_2482_, v___x_2483_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2515_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2515_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2515_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v_fst_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2513_; 
v_fst_2489_ = lean_ctor_get(v_a_2485_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_a_2485_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v_a_2485_, 1);
lean_dec(v_unused_2514_);
v___x_2491_ = v_a_2485_;
v_isShared_2492_ = v_isSharedCheck_2513_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_fst_2489_);
lean_dec(v_a_2485_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2513_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
if (lean_obj_tag(v_fst_2489_) == 0)
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_del_object(v___x_2487_);
v___x_2493_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2494_ = l_Lean_MessageData_ofName(v___x_2480_);
lean_inc_ref(v___x_2494_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 7);
lean_ctor_set(v___x_2491_, 1, v___x_2494_);
lean_ctor_set(v___x_2491_, 0, v___x_2493_);
v___x_2496_ = v___x_2491_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2497_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = l_Lean_MessageData_ofSyntax(v_stx_2293_);
v___x_2500_ = l_Lean_indentD(v___x_2499_);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2498_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v___x_2494_);
v___x_2505_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2506_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2507_;
}
}
else
{
lean_object* v_val_2509_; lean_object* v___x_2511_; 
lean_del_object(v___x_2491_);
lean_dec(v___x_2480_);
lean_dec(v_stx_2293_);
v_val_2509_ = lean_ctor_get(v_fst_2489_, 0);
lean_inc(v_val_2509_);
lean_dec_ref(v_fst_2489_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v_val_2509_);
v___x_2511_ = v___x_2487_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_val_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v___x_2480_);
lean_dec(v_stx_2293_);
v_a_2516_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2484_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2484_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2526_; 
lean_dec(v_stx_2293_);
v___x_2524_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2524_);
v___x_2526_ = v___x_2330_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec(v_stx_2293_);
v_a_4381_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_2327_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_2327_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
v___jp_2301_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2310_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___y_2304_);
v___x_2313_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2310_, v___x_2311_, v___x_2312_, v___y_2309_, v___y_2303_, v___y_2305_, v___y_2302_, v___y_2306_, v___y_2308_, v___y_2307_);
return v___x_2313_;
}
v___jp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2315_, v_bodyInfo_2316_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
v___jp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2320_, v_bodyInfo_2321_);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4389_, size_t v_sz_4390_, size_t v_i_4391_, lean_object* v_b_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
uint8_t v___x_4400_; 
v___x_4400_ = lean_usize_dec_lt(v_i_4391_, v_sz_4390_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; 
v___x_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4401_, 0, v_b_4392_);
return v___x_4401_;
}
else
{
uint8_t v_breaks_4402_; uint8_t v_continues_4403_; uint8_t v_returnsEarly_4404_; lean_object* v_numRegularExits_4405_; lean_object* v_reassigns_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v_breaks_4402_ = lean_ctor_get_uint8(v_b_4392_, sizeof(void*)*2);
v_continues_4403_ = lean_ctor_get_uint8(v_b_4392_, sizeof(void*)*2 + 1);
v_returnsEarly_4404_ = lean_ctor_get_uint8(v_b_4392_, sizeof(void*)*2 + 2);
v_numRegularExits_4405_ = lean_ctor_get(v_b_4392_, 0);
v_reassigns_4406_ = lean_ctor_get(v_b_4392_, 1);
v___x_4407_ = lean_unsigned_to_nat(0u);
v___x_4408_ = lean_nat_dec_eq(v_numRegularExits_4405_, v___x_4407_);
if (v___x_4408_ == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4410_; 
lean_inc(v_reassigns_4406_);
lean_dec_ref(v_b_4392_);
v_a_4409_ = lean_array_uget_borrowed(v_as_4389_, v_i_4391_);
lean_inc(v_a_4409_);
v___x_4410_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4409_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; uint8_t v___y_4413_; uint8_t v___y_4414_; uint8_t v___y_4415_; uint8_t v___y_4430_; uint8_t v___y_4431_; uint8_t v___y_4434_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref(v___x_4410_);
if (v_breaks_4402_ == 0)
{
uint8_t v_breaks_4436_; 
v_breaks_4436_ = lean_ctor_get_uint8(v_a_4411_, sizeof(void*)*2);
v___y_4434_ = v_breaks_4436_;
goto v___jp_4433_;
}
else
{
v___y_4434_ = v___x_4400_;
goto v___jp_4433_;
}
v___jp_4412_:
{
lean_object* v_numRegularExits_4416_; lean_object* v_reassigns_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4428_; 
v_numRegularExits_4416_ = lean_ctor_get(v_a_4411_, 0);
v_reassigns_4417_ = lean_ctor_get(v_a_4411_, 1);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_a_4411_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4419_ = v_a_4411_;
v_isShared_4420_ = v_isSharedCheck_4428_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_reassigns_4417_);
lean_inc(v_numRegularExits_4416_);
lean_dec(v_a_4411_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4428_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4421_ = l_Lean_NameSet_append(v_reassigns_4406_, v_reassigns_4417_);
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 1, v___x_4421_);
v___x_4423_ = v___x_4419_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_numRegularExits_4416_);
lean_ctor_set(v_reuseFailAlloc_4427_, 1, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
size_t v___x_4424_; size_t v___x_4425_; 
lean_ctor_set_uint8(v___x_4423_, sizeof(void*)*2, v___y_4413_);
lean_ctor_set_uint8(v___x_4423_, sizeof(void*)*2 + 1, v___y_4414_);
lean_ctor_set_uint8(v___x_4423_, sizeof(void*)*2 + 2, v___y_4415_);
v___x_4424_ = ((size_t)1ULL);
v___x_4425_ = lean_usize_add(v_i_4391_, v___x_4424_);
v_i_4391_ = v___x_4425_;
v_b_4392_ = v___x_4423_;
goto _start;
}
}
}
v___jp_4429_:
{
if (v_returnsEarly_4404_ == 0)
{
uint8_t v_returnsEarly_4432_; 
v_returnsEarly_4432_ = lean_ctor_get_uint8(v_a_4411_, sizeof(void*)*2 + 2);
v___y_4413_ = v___y_4430_;
v___y_4414_ = v___y_4431_;
v___y_4415_ = v_returnsEarly_4432_;
goto v___jp_4412_;
}
else
{
v___y_4413_ = v___y_4430_;
v___y_4414_ = v___y_4431_;
v___y_4415_ = v___x_4400_;
goto v___jp_4412_;
}
}
v___jp_4433_:
{
if (v_continues_4403_ == 0)
{
uint8_t v_continues_4435_; 
v_continues_4435_ = lean_ctor_get_uint8(v_a_4411_, sizeof(void*)*2 + 1);
v___y_4430_ = v___y_4434_;
v___y_4431_ = v_continues_4435_;
goto v___jp_4429_;
}
else
{
v___y_4430_ = v___y_4434_;
v___y_4431_ = v___x_4400_;
goto v___jp_4429_;
}
}
}
else
{
lean_dec(v_reassigns_4406_);
return v___x_4410_;
}
}
else
{
lean_object* v___x_4437_; 
v___x_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4437_, 0, v_b_4392_);
return v___x_4437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v_info_4446_; lean_object* v___x_4447_; size_t v_sz_4448_; size_t v___x_4449_; lean_object* v___x_4450_; 
v_info_4446_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
v___x_4447_ = l_Lean_Parser_Term_getDoElems(v_stx_4438_);
v_sz_4448_ = lean_array_size(v___x_4447_);
v___x_4449_ = ((size_t)0ULL);
v___x_4450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4447_, v_sz_4448_, v___x_4449_, v_info_4446_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
lean_dec_ref(v___x_4447_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_);
lean_dec(v_a_4457_);
lean_dec_ref(v_a_4456_);
lean_dec(v_a_4455_);
lean_dec_ref(v_a_4454_);
lean_dec(v_a_4453_);
lean_dec_ref(v_a_4452_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
lean_dec(v_a_4462_);
lean_dec_ref(v_a_4461_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4469_, lean_object* v_sz_4470_, lean_object* v_i_4471_, lean_object* v_b_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
size_t v_sz_boxed_4480_; size_t v_i_boxed_4481_; lean_object* v_res_4482_; 
v_sz_boxed_4480_ = lean_unbox_usize(v_sz_4470_);
lean_dec(v_sz_4470_);
v_i_boxed_4481_ = lean_unbox_usize(v_i_4471_);
lean_dec(v_i_4471_);
v_res_4482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4469_, v_sz_boxed_4480_, v_i_boxed_4481_, v_b_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec_ref(v_as_4469_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4483_, lean_object* v_sz_4484_, lean_object* v_i_4485_, lean_object* v_b_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
size_t v_sz_boxed_4494_; size_t v_i_boxed_4495_; lean_object* v_res_4496_; 
v_sz_boxed_4494_ = lean_unbox_usize(v_sz_4484_);
lean_dec(v_sz_4484_);
v_i_boxed_4495_ = lean_unbox_usize(v_i_4485_);
lean_dec(v_i_4485_);
v_res_4496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4483_, v_sz_boxed_4494_, v_i_boxed_4495_, v_b_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec_ref(v_as_4483_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_4497_, lean_object* v_rhs_x3f_4498_, lean_object* v_otherwise_x3f_4499_, lean_object* v_body_x3f_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_4497_, v_rhs_x3f_4498_, v_otherwise_x3f_4499_, v_body_x3f_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4509_, lean_object* v_as_4510_, lean_object* v_sz_4511_, lean_object* v_i_4512_, lean_object* v_b_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
uint8_t v___x_286862__boxed_4521_; size_t v_sz_boxed_4522_; size_t v_i_boxed_4523_; lean_object* v_res_4524_; 
v___x_286862__boxed_4521_ = lean_unbox(v___x_4509_);
v_sz_boxed_4522_ = lean_unbox_usize(v_sz_4511_);
lean_dec(v_sz_4511_);
v_i_boxed_4523_ = lean_unbox_usize(v_i_4512_);
lean_dec(v_i_4512_);
v_res_4524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_286862__boxed_4521_, v_as_4510_, v_sz_boxed_4522_, v_i_boxed_4523_, v_b_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec_ref(v_as_4510_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4525_, lean_object* v_as_4526_, lean_object* v_sz_4527_, lean_object* v_i_4528_, lean_object* v_b_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
uint8_t v___x_286913__boxed_4537_; size_t v_sz_boxed_4538_; size_t v_i_boxed_4539_; lean_object* v_res_4540_; 
v___x_286913__boxed_4537_ = lean_unbox(v___x_4525_);
v_sz_boxed_4538_ = lean_unbox_usize(v_sz_4527_);
lean_dec(v_sz_4527_);
v_i_boxed_4539_ = lean_unbox_usize(v_i_4528_);
lean_dec(v_i_4528_);
v_res_4540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_286913__boxed_4537_, v_as_4526_, v_sz_boxed_4538_, v_i_boxed_4539_, v_b_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec_ref(v_as_4526_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_4541_, lean_object* v_sz_4542_, lean_object* v_i_4543_, lean_object* v_b_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
size_t v_sz_boxed_4552_; size_t v_i_boxed_4553_; lean_object* v_res_4554_; 
v_sz_boxed_4552_ = lean_unbox_usize(v_sz_4542_);
lean_dec(v_sz_4542_);
v_i_boxed_4553_ = lean_unbox_usize(v_i_4543_);
lean_dec(v_i_4543_);
v_res_4554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_4541_, v_sz_boxed_4552_, v_i_boxed_4553_, v_b_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec_ref(v_as_4541_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_4555_, lean_object* v_decl_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_){
_start:
{
uint8_t v_reassignment_boxed_4564_; lean_object* v_res_4565_; 
v_reassignment_boxed_4564_ = lean_unbox(v_reassignment_4555_);
v_res_4565_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_4564_, v_decl_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
lean_dec(v_a_4560_);
lean_dec_ref(v_a_4559_);
lean_dec(v_a_4558_);
lean_dec_ref(v_a_4557_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_);
lean_dec(v_a_4572_);
lean_dec_ref(v_a_4571_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* v_00_u03b1_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v___x_4583_; 
v___x_4583_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_00_u03b1_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_00_u03b1_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_4593_, lean_object* v_ref_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_4594_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_4603_, lean_object* v_ref_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_4603_, v_ref_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_4613_, lean_object* v_x_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v___x_4622_; 
v___x_4622_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_4623_, lean_object* v_x_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_4623_, v_x_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_4633_, lean_object* v_as_4634_, lean_object* v_as_x27_4635_, lean_object* v_b_4636_, lean_object* v_a_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_4633_, v_as_x27_4635_, v_b_4636_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_4646_, lean_object* v_as_4647_, lean_object* v_as_x27_4648_, lean_object* v_b_4649_, lean_object* v_a_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_4646_, v_as_4647_, v_as_x27_4648_, v_b_4649_, v_a_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v_as_4647_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_4659_, lean_object* v_msg_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_4669_, lean_object* v_msg_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_4669_, v_msg_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
return v_res_4678_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_4679_, lean_object* v_msg_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_4679_, v_msg_4680_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_4689_, lean_object* v_msg_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_4689_, v_msg_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_4699_, lean_object* v_as_x27_4700_, lean_object* v_b_4701_, lean_object* v_a_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_4700_, v_b_4701_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_4711_, lean_object* v_as_x27_4712_, lean_object* v_b_4713_, lean_object* v_a_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_4711_, v_as_x27_4712_, v_b_4713_, v_a_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v_as_4711_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_4723_, lean_object* v_ref_4724_, lean_object* v_msg_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_4724_, v_msg_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_4734_, lean_object* v_ref_4735_, lean_object* v_msg_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_){
_start:
{
lean_object* v_res_4744_; 
v_res_4744_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_4734_, v_ref_4735_, v_msg_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_);
lean_dec(v___y_4742_);
lean_dec_ref(v___y_4741_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v_ref_4735_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_4745_, lean_object* v_macroStack_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_){
_start:
{
lean_object* v___x_4754_; 
v___x_4754_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_4745_, v_macroStack_4746_, v___y_4751_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_4755_, lean_object* v_macroStack_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_4755_, v_macroStack_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec(v___y_4758_);
lean_dec_ref(v___y_4757_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_4765_, lean_object* v_m_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v___x_4768_; 
v___x_4768_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_4766_, v_a_4767_);
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_4769_, lean_object* v_m_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_4769_, v_m_4770_, v_a_4771_);
lean_dec(v_a_4771_);
lean_dec_ref(v_m_4770_);
return v_res_4772_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_4773_, lean_object* v_x_4774_, lean_object* v_x_4775_){
_start:
{
uint8_t v___x_4776_; 
v___x_4776_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_4774_, v_x_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_4777_, lean_object* v_x_4778_, lean_object* v_x_4779_){
_start:
{
uint8_t v_res_4780_; lean_object* v_r_4781_; 
v_res_4780_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_4777_, v_x_4778_, v_x_4779_);
lean_dec_ref(v_x_4779_);
lean_dec_ref(v_x_4778_);
v_r_4781_ = lean_box(v_res_4780_);
return v_r_4781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_4782_, lean_object* v_a_4783_, lean_object* v_x_4784_){
_start:
{
lean_object* v___x_4785_; 
v___x_4785_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_4783_, v_x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_4786_, lean_object* v_a_4787_, lean_object* v_x_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_4786_, v_a_4787_, v_x_4788_);
lean_dec(v_x_4788_);
lean_dec(v_a_4787_);
return v_res_4789_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_4790_, lean_object* v_x_4791_, size_t v_x_4792_, lean_object* v_x_4793_){
_start:
{
uint8_t v___x_4794_; 
v___x_4794_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_4791_, v_x_4792_, v_x_4793_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4795_, lean_object* v_x_4796_, lean_object* v_x_4797_, lean_object* v_x_4798_){
_start:
{
size_t v_x_292631__boxed_4799_; uint8_t v_res_4800_; lean_object* v_r_4801_; 
v_x_292631__boxed_4799_ = lean_unbox_usize(v_x_4797_);
lean_dec(v_x_4797_);
v_res_4800_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_4795_, v_x_4796_, v_x_292631__boxed_4799_, v_x_4798_);
lean_dec_ref(v_x_4798_);
lean_dec_ref(v_x_4796_);
v_r_4801_ = lean_box(v_res_4800_);
return v_r_4801_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_4802_, lean_object* v_keys_4803_, lean_object* v_vals_4804_, lean_object* v_heq_4805_, lean_object* v_i_4806_, lean_object* v_k_4807_){
_start:
{
uint8_t v___x_4808_; 
v___x_4808_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_4803_, v_i_4806_, v_k_4807_);
return v___x_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_4809_, lean_object* v_keys_4810_, lean_object* v_vals_4811_, lean_object* v_heq_4812_, lean_object* v_i_4813_, lean_object* v_k_4814_){
_start:
{
uint8_t v_res_4815_; lean_object* v_r_4816_; 
v_res_4815_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_4809_, v_keys_4810_, v_vals_4811_, v_heq_4812_, v_i_4813_, v_k_4814_);
lean_dec_ref(v_k_4814_);
lean_dec_ref(v_vals_4811_);
lean_dec_ref(v_keys_4810_);
v_r_4816_ = lean_box(v_res_4815_);
return v_r_4816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_){
_start:
{
lean_object* v___x_4825_; 
v___x_4825_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_);
lean_dec(v_a_4832_);
lean_dec_ref(v_a_4831_);
lean_dec(v_a_4830_);
lean_dec_ref(v_a_4829_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_);
lean_dec(v_a_4850_);
lean_dec_ref(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
lean_dec(v_a_4846_);
lean_dec_ref(v_a_4845_);
return v_res_4852_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Term(builtin);
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
res = l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Do_controlInfoElemAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Do_controlInfoElemAttribute);
lean_dec_ref(res);
res = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
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
