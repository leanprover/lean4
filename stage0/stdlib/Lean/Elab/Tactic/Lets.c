// Lean compiler output
// Module: Lean.Elab.Tactic.Lets
// Imports: public import Lean.Meta.Tactic.Lets public import Lean.Elab.Tactic.Location import Lean.Elab.Binders import Lean.Linter.Basic
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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
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
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_MVarId_letToHave(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_register_option(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_liftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
lean_object* l_Lean_MVarId_extractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "unusedName"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(206, 206, 61, 199, 208, 244, 88, 253)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 220, 201, 55, 250, 95, 85, 187)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "enable the 'unused name' tactic linter"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 218, 239, 141, 209, 224, 98, 123)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 199, 243, 68, 217, 216, 62, 142)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(57, 222, 21, 214, 118, 132, 172, 125)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_linter_tactic_unusedName;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unused name"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value;
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ExtractLetsConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Error evaluating configuration\n"};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\n\nException: "};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Configuration contains `sorry`"};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Error evaluating configuration: Environment does not yet contain type "};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9;
static const lean_ctor_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 16, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "'extract_lets' tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLets"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 52, 152, 152, 121, 17, 54, 202)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalExtractLets___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__6_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalExtractLets"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 187, 108, 174, 23, 225, 147, 32)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LiftLetsConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(15, 138, 90, 221, 135, 228, 98, 245)}};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1;
static const lean_ctor_object l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 16, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "'lift_lets' tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLiftLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "liftLets"};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 154, 84, 113, 122, 200, 54, 62)}};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalLiftLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalLiftLets"};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 204, 119, 233, 20, 201, 134, 20)}};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "'let_to_have' tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLetToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 208, 147, 22, 140, 102, 111, 183)}};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalLetToHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalLetToHave"};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 67, 243, 172, 71, 255, 176, 225)}};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_63_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_64_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_65_ = l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4____boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
return v_res_67_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_opts_68_, lean_object* v_opt_69_){
_start:
{
lean_object* v_name_70_; lean_object* v_defValue_71_; lean_object* v_map_72_; lean_object* v___x_73_; 
v_name_70_ = lean_ctor_get(v_opt_69_, 0);
v_defValue_71_ = lean_ctor_get(v_opt_69_, 1);
v_map_72_ = lean_ctor_get(v_opts_68_, 0);
v___x_73_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_72_, v_name_70_);
if (lean_obj_tag(v___x_73_) == 0)
{
uint8_t v___x_74_; 
v___x_74_ = lean_unbox(v_defValue_71_);
return v___x_74_;
}
else
{
lean_object* v_val_75_; 
v_val_75_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v___x_73_);
if (lean_obj_tag(v_val_75_) == 1)
{
uint8_t v_v_76_; 
v_v_76_ = lean_ctor_get_uint8(v_val_75_, 0);
lean_dec_ref(v_val_75_);
return v_v_76_;
}
else
{
uint8_t v___x_77_; 
lean_dec(v_val_75_);
v___x_77_ = lean_unbox(v_defValue_71_);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_opts_78_, lean_object* v_opt_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_opts_78_, v_opt_79_);
lean_dec_ref(v_opt_79_);
lean_dec_ref(v_opts_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msgData_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; lean_object* v_env_89_; lean_object* v___x_90_; lean_object* v_mctx_91_; lean_object* v_lctx_92_; lean_object* v_options_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_88_ = lean_st_ref_get(v___y_86_);
v_env_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_ref(v_env_89_);
lean_dec(v___x_88_);
v___x_90_ = lean_st_ref_get(v___y_84_);
v_mctx_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_mctx_91_);
lean_dec(v___x_90_);
v_lctx_92_ = lean_ctor_get(v___y_83_, 2);
v_options_93_ = lean_ctor_get(v___y_85_, 2);
lean_inc_ref(v_options_93_);
lean_inc_ref(v_lctx_92_);
v___x_94_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_94_, 0, v_env_89_);
lean_ctor_set(v___x_94_, 1, v_mctx_91_);
lean_ctor_set(v___x_94_, 2, v_lctx_92_);
lean_ctor_set(v___x_94_, 3, v_options_93_);
v___x_95_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_msgData_82_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msgData_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msgData_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_103_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(uint8_t v___y_110_, uint8_t v_suppressElabErrors_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 1)
{
lean_object* v_pre_113_; 
v_pre_113_ = lean_ctor_get(v_x_112_, 0);
switch(lean_obj_tag(v_pre_113_))
{
case 1:
{
lean_object* v_pre_114_; 
v_pre_114_ = lean_ctor_get(v_pre_113_, 0);
switch(lean_obj_tag(v_pre_114_))
{
case 0:
{
lean_object* v_str_115_; lean_object* v_str_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_str_115_ = lean_ctor_get(v_x_112_, 1);
v_str_116_ = lean_ctor_get(v_pre_113_, 1);
v___x_117_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_118_ = lean_string_dec_eq(v_str_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_120_ = lean_string_dec_eq(v_str_116_, v___x_119_);
if (v___x_120_ == 0)
{
return v___y_110_;
}
else
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0));
v___x_122_ = lean_string_dec_eq(v_str_115_, v___x_121_);
if (v___x_122_ == 0)
{
return v___y_110_;
}
else
{
return v_suppressElabErrors_111_;
}
}
}
else
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1));
v___x_124_ = lean_string_dec_eq(v_str_115_, v___x_123_);
if (v___x_124_ == 0)
{
return v___y_110_;
}
else
{
return v_suppressElabErrors_111_;
}
}
}
case 1:
{
lean_object* v_pre_125_; 
v_pre_125_ = lean_ctor_get(v_pre_114_, 0);
if (lean_obj_tag(v_pre_125_) == 0)
{
lean_object* v_str_126_; lean_object* v_str_127_; lean_object* v_str_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_str_126_ = lean_ctor_get(v_x_112_, 1);
v_str_127_ = lean_ctor_get(v_pre_113_, 1);
v_str_128_ = lean_ctor_get(v_pre_114_, 1);
v___x_129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2));
v___x_130_ = lean_string_dec_eq(v_str_128_, v___x_129_);
if (v___x_130_ == 0)
{
return v___y_110_;
}
else
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3));
v___x_132_ = lean_string_dec_eq(v_str_127_, v___x_131_);
if (v___x_132_ == 0)
{
return v___y_110_;
}
else
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4));
v___x_134_ = lean_string_dec_eq(v_str_126_, v___x_133_);
if (v___x_134_ == 0)
{
return v___y_110_;
}
else
{
return v_suppressElabErrors_111_;
}
}
}
}
else
{
return v___y_110_;
}
}
default: 
{
return v___y_110_;
}
}
}
case 0:
{
lean_object* v_str_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_str_135_ = lean_ctor_get(v_x_112_, 1);
v___x_136_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5));
v___x_137_ = lean_string_dec_eq(v_str_135_, v___x_136_);
if (v___x_137_ == 0)
{
return v___y_110_;
}
else
{
return v_suppressElabErrors_111_;
}
}
default: 
{
return v___y_110_;
}
}
}
else
{
return v___y_110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v___y_138_, lean_object* v_suppressElabErrors_139_, lean_object* v_x_140_){
_start:
{
uint8_t v___y_6611__boxed_141_; uint8_t v_suppressElabErrors_boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v___y_6611__boxed_141_ = lean_unbox(v___y_138_);
v_suppressElabErrors_boxed_142_ = lean_unbox(v_suppressElabErrors_139_);
v_res_143_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(v___y_6611__boxed_141_, v_suppressElabErrors_boxed_142_, v_x_140_);
lean_dec(v_x_140_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_146_, lean_object* v_msgData_147_, uint8_t v_severity_148_, uint8_t v_isSilent_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
uint8_t v___y_156_; lean_object* v___y_157_; uint8_t v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_192_; uint8_t v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; uint8_t v___y_196_; uint8_t v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_217_; uint8_t v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; uint8_t v___y_222_; uint8_t v___y_223_; lean_object* v___y_224_; lean_object* v___y_228_; uint8_t v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; uint8_t v___y_233_; uint8_t v___y_234_; uint8_t v___x_239_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; uint8_t v___y_245_; uint8_t v___y_246_; uint8_t v___y_247_; uint8_t v___y_249_; uint8_t v___x_264_; 
v___x_239_ = 2;
v___x_264_ = l_Lean_instBEqMessageSeverity_beq(v_severity_148_, v___x_239_);
if (v___x_264_ == 0)
{
v___y_249_ = v___x_264_;
goto v___jp_248_;
}
else
{
uint8_t v___x_265_; 
lean_inc_ref(v_msgData_147_);
v___x_265_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_147_);
v___y_249_ = v___x_265_;
goto v___jp_248_;
}
v___jp_155_:
{
lean_object* v___x_165_; lean_object* v_currNamespace_166_; lean_object* v_openDecls_167_; lean_object* v_env_168_; lean_object* v_nextMacroScope_169_; lean_object* v_ngen_170_; lean_object* v_auxDeclNGen_171_; lean_object* v_traceState_172_; lean_object* v_cache_173_; lean_object* v_messages_174_; lean_object* v_infoState_175_; lean_object* v_snapshotTasks_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_190_; 
v___x_165_ = lean_st_ref_take(v___y_164_);
v_currNamespace_166_ = lean_ctor_get(v___y_163_, 6);
lean_inc(v_currNamespace_166_);
v_openDecls_167_ = lean_ctor_get(v___y_163_, 7);
lean_inc(v_openDecls_167_);
lean_dec_ref(v___y_163_);
v_env_168_ = lean_ctor_get(v___x_165_, 0);
v_nextMacroScope_169_ = lean_ctor_get(v___x_165_, 1);
v_ngen_170_ = lean_ctor_get(v___x_165_, 2);
v_auxDeclNGen_171_ = lean_ctor_get(v___x_165_, 3);
v_traceState_172_ = lean_ctor_get(v___x_165_, 4);
v_cache_173_ = lean_ctor_get(v___x_165_, 5);
v_messages_174_ = lean_ctor_get(v___x_165_, 6);
v_infoState_175_ = lean_ctor_get(v___x_165_, 7);
v_snapshotTasks_176_ = lean_ctor_get(v___x_165_, 8);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_190_ == 0)
{
v___x_178_ = v___x_165_;
v_isShared_179_ = v_isSharedCheck_190_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snapshotTasks_176_);
lean_inc(v_infoState_175_);
lean_inc(v_messages_174_);
lean_inc(v_cache_173_);
lean_inc(v_traceState_172_);
lean_inc(v_auxDeclNGen_171_);
lean_inc(v_ngen_170_);
lean_inc(v_nextMacroScope_169_);
lean_inc(v_env_168_);
lean_dec(v___x_165_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_190_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_currNamespace_166_);
lean_ctor_set(v___x_180_, 1, v_openDecls_167_);
v___x_181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___y_159_);
v___x_182_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_182_, 0, v___y_157_);
lean_ctor_set(v___x_182_, 1, v___y_161_);
lean_ctor_set(v___x_182_, 2, v___y_160_);
lean_ctor_set(v___x_182_, 3, v___y_162_);
lean_ctor_set(v___x_182_, 4, v___x_181_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*5, v___y_156_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*5 + 1, v___y_158_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*5 + 2, v_isSilent_149_);
v___x_183_ = l_Lean_MessageLog_add(v___x_182_, v_messages_174_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 6, v___x_183_);
v___x_185_ = v___x_178_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_env_168_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_nextMacroScope_169_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v_ngen_170_);
lean_ctor_set(v_reuseFailAlloc_189_, 3, v_auxDeclNGen_171_);
lean_ctor_set(v_reuseFailAlloc_189_, 4, v_traceState_172_);
lean_ctor_set(v_reuseFailAlloc_189_, 5, v_cache_173_);
lean_ctor_set(v_reuseFailAlloc_189_, 6, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_189_, 7, v_infoState_175_);
lean_ctor_set(v_reuseFailAlloc_189_, 8, v_snapshotTasks_176_);
v___x_185_ = v_reuseFailAlloc_189_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_st_ref_set(v___y_164_, v___x_185_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
}
v___jp_191_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_215_; 
v___x_200_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_147_);
v___x_201_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v___x_200_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_215_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_inc_ref(v___y_195_);
v___x_206_ = l_Lean_FileMap_toPosition(v___y_195_, v___y_198_);
lean_dec(v___y_198_);
v___x_207_ = l_Lean_FileMap_toPosition(v___y_195_, v___y_199_);
lean_dec(v___y_199_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
v___x_209_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
if (v___y_197_ == 0)
{
lean_del_object(v___x_204_);
lean_dec_ref(v___y_192_);
v___y_156_ = v___y_193_;
v___y_157_ = v___y_194_;
v___y_158_ = v___y_196_;
v___y_159_ = v_a_202_;
v___y_160_ = v___x_208_;
v___y_161_ = v___x_206_;
v___y_162_ = v___x_209_;
v___y_163_ = v___y_152_;
v___y_164_ = v___y_153_;
goto v___jp_155_;
}
else
{
uint8_t v___x_210_; 
lean_inc(v_a_202_);
v___x_210_ = l_Lean_MessageData_hasTag(v___y_192_, v_a_202_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec_ref(v___x_208_);
lean_dec_ref(v___x_206_);
lean_dec(v_a_202_);
lean_dec_ref(v___y_194_);
lean_dec_ref(v___y_152_);
v___x_211_ = lean_box(0);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_211_);
v___x_213_ = v___x_204_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
else
{
lean_del_object(v___x_204_);
v___y_156_ = v___y_193_;
v___y_157_ = v___y_194_;
v___y_158_ = v___y_196_;
v___y_159_ = v_a_202_;
v___y_160_ = v___x_208_;
v___y_161_ = v___x_206_;
v___y_162_ = v___x_209_;
v___y_163_ = v___y_152_;
v___y_164_ = v___y_153_;
goto v___jp_155_;
}
}
}
}
v___jp_216_:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Syntax_getTailPos_x3f(v___y_221_, v___y_218_);
lean_dec(v___y_221_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_inc(v___y_224_);
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_220_;
v___y_195_ = v___y_219_;
v___y_196_ = v___y_222_;
v___y_197_ = v___y_223_;
v___y_198_ = v___y_224_;
v___y_199_ = v___y_224_;
goto v___jp_191_;
}
else
{
lean_object* v_val_226_; 
v_val_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_226_);
lean_dec_ref(v___x_225_);
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_220_;
v___y_195_ = v___y_219_;
v___y_196_ = v___y_222_;
v___y_197_ = v___y_223_;
v___y_198_ = v___y_224_;
v___y_199_ = v_val_226_;
goto v___jp_191_;
}
}
v___jp_227_:
{
lean_object* v_ref_235_; lean_object* v___x_236_; 
v_ref_235_ = l_Lean_replaceRef(v_ref_146_, v___y_232_);
lean_dec(v___y_232_);
v___x_236_ = l_Lean_Syntax_getPos_x3f(v_ref_235_, v___y_229_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___y_217_ = v___y_228_;
v___y_218_ = v___y_229_;
v___y_219_ = v___y_231_;
v___y_220_ = v___y_230_;
v___y_221_ = v_ref_235_;
v___y_222_ = v___y_234_;
v___y_223_ = v___y_233_;
v___y_224_ = v___x_237_;
goto v___jp_216_;
}
else
{
lean_object* v_val_238_; 
v_val_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref(v___x_236_);
v___y_217_ = v___y_228_;
v___y_218_ = v___y_229_;
v___y_219_ = v___y_231_;
v___y_220_ = v___y_230_;
v___y_221_ = v_ref_235_;
v___y_222_ = v___y_234_;
v___y_223_ = v___y_233_;
v___y_224_ = v_val_238_;
goto v___jp_216_;
}
}
v___jp_240_:
{
if (v___y_247_ == 0)
{
v___y_228_ = v___y_244_;
v___y_229_ = v___y_246_;
v___y_230_ = v___y_242_;
v___y_231_ = v___y_241_;
v___y_232_ = v___y_243_;
v___y_233_ = v___y_245_;
v___y_234_ = v_severity_148_;
goto v___jp_227_;
}
else
{
v___y_228_ = v___y_244_;
v___y_229_ = v___y_246_;
v___y_230_ = v___y_242_;
v___y_231_ = v___y_241_;
v___y_232_ = v___y_243_;
v___y_233_ = v___y_245_;
v___y_234_ = v___x_239_;
goto v___jp_227_;
}
}
v___jp_248_:
{
if (v___y_249_ == 0)
{
lean_object* v_fileName_250_; lean_object* v_fileMap_251_; lean_object* v_options_252_; lean_object* v_ref_253_; uint8_t v_suppressElabErrors_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___f_257_; uint8_t v___x_258_; uint8_t v___x_259_; 
v_fileName_250_ = lean_ctor_get(v___y_152_, 0);
v_fileMap_251_ = lean_ctor_get(v___y_152_, 1);
v_options_252_ = lean_ctor_get(v___y_152_, 2);
v_ref_253_ = lean_ctor_get(v___y_152_, 5);
v_suppressElabErrors_254_ = lean_ctor_get_uint8(v___y_152_, sizeof(void*)*14 + 1);
v___x_255_ = lean_box(v___y_249_);
v___x_256_ = lean_box(v_suppressElabErrors_254_);
v___f_257_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_257_, 0, v___x_255_);
lean_closure_set(v___f_257_, 1, v___x_256_);
v___x_258_ = 1;
v___x_259_ = l_Lean_instBEqMessageSeverity_beq(v_severity_148_, v___x_258_);
if (v___x_259_ == 0)
{
lean_inc(v_ref_253_);
lean_inc_ref(v_fileName_250_);
lean_inc_ref(v_fileMap_251_);
v___y_241_ = v_fileMap_251_;
v___y_242_ = v_fileName_250_;
v___y_243_ = v_ref_253_;
v___y_244_ = v___f_257_;
v___y_245_ = v_suppressElabErrors_254_;
v___y_246_ = v___y_249_;
v___y_247_ = v___x_259_;
goto v___jp_240_;
}
else
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = l_Lean_warningAsError;
v___x_261_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_252_, v___x_260_);
lean_inc(v_ref_253_);
lean_inc_ref(v_fileName_250_);
lean_inc_ref(v_fileMap_251_);
v___y_241_ = v_fileMap_251_;
v___y_242_ = v_fileName_250_;
v___y_243_ = v_ref_253_;
v___y_244_ = v___f_257_;
v___y_245_ = v_suppressElabErrors_254_;
v___y_246_ = v___y_249_;
v___y_247_ = v___x_261_;
goto v___jp_240_;
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec_ref(v___y_152_);
lean_dec_ref(v_msgData_147_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_266_, lean_object* v_msgData_267_, lean_object* v_severity_268_, lean_object* v_isSilent_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v_severity_boxed_275_; uint8_t v_isSilent_boxed_276_; lean_object* v_res_277_; 
v_severity_boxed_275_ = lean_unbox(v_severity_268_);
v_isSilent_boxed_276_ = lean_unbox(v_isSilent_269_);
v_res_277_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_266_, v_msgData_267_, v_severity_boxed_275_, v_isSilent_boxed_276_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_ref_266_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(lean_object* v_ref_278_, lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
uint8_t v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; 
v___x_289_ = 1;
v___x_290_ = 0;
v___x_291_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_278_, v_msgData_279_, v___x_289_, v___x_290_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3___boxed(lean_object* v_ref_292_, lean_object* v_msgData_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_ref_292_, v_msgData_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_ref_292_);
return v_res_303_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2));
v___x_309_ = l_Lean_stringToMessageData(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(lean_object* v_linterOption_310_, lean_object* v_stx_311_, lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_name_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_337_; 
v_name_322_ = lean_ctor_get(v_linterOption_310_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_linterOption_310_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_linterOption_310_, 1);
lean_dec(v_unused_338_);
v___x_324_ = v_linterOption_310_;
v_isShared_325_ = v_isSharedCheck_337_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_name_322_);
lean_dec(v_linterOption_310_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_337_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_326_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1);
lean_inc(v_name_322_);
v___x_327_ = l_Lean_MessageData_ofName(v_name_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 7);
lean_ctor_set(v___x_324_, 1, v___x_327_);
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_329_ = v___x_324_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_336_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_disable_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_330_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v_disable_332_ = l_Lean_MessageData_note(v___x_331_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v_msg_312_);
lean_ctor_set(v___x_333_, 1, v_disable_332_);
v___x_334_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_334_, 0, v_name_322_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_stx_311_, v___x_334_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___boxed(lean_object* v_linterOption_339_, lean_object* v_stx_340_, lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_339_, v_stx_340_, v_msg_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v_stx_340_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_o_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v_env_356_; lean_object* v___x_357_; lean_object* v_toEnvExtension_358_; lean_object* v_asyncMode_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_linterSets_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_355_ = lean_st_ref_get(v___y_353_);
v_env_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref(v_env_356_);
lean_dec(v___x_355_);
v___x_357_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc_ref(v_toEnvExtension_358_);
v_asyncMode_359_ = lean_ctor_get(v_toEnvExtension_358_, 2);
lean_inc(v_asyncMode_359_);
lean_dec_ref(v_toEnvExtension_358_);
v___x_360_ = lean_box(1);
v___x_361_ = lean_box(0);
v_linterSets_362_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_360_, v___x_357_, v_env_356_, v_asyncMode_359_, v___x_361_);
lean_dec(v_asyncMode_359_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_o_352_);
lean_ctor_set(v___x_363_, 1, v_linterSets_362_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_o_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_365_, v___y_366_);
lean_dec(v___y_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_options_378_; lean_object* v___x_379_; 
v_options_378_ = lean_ctor_get(v___y_375_, 2);
lean_inc_ref(v_options_378_);
lean_dec_ref(v___y_375_);
v___x_379_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_options_378_, v___y_376_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(lean_object* v_linterOption_390_, lean_object* v_stx_391_, lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_413_; 
lean_inc_ref(v___y_399_);
v___x_402_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_413_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
uint8_t v___x_407_; 
v___x_407_ = l_Lean_Linter_getLinterValue(v_linterOption_390_, v_a_403_);
lean_dec(v_a_403_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_410_; 
lean_dec_ref(v___y_399_);
lean_dec_ref(v_msg_392_);
lean_dec_ref(v_linterOption_390_);
v___x_408_ = lean_box(0);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_408_);
v___x_410_ = v___x_405_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v___x_412_; 
lean_del_object(v___x_405_);
v___x_412_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_390_, v_stx_391_, v_msg_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(lean_object* v_linterOption_414_, lean_object* v_stx_415_, lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v_linterOption_414_, v_stx_415_, v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v_stx_415_);
return v_res_426_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0));
v___x_429_ = l_Lean_stringToMessageData(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(lean_object* v_upperBound_430_, lean_object* v_fvars_431_, lean_object* v_ids_432_, lean_object* v_a_433_, lean_object* v_b_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_a_445_; uint8_t v___x_449_; 
v___x_449_ = lean_nat_dec_lt(v_a_433_, v_upperBound_430_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_a_433_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_b_434_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_box(0);
v___x_452_ = lean_array_get_size(v_fvars_431_);
v___x_453_ = lean_nat_dec_lt(v_a_433_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = l_Lean_Elab_Tactic_linter_tactic_unusedName;
v___x_455_ = lean_array_fget_borrowed(v_ids_432_, v_a_433_);
v___x_456_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1);
lean_inc_ref(v___y_441_);
v___x_457_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v___x_454_, v___x_455_, v___x_456_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_dec_ref(v___x_457_);
v_a_445_ = v___x_451_;
goto v___jp_444_;
}
else
{
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_a_433_);
return v___x_457_;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = lean_array_fget_borrowed(v_ids_432_, v_a_433_);
v___x_459_ = lean_array_fget_borrowed(v_fvars_431_, v_a_433_);
lean_inc(v___x_459_);
v___x_460_ = l_Lean_mkFVar(v___x_459_);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc(v___x_458_);
v___x_461_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_458_, v___x_460_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_dec_ref(v___x_461_);
v_a_445_ = v___x_451_;
goto v___jp_444_;
}
else
{
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_a_433_);
return v___x_461_;
}
}
}
v___jp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_a_433_, v___x_446_);
lean_dec(v_a_433_);
v_a_433_ = v___x_447_;
v_b_434_ = v_a_445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(lean_object* v_upperBound_462_, lean_object* v_fvars_463_, lean_object* v_ids_464_, lean_object* v_a_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_462_, v_fvars_463_, v_ids_464_, v_a_465_, v_b_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec_ref(v_ids_464_);
lean_dec_ref(v_fvars_463_);
lean_dec(v_upperBound_462_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(lean_object* v___x_477_, lean_object* v_fvars_478_, lean_object* v_ids_479_, lean_object* v___x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v___x_477_, v_fvars_478_, v_ids_479_, v___x_490_, v___x_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v___x_491_, 0);
lean_dec(v_unused_499_);
v___x_493_ = v___x_491_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_dec(v___x_491_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_480_);
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_480_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(lean_object* v___x_500_, lean_object* v_fvars_501_, lean_object* v_ids_502_, lean_object* v___x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(v___x_500_, v_fvars_501_, v_ids_502_, v___x_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_ids_502_);
lean_dec_ref(v_fvars_501_);
lean_dec(v___x_500_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object* v_ids_514_, lean_object* v_fvars_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; 
v___x_525_ = lean_array_get_size(v_ids_514_);
v___x_526_ = lean_box(0);
v___f_527_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed), 13, 4);
lean_closure_set(v___f_527_, 0, v___x_525_);
lean_closure_set(v___f_527_, 1, v_fvars_515_);
lean_closure_set(v___f_527_, 2, v_ids_514_);
lean_closure_set(v___f_527_, 3, v___x_526_);
v___x_528_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_527_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(lean_object* v_ids_529_, lean_object* v_fvars_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_529_, v_fvars_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(lean_object* v_upperBound_541_, lean_object* v_fvars_542_, lean_object* v_ids_543_, lean_object* v_inst_544_, lean_object* v_R_545_, lean_object* v_a_546_, lean_object* v_b_547_, lean_object* v_c_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_541_, v_fvars_542_, v_ids_543_, v_a_546_, v_b_547_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_559_ = _args[0];
lean_object* v_fvars_560_ = _args[1];
lean_object* v_ids_561_ = _args[2];
lean_object* v_inst_562_ = _args[3];
lean_object* v_R_563_ = _args[4];
lean_object* v_a_564_ = _args[5];
lean_object* v_b_565_ = _args[6];
lean_object* v_c_566_ = _args[7];
lean_object* v___y_567_ = _args[8];
lean_object* v___y_568_ = _args[9];
lean_object* v___y_569_ = _args[10];
lean_object* v___y_570_ = _args[11];
lean_object* v___y_571_ = _args[12];
lean_object* v___y_572_ = _args[13];
lean_object* v___y_573_ = _args[14];
lean_object* v___y_574_ = _args[15];
lean_object* v___y_575_ = _args[16];
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(v_upperBound_559_, v_fvars_560_, v_ids_561_, v_inst_562_, v_R_563_, v_a_564_, v_b_565_, v_c_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_ids_561_);
lean_dec_ref(v_fvars_560_);
lean_dec(v_upperBound_559_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(lean_object* v_o_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_577_, v___y_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_o_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(v_o_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(lean_object* v_ref_599_, lean_object* v_msgData_600_, uint8_t v_severity_601_, uint8_t v_isSilent_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_599_, v_msgData_600_, v_severity_601_, v_isSilent_602_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_613_, lean_object* v_msgData_614_, lean_object* v_severity_615_, lean_object* v_isSilent_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
uint8_t v_severity_boxed_626_; uint8_t v_isSilent_boxed_627_; lean_object* v_res_628_; 
v_severity_boxed_626_ = lean_unbox(v_severity_615_);
v_isSilent_boxed_627_ = lean_unbox(v_isSilent_616_);
v_res_628_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(v_ref_613_, v_msgData_614_, v_severity_boxed_626_, v_isSilent_boxed_627_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v_ref_613_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_641_; uint8_t v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
v___x_641_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_));
v___x_642_ = 0;
v___x_643_ = 1;
v___x_644_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_641_, v_e_635_, v___x_642_, v___x_643_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3____boxed(lean_object* v_e_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(v_e_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(lean_object* v_e_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(v_e_652_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3____boxed(lean_object* v_e_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(v_e_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
return v_res_669_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box(1);
v___x_671_ = l_Lean_MessageData_ofFormat(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__2));
v___x_676_ = l_Lean_MessageData_ofFormat(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9(lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
return v_x_677_;
}
else
{
lean_object* v_head_679_; lean_object* v_tail_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_702_; 
v_head_679_ = lean_ctor_get(v_x_678_, 0);
v_tail_680_ = lean_ctor_get(v_x_678_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_678_);
if (v_isSharedCheck_702_ == 0)
{
v___x_682_ = v_x_678_;
v_isShared_683_ = v_isSharedCheck_702_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_tail_680_);
lean_inc(v_head_679_);
lean_dec(v_x_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_702_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_before_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_700_; 
v_before_684_ = lean_ctor_get(v_head_679_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v_head_679_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v_head_679_, 1);
lean_dec(v_unused_701_);
v___x_686_ = v_head_679_;
v_isShared_687_ = v_isSharedCheck_700_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_before_684_);
lean_dec(v_head_679_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_700_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__0);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 7);
lean_ctor_set(v___x_686_, 1, v___x_688_);
lean_ctor_set(v___x_686_, 0, v_x_677_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_x_677_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_699_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__3);
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 7);
lean_ctor_set(v___x_682_, 1, v___x_691_);
lean_ctor_set(v___x_682_, 0, v___x_690_);
v___x_693_ = v___x_682_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_698_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_MessageData_ofSyntax(v_before_684_);
v___x_695_ = l_Lean_indentD(v___x_694_);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_693_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v_x_677_ = v___x_696_;
v_x_678_ = v_tail_680_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__1));
v___x_707_ = l_Lean_MessageData_ofFormat(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(lean_object* v_msgData_708_, lean_object* v_macroStack_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_options_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_options_712_ = lean_ctor_get(v___y_710_, 2);
v___x_713_ = l_Lean_Elab_pp_macroStack;
v___x_714_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_712_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_dec(v_macroStack_709_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_msgData_708_);
return v___x_715_;
}
else
{
if (lean_obj_tag(v_macroStack_709_) == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_msgData_708_);
return v___x_716_;
}
else
{
lean_object* v_head_717_; lean_object* v_after_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_733_; 
v_head_717_ = lean_ctor_get(v_macroStack_709_, 0);
lean_inc(v_head_717_);
v_after_718_ = lean_ctor_get(v_head_717_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_head_717_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_head_717_, 0);
lean_dec(v_unused_734_);
v___x_720_ = v_head_717_;
v_isShared_721_ = v_isSharedCheck_733_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_after_718_);
lean_dec(v_head_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_733_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9___closed__0);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 7);
lean_ctor_set(v___x_720_, 1, v___x_722_);
lean_ctor_set(v___x_720_, 0, v_msgData_708_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_msgData_708_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_722_);
v___x_724_ = v_reuseFailAlloc_732_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_msgData_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_725_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = l_Lean_MessageData_ofSyntax(v_after_718_);
v___x_728_ = l_Lean_indentD(v___x_727_);
v_msgData_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_729_, 0, v___x_726_);
lean_ctor_set(v_msgData_729_, 1, v___x_728_);
v___x_730_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__9(v_msgData_729_, v_macroStack_709_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_735_, lean_object* v_macroStack_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(v_msgData_735_, v_macroStack_736_, v___y_737_);
lean_dec_ref(v___y_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_ref_748_; lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v_macroStack_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_ref_748_ = lean_ctor_get(v___y_745_, 5);
v___x_749_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_740_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref(v___x_749_);
v_macroStack_751_ = lean_ctor_get(v___y_741_, 1);
lean_inc(v_macroStack_751_);
lean_dec_ref(v___y_741_);
lean_inc(v_macroStack_751_);
v___x_752_ = l_Lean_Elab_getBetterRef(v_ref_748_, v_macroStack_751_);
v___x_753_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(v_a_750_, v_macroStack_751_, v___y_745_);
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_752_);
lean_ctor_set(v___x_758_, 1, v_a_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 1);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg___boxed(lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v_msg_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
return v_res_771_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_772_; double v___x_773_; 
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_float_of_nat(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg(lean_object* v_cls_776_, lean_object* v_msg_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_ref_783_; lean_object* v___x_784_; lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_829_; 
v_ref_783_ = lean_ctor_get(v___y_780_, 5);
v___x_784_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_829_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_829_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_829_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v_traceState_790_; lean_object* v_env_791_; lean_object* v_nextMacroScope_792_; lean_object* v_ngen_793_; lean_object* v_auxDeclNGen_794_; lean_object* v_cache_795_; lean_object* v_messages_796_; lean_object* v_infoState_797_; lean_object* v_snapshotTasks_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_828_; 
v___x_789_ = lean_st_ref_take(v___y_781_);
v_traceState_790_ = lean_ctor_get(v___x_789_, 4);
v_env_791_ = lean_ctor_get(v___x_789_, 0);
v_nextMacroScope_792_ = lean_ctor_get(v___x_789_, 1);
v_ngen_793_ = lean_ctor_get(v___x_789_, 2);
v_auxDeclNGen_794_ = lean_ctor_get(v___x_789_, 3);
v_cache_795_ = lean_ctor_get(v___x_789_, 5);
v_messages_796_ = lean_ctor_get(v___x_789_, 6);
v_infoState_797_ = lean_ctor_get(v___x_789_, 7);
v_snapshotTasks_798_ = lean_ctor_get(v___x_789_, 8);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_828_ == 0)
{
v___x_800_ = v___x_789_;
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snapshotTasks_798_);
lean_inc(v_infoState_797_);
lean_inc(v_messages_796_);
lean_inc(v_cache_795_);
lean_inc(v_traceState_790_);
lean_inc(v_auxDeclNGen_794_);
lean_inc(v_ngen_793_);
lean_inc(v_nextMacroScope_792_);
lean_inc(v_env_791_);
lean_dec(v___x_789_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint64_t v_tid_802_; lean_object* v_traces_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_827_; 
v_tid_802_ = lean_ctor_get_uint64(v_traceState_790_, sizeof(void*)*1);
v_traces_803_ = lean_ctor_get(v_traceState_790_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v_traceState_790_);
if (v_isSharedCheck_827_ == 0)
{
v___x_805_ = v_traceState_790_;
v_isShared_806_ = v_isSharedCheck_827_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_traces_803_);
lean_dec(v_traceState_790_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_827_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; double v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_807_ = lean_box(0);
v___x_808_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_809_ = 0;
v___x_810_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
v___x_811_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_811_, 0, v_cls_776_);
lean_ctor_set(v___x_811_, 1, v___x_807_);
lean_ctor_set(v___x_811_, 2, v___x_810_);
lean_ctor_set_float(v___x_811_, sizeof(void*)*3, v___x_808_);
lean_ctor_set_float(v___x_811_, sizeof(void*)*3 + 8, v___x_808_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*3 + 16, v___x_809_);
v___x_812_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_813_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v_a_785_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
lean_inc(v_ref_783_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_ref_783_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_PersistentArray_push___redArg(v_traces_803_, v___x_814_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_815_);
v___x_817_ = v___x_805_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_815_);
lean_ctor_set_uint64(v_reuseFailAlloc_826_, sizeof(void*)*1, v_tid_802_);
v___x_817_ = v_reuseFailAlloc_826_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v___x_817_);
v___x_819_ = v___x_800_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_env_791_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_nextMacroScope_792_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_ngen_793_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_auxDeclNGen_794_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_825_, 5, v_cache_795_);
lean_ctor_set(v_reuseFailAlloc_825_, 6, v_messages_796_);
lean_ctor_set(v_reuseFailAlloc_825_, 7, v_infoState_797_);
lean_ctor_set(v_reuseFailAlloc_825_, 8, v_snapshotTasks_798_);
v___x_819_ = v_reuseFailAlloc_825_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_820_ = lean_st_ref_set(v___y_781_, v___x_819_);
v___x_821_ = lean_box(0);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_821_);
v___x_823_ = v___x_787_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_cls_830_, lean_object* v_msg_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg(v_cls_830_, v_msg_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_options_843_; uint8_t v_hasTrace_844_; 
v_options_843_ = lean_ctor_get(v___y_841_, 2);
v_hasTrace_844_ = lean_ctor_get_uint8(v_options_843_, sizeof(void*)*1);
if (v_hasTrace_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_cls_840_);
v___x_845_ = lean_box(v_hasTrace_844_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
else
{
lean_object* v_inheritedTraceOptions_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_inheritedTraceOptions_847_ = lean_ctor_get(v___y_841_, 13);
v___x_848_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_849_ = l_Lean_Name_append(v___x_848_, v_cls_840_);
v___x_850_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_847_, v_options_843_, v___x_849_);
lean_dec(v___x_849_);
v___x_851_ = lean_box(v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(v_cls_853_, v___y_854_);
lean_dec_ref(v___y_854_);
return v_res_856_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_keys_857_, lean_object* v_i_858_, lean_object* v_k_859_){
_start:
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = lean_array_get_size(v_keys_857_);
v___x_861_ = lean_nat_dec_lt(v_i_858_, v___x_860_);
if (v___x_861_ == 0)
{
lean_dec(v_i_858_);
return v___x_861_;
}
else
{
lean_object* v_k_x27_862_; uint8_t v___x_863_; 
v_k_x27_862_ = lean_array_fget_borrowed(v_keys_857_, v_i_858_);
v___x_863_ = l_Lean_instBEqExtraModUse_beq(v_k_859_, v_k_x27_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_nat_add(v_i_858_, v___x_864_);
lean_dec(v_i_858_);
v_i_858_ = v___x_865_;
goto _start;
}
else
{
lean_dec(v_i_858_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_keys_867_, lean_object* v_i_868_, lean_object* v_k_869_){
_start:
{
uint8_t v_res_870_; lean_object* v_r_871_; 
v_res_870_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_867_, v_i_868_, v_k_869_);
lean_dec_ref(v_k_869_);
lean_dec_ref(v_keys_867_);
v_r_871_ = lean_box(v_res_870_);
return v_r_871_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; 
v___x_872_ = ((size_t)5ULL);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_shift_left(v___x_873_, v___x_872_);
return v___x_874_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; 
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_877_ = lean_usize_sub(v___x_876_, v___x_875_);
return v___x_877_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_878_, size_t v_x_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_object* v_es_881_; lean_object* v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v_j_886_; lean_object* v___x_887_; 
v_es_881_ = lean_ctor_get(v_x_878_, 0);
lean_inc_ref(v_es_881_);
lean_dec_ref(v_x_878_);
v___x_882_ = lean_box(2);
v___x_883_ = ((size_t)5ULL);
v___x_884_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_885_ = lean_usize_land(v_x_879_, v___x_884_);
v_j_886_ = lean_usize_to_nat(v___x_885_);
v___x_887_ = lean_array_get(v___x_882_, v_es_881_, v_j_886_);
lean_dec(v_j_886_);
lean_dec_ref(v_es_881_);
switch(lean_obj_tag(v___x_887_))
{
case 0:
{
lean_object* v_key_888_; uint8_t v___x_889_; 
v_key_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_key_888_);
lean_dec_ref(v___x_887_);
v___x_889_ = l_Lean_instBEqExtraModUse_beq(v_x_880_, v_key_888_);
lean_dec(v_key_888_);
return v___x_889_;
}
case 1:
{
lean_object* v_node_890_; size_t v___x_891_; 
v_node_890_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_node_890_);
lean_dec_ref(v___x_887_);
v___x_891_ = lean_usize_shift_right(v_x_879_, v___x_883_);
v_x_878_ = v_node_890_;
v_x_879_ = v___x_891_;
goto _start;
}
default: 
{
uint8_t v___x_893_; 
v___x_893_ = 0;
return v___x_893_;
}
}
}
else
{
lean_object* v_ks_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_ks_894_ = lean_ctor_get(v_x_878_, 0);
lean_inc_ref(v_ks_894_);
lean_dec_ref(v_x_878_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ks_894_, v___x_895_, v_x_880_);
lean_dec_ref(v_ks_894_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
size_t v_x_11941__boxed_900_; uint8_t v_res_901_; lean_object* v_r_902_; 
v_x_11941__boxed_900_ = lean_unbox_usize(v_x_898_);
lean_dec(v_x_898_);
v_res_901_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_897_, v_x_11941__boxed_900_, v_x_899_);
lean_dec_ref(v_x_899_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
uint64_t v___x_905_; size_t v___x_906_; uint8_t v___x_907_; 
v___x_905_ = l_Lean_instHashableExtraModUse_hash(v_x_904_);
v___x_906_ = lean_uint64_to_usize(v___x_905_);
v___x_907_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_903_, v___x_906_, v_x_904_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
uint8_t v_res_910_; lean_object* v_r_911_; 
v_res_910_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(v_x_908_, v_x_909_);
lean_dec_ref(v_x_909_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__1));
v___x_915_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__0));
v___x_916_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_915_, v___x_914_);
return v___x_916_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_917_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4);
v___x_923_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
lean_ctor_set(v___x_923_, 2, v___x_922_);
lean_ctor_set(v___x_923_, 3, v___x_922_);
lean_ctor_set(v___x_923_, 4, v___x_922_);
lean_ctor_set(v___x_923_, 5, v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__9));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__11));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__14));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__16));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(lean_object* v_mod_945_, uint8_t v_isMeta_946_, lean_object* v_hint_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_env_956_; uint8_t v_isExporting_957_; lean_object* v___x_958_; lean_object* v_env_959_; lean_object* v___x_960_; lean_object* v_entry_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_955_ = lean_st_ref_get(v___y_953_);
v_env_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc_ref(v_env_956_);
lean_dec(v___x_955_);
v_isExporting_957_ = lean_ctor_get_uint8(v_env_956_, sizeof(void*)*8);
lean_dec_ref(v_env_956_);
v___x_958_ = lean_st_ref_get(v___y_953_);
v_env_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc_ref(v_env_959_);
lean_dec(v___x_958_);
v___x_960_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_945_);
v_entry_961_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_961_, 0, v_mod_945_);
lean_ctor_set_uint8(v_entry_961_, sizeof(void*)*1, v_isExporting_957_);
lean_ctor_set_uint8(v_entry_961_, sizeof(void*)*1 + 1, v_isMeta_946_);
v___x_962_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_963_ = lean_box(1);
v___x_964_ = lean_box(0);
v___x_1007_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_960_, v___x_962_, v_env_959_, v___x_963_, v___x_964_);
v___x_1008_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(v___x_1007_, v_entry_961_);
if (v___x_1008_ == 0)
{
lean_object* v_cls_1009_; lean_object* v___x_1010_; lean_object* v_a_1011_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1018_; lean_object* v___y_1019_; uint8_t v___x_1031_; 
v_cls_1009_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__8));
v___x_1010_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(v_cls_1009_, v___y_952_);
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
v___x_1031_ = lean_unbox(v_a_1011_);
lean_dec(v_a_1011_);
if (v___x_1031_ == 0)
{
lean_dec(v_hint_947_);
lean_dec(v_mod_945_);
v___y_966_ = v___y_951_;
v___y_967_ = v___y_953_;
goto v___jp_965_;
}
else
{
lean_object* v___x_1032_; lean_object* v___y_1034_; 
v___x_1032_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15);
if (v_isExporting_957_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__20));
v___y_1034_ = v___x_1041_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__21));
v___y_1034_ = v___x_1042_;
goto v___jp_1033_;
}
v___jp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1035_ = l_Lean_stringToMessageData(v___y_1034_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1032_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
if (v_isMeta_946_ == 0)
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__18));
v___y_1018_ = v___x_1038_;
v___y_1019_ = v___x_1039_;
goto v___jp_1017_;
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19));
v___y_1018_ = v___x_1038_;
v___y_1019_ = v___x_1040_;
goto v___jp_1017_;
}
}
}
v___jp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___y_1013_);
lean_ctor_set(v___x_1015_, 1, v___y_1014_);
v___x_1016_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg(v_cls_1009_, v___x_1015_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_dec_ref(v___x_1016_);
v___y_966_ = v___y_951_;
v___y_967_ = v___y_953_;
goto v___jp_965_;
}
else
{
lean_dec_ref(v_entry_961_);
return v___x_1016_;
}
}
v___jp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1020_ = l_Lean_stringToMessageData(v___y_1019_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___y_1018_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = l_Lean_MessageData_ofName(v_mod_945_);
v___x_1025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l_Lean_Name_isAnonymous(v_hint_947_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12);
v___x_1028_ = l_Lean_MessageData_ofName(v_hint_947_);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___y_1013_ = v___x_1025_;
v___y_1014_ = v___x_1029_;
goto v___jp_1012_;
}
else
{
lean_object* v___x_1030_; 
lean_dec(v_hint_947_);
v___x_1030_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13);
v___y_1013_ = v___x_1025_;
v___y_1014_ = v___x_1030_;
goto v___jp_1012_;
}
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref(v_entry_961_);
lean_dec(v_hint_947_);
lean_dec(v_mod_945_);
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
v___jp_965_:
{
lean_object* v___x_968_; lean_object* v_toEnvExtension_969_; lean_object* v_env_970_; lean_object* v_nextMacroScope_971_; lean_object* v_ngen_972_; lean_object* v_auxDeclNGen_973_; lean_object* v_traceState_974_; lean_object* v_messages_975_; lean_object* v_infoState_976_; lean_object* v_snapshotTasks_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1005_; 
v___x_968_ = lean_st_ref_take(v___y_967_);
v_toEnvExtension_969_ = lean_ctor_get(v___x_962_, 0);
lean_inc_ref(v_toEnvExtension_969_);
v_env_970_ = lean_ctor_get(v___x_968_, 0);
v_nextMacroScope_971_ = lean_ctor_get(v___x_968_, 1);
v_ngen_972_ = lean_ctor_get(v___x_968_, 2);
v_auxDeclNGen_973_ = lean_ctor_get(v___x_968_, 3);
v_traceState_974_ = lean_ctor_get(v___x_968_, 4);
v_messages_975_ = lean_ctor_get(v___x_968_, 6);
v_infoState_976_ = lean_ctor_get(v___x_968_, 7);
v_snapshotTasks_977_ = lean_ctor_get(v___x_968_, 8);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v___x_968_, 5);
lean_dec(v_unused_1006_);
v___x_979_ = v___x_968_;
v_isShared_980_ = v_isSharedCheck_1005_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snapshotTasks_977_);
lean_inc(v_infoState_976_);
lean_inc(v_messages_975_);
lean_inc(v_traceState_974_);
lean_inc(v_auxDeclNGen_973_);
lean_inc(v_ngen_972_);
lean_inc(v_nextMacroScope_971_);
lean_inc(v_env_970_);
lean_dec(v___x_968_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1005_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_asyncMode_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; 
v_asyncMode_981_ = lean_ctor_get(v_toEnvExtension_969_, 2);
lean_inc(v_asyncMode_981_);
lean_dec_ref(v_toEnvExtension_969_);
v___x_982_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_962_, v_env_970_, v_entry_961_, v_asyncMode_981_, v___x_964_);
lean_dec(v_asyncMode_981_);
v___x_983_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 5, v___x_983_);
lean_ctor_set(v___x_979_, 0, v___x_982_);
v___x_985_ = v___x_979_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_nextMacroScope_971_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_ngen_972_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_auxDeclNGen_973_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_traceState_974_);
lean_ctor_set(v_reuseFailAlloc_1004_, 5, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_1004_, 6, v_messages_975_);
lean_ctor_set(v_reuseFailAlloc_1004_, 7, v_infoState_976_);
lean_ctor_set(v_reuseFailAlloc_1004_, 8, v_snapshotTasks_977_);
v___x_985_ = v_reuseFailAlloc_1004_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v_mctx_988_; lean_object* v_zetaDeltaFVarIds_989_; lean_object* v_postponed_990_; lean_object* v_diag_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1002_; 
v___x_986_ = lean_st_ref_set(v___y_967_, v___x_985_);
v___x_987_ = lean_st_ref_take(v___y_966_);
v_mctx_988_ = lean_ctor_get(v___x_987_, 0);
v_zetaDeltaFVarIds_989_ = lean_ctor_get(v___x_987_, 2);
v_postponed_990_ = lean_ctor_get(v___x_987_, 3);
v_diag_991_ = lean_ctor_get(v___x_987_, 4);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v___x_987_, 1);
lean_dec(v_unused_1003_);
v___x_993_ = v___x_987_;
v_isShared_994_ = v_isSharedCheck_1002_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_diag_991_);
lean_inc(v_postponed_990_);
lean_inc(v_zetaDeltaFVarIds_989_);
lean_inc(v_mctx_988_);
lean_dec(v___x_987_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1002_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_mctx_988_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_zetaDeltaFVarIds_989_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_postponed_990_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_diag_991_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_st_ref_set(v___y_966_, v___x_997_);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___boxed(lean_object* v_mod_1045_, lean_object* v_isMeta_1046_, lean_object* v_hint_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v_isMeta_boxed_1055_; lean_object* v_res_1056_; 
v_isMeta_boxed_1055_ = lean_unbox(v_isMeta_1046_);
v_res_1056_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(v_mod_1045_, v_isMeta_boxed_1055_, v_hint_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6___redArg(lean_object* v_a_1057_, lean_object* v_x_1058_){
_start:
{
if (lean_obj_tag(v_x_1058_) == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_box(0);
return v___x_1059_;
}
else
{
lean_object* v_key_1060_; lean_object* v_value_1061_; lean_object* v_tail_1062_; uint8_t v___x_1063_; 
v_key_1060_ = lean_ctor_get(v_x_1058_, 0);
v_value_1061_ = lean_ctor_get(v_x_1058_, 1);
v_tail_1062_ = lean_ctor_get(v_x_1058_, 2);
v___x_1063_ = lean_name_eq(v_key_1060_, v_a_1057_);
if (v___x_1063_ == 0)
{
v_x_1058_ = v_tail_1062_;
goto _start;
}
else
{
lean_object* v___x_1065_; 
lean_inc(v_value_1061_);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_value_1061_);
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6___redArg(v_a_1066_, v_x_1067_);
lean_dec(v_x_1067_);
lean_dec(v_a_1066_);
return v_res_1068_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1069_; uint64_t v___x_1070_; 
v___x_1069_ = lean_unsigned_to_nat(1723u);
v___x_1070_ = lean_uint64_of_nat(v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(lean_object* v_m_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_buckets_1073_; lean_object* v___x_1074_; uint64_t v___y_1076_; 
v_buckets_1073_ = lean_ctor_get(v_m_1071_, 1);
v___x_1074_ = lean_array_get_size(v_buckets_1073_);
if (lean_obj_tag(v_a_1072_) == 0)
{
uint64_t v___x_1090_; 
v___x_1090_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0);
v___y_1076_ = v___x_1090_;
goto v___jp_1075_;
}
else
{
uint64_t v_hash_1091_; 
v_hash_1091_ = lean_ctor_get_uint64(v_a_1072_, sizeof(void*)*2);
v___y_1076_ = v_hash_1091_;
goto v___jp_1075_;
}
v___jp_1075_:
{
uint64_t v___x_1077_; uint64_t v___x_1078_; uint64_t v_fold_1079_; uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1077_ = 32ULL;
v___x_1078_ = lean_uint64_shift_right(v___y_1076_, v___x_1077_);
v_fold_1079_ = lean_uint64_xor(v___y_1076_, v___x_1078_);
v___x_1080_ = 16ULL;
v___x_1081_ = lean_uint64_shift_right(v_fold_1079_, v___x_1080_);
v___x_1082_ = lean_uint64_xor(v_fold_1079_, v___x_1081_);
v___x_1083_ = lean_uint64_to_usize(v___x_1082_);
v___x_1084_ = lean_usize_of_nat(v___x_1074_);
v___x_1085_ = ((size_t)1ULL);
v___x_1086_ = lean_usize_sub(v___x_1084_, v___x_1085_);
v___x_1087_ = lean_usize_land(v___x_1083_, v___x_1086_);
v___x_1088_ = lean_array_uget_borrowed(v_buckets_1073_, v___x_1087_);
v___x_1089_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6___redArg(v_a_1072_, v___x_1088_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(v_m_1092_, v_a_1093_);
lean_dec(v_a_1093_);
lean_dec_ref(v_m_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1(lean_object* v___x_1095_, lean_object* v_declName_1096_, lean_object* v_as_1097_, size_t v_sz_1098_, size_t v_i_1099_, lean_object* v_b_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
uint8_t v___x_1108_; 
v___x_1108_ = lean_usize_dec_lt(v_i_1099_, v_sz_1098_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
lean_dec(v_declName_1096_);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_b_1100_);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; lean_object* v_modules_1111_; lean_object* v___x_1112_; lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v_toImport_1115_; lean_object* v_module_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1110_ = l_Lean_Environment_header(v___x_1095_);
v_modules_1111_ = lean_ctor_get(v___x_1110_, 3);
lean_inc_ref(v_modules_1111_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1113_ = lean_array_uget_borrowed(v_as_1097_, v_i_1099_);
v___x_1114_ = lean_array_get(v___x_1112_, v_modules_1111_, v_a_1113_);
lean_dec_ref(v_modules_1111_);
v_toImport_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_toImport_1115_);
lean_dec(v___x_1114_);
v_module_1116_ = lean_ctor_get(v_toImport_1115_, 0);
lean_inc(v_module_1116_);
lean_dec_ref(v_toImport_1115_);
v___x_1117_ = 0;
lean_inc(v_declName_1096_);
v___x_1118_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(v_module_1116_, v___x_1117_, v_declName_1096_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; 
lean_dec_ref(v___x_1118_);
v___x_1119_ = lean_box(0);
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_add(v_i_1099_, v___x_1120_);
v_i_1099_ = v___x_1121_;
v_b_1100_ = v___x_1119_;
goto _start;
}
else
{
lean_dec(v_declName_1096_);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1___boxed(lean_object* v___x_1123_, lean_object* v_declName_1124_, lean_object* v_as_1125_, lean_object* v_sz_1126_, lean_object* v_i_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
size_t v_sz_boxed_1136_; size_t v_i_boxed_1137_; lean_object* v_res_1138_; 
v_sz_boxed_1136_ = lean_unbox_usize(v_sz_1126_);
lean_dec(v_sz_1126_);
v_i_boxed_1137_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_res_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1(v___x_1123_, v_declName_1124_, v_as_1125_, v_sz_boxed_1136_, v_i_boxed_1137_, v_b_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v_as_1125_);
lean_dec_ref(v___x_1123_);
return v_res_1138_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__1));
v___x_1142_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__0));
v___x_1143_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(lean_object* v_declName_1146_, uint8_t v_isMeta_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; lean_object* v_env_1159_; lean_object* v___y_1161_; lean_object* v___x_1174_; 
v___x_1155_ = lean_st_ref_get(v___y_1153_);
v_env_1159_ = lean_ctor_get(v___x_1155_, 0);
lean_inc_ref(v_env_1159_);
lean_dec(v___x_1155_);
v___x_1174_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1159_, v_declName_1146_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_dec_ref(v_env_1159_);
lean_dec(v_declName_1146_);
goto v___jp_1156_;
}
else
{
lean_object* v_val_1175_; lean_object* v___x_1176_; lean_object* v_modules_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_val_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_val_1175_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = l_Lean_Environment_header(v_env_1159_);
v_modules_1177_ = lean_ctor_get(v___x_1176_, 3);
lean_inc_ref(v_modules_1177_);
lean_dec_ref(v___x_1176_);
v___x_1178_ = lean_array_get_size(v_modules_1177_);
v___x_1179_ = lean_nat_dec_lt(v_val_1175_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_dec_ref(v_modules_1177_);
lean_dec(v_val_1175_);
lean_dec_ref(v_env_1159_);
lean_dec(v_declName_1146_);
goto v___jp_1156_;
}
else
{
lean_object* v___x_1180_; lean_object* v_env_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___y_1185_; 
v___x_1180_ = lean_st_ref_get(v___y_1153_);
v_env_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc_ref(v_env_1181_);
lean_dec(v___x_1180_);
v___x_1182_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2);
v___x_1183_ = lean_array_fget(v_modules_1177_, v_val_1175_);
lean_dec(v_val_1175_);
lean_dec_ref(v_modules_1177_);
if (v_isMeta_1147_ == 0)
{
lean_dec_ref(v_env_1181_);
v___y_1185_ = v_isMeta_1147_;
goto v___jp_1184_;
}
else
{
uint8_t v___x_1196_; 
lean_inc(v_declName_1146_);
v___x_1196_ = l_Lean_isMarkedMeta(v_env_1181_, v_declName_1146_);
if (v___x_1196_ == 0)
{
v___y_1185_ = v_isMeta_1147_;
goto v___jp_1184_;
}
else
{
uint8_t v___x_1197_; 
v___x_1197_ = 0;
v___y_1185_ = v___x_1197_;
goto v___jp_1184_;
}
}
v___jp_1184_:
{
lean_object* v_toImport_1186_; lean_object* v_module_1187_; lean_object* v___x_1188_; 
v_toImport_1186_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref(v_toImport_1186_);
lean_dec(v___x_1183_);
v_module_1187_ = lean_ctor_get(v_toImport_1186_, 0);
lean_inc(v_module_1187_);
lean_dec_ref(v_toImport_1186_);
lean_inc(v_declName_1146_);
v___x_1188_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(v_module_1187_, v___y_1185_, v_declName_1146_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v___x_1188_);
v___x_1189_ = l_Lean_indirectModUseExt;
v___x_1190_ = lean_box(1);
v___x_1191_ = lean_box(0);
lean_inc_ref(v_env_1159_);
v___x_1192_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1182_, v___x_1189_, v_env_1159_, v___x_1190_, v___x_1191_);
v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(v___x_1192_, v_declName_1146_);
lean_dec(v___x_1192_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v___x_1194_; 
v___x_1194_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__3));
v___y_1161_ = v___x_1194_;
goto v___jp_1160_;
}
else
{
lean_object* v_val_1195_; 
v_val_1195_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_val_1195_);
lean_dec_ref(v___x_1193_);
v___y_1161_ = v_val_1195_;
goto v___jp_1160_;
}
}
else
{
lean_dec_ref(v_env_1159_);
lean_dec(v_declName_1146_);
return v___x_1188_;
}
}
}
}
v___jp_1156_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
v___jp_1160_:
{
lean_object* v___x_1162_; size_t v_sz_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = lean_box(0);
v_sz_1163_ = lean_array_size(v___y_1161_);
v___x_1164_ = ((size_t)0ULL);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1(v_env_1159_, v_declName_1146_, v___y_1161_, v_sz_1163_, v___x_1164_, v___x_1162_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v_env_1159_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v___x_1165_, 0);
lean_dec(v_unused_1173_);
v___x_1167_ = v___x_1165_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_dec(v___x_1165_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1162_);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1162_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___boxed(lean_object* v_declName_1198_, lean_object* v_isMeta_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v_isMeta_boxed_1207_; lean_object* v_res_1208_; 
v_isMeta_boxed_1207_ = lean_unbox(v_isMeta_1199_);
v_res_1208_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(v_declName_1198_, v_isMeta_boxed_1207_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1208_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0));
v___x_1211_ = l_Lean_stringToMessageData(v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__2));
v___x_1214_ = l_Lean_stringToMessageData(v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__4));
v___x_1217_ = l_Lean_stringToMessageData(v___x_1216_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__6));
v___x_1220_ = l_Lean_stringToMessageData(v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_));
v___x_1222_ = l_Lean_MessageData_ofName(v___x_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8);
v___x_1224_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7);
v___x_1225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object* v_optConfig_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; uint8_t v___y_1248_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; uint8_t v_recover_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; uint8_t v___x_1276_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; 
v_recover_1270_ = lean_ctor_get_uint8(v_a_1230_, sizeof(void*)*1);
lean_inc(v_optConfig_1229_);
v___x_1271_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_1229_);
v___x_1272_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_1271_);
v___x_1273_ = lean_array_get_size(v___x_1272_);
v___x_1274_ = lean_unsigned_to_nat(0u);
v___x_1275_ = lean_nat_dec_eq(v___x_1273_, v___x_1274_);
v___x_1276_ = 1;
if (v___x_1275_ == 0)
{
lean_object* v___x_1324_; lean_object* v_fileName_1325_; lean_object* v_fileMap_1326_; lean_object* v_options_1327_; lean_object* v_currRecDepth_1328_; lean_object* v_maxRecDepth_1329_; lean_object* v_ref_1330_; lean_object* v_currNamespace_1331_; lean_object* v_openDecls_1332_; lean_object* v_initHeartbeats_1333_; lean_object* v_maxHeartbeats_1334_; lean_object* v_quotContext_1335_; lean_object* v_currMacroScope_1336_; uint8_t v_diag_1337_; lean_object* v_cancelTk_x3f_1338_; uint8_t v_suppressElabErrors_1339_; lean_object* v_inheritedTraceOptions_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1361_; 
v___x_1324_ = lean_st_ref_get(v_a_1236_);
v_fileName_1325_ = lean_ctor_get(v_a_1235_, 0);
v_fileMap_1326_ = lean_ctor_get(v_a_1235_, 1);
v_options_1327_ = lean_ctor_get(v_a_1235_, 2);
v_currRecDepth_1328_ = lean_ctor_get(v_a_1235_, 3);
v_maxRecDepth_1329_ = lean_ctor_get(v_a_1235_, 4);
v_ref_1330_ = lean_ctor_get(v_a_1235_, 5);
v_currNamespace_1331_ = lean_ctor_get(v_a_1235_, 6);
v_openDecls_1332_ = lean_ctor_get(v_a_1235_, 7);
v_initHeartbeats_1333_ = lean_ctor_get(v_a_1235_, 8);
v_maxHeartbeats_1334_ = lean_ctor_get(v_a_1235_, 9);
v_quotContext_1335_ = lean_ctor_get(v_a_1235_, 10);
v_currMacroScope_1336_ = lean_ctor_get(v_a_1235_, 11);
v_diag_1337_ = lean_ctor_get_uint8(v_a_1235_, sizeof(void*)*14);
v_cancelTk_x3f_1338_ = lean_ctor_get(v_a_1235_, 12);
v_suppressElabErrors_1339_ = lean_ctor_get_uint8(v_a_1235_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1340_ = lean_ctor_get(v_a_1235_, 13);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_a_1235_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1342_ = v_a_1235_;
v_isShared_1343_ = v_isSharedCheck_1361_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_inheritedTraceOptions_1340_);
lean_inc(v_cancelTk_x3f_1338_);
lean_inc(v_currMacroScope_1336_);
lean_inc(v_quotContext_1335_);
lean_inc(v_maxHeartbeats_1334_);
lean_inc(v_initHeartbeats_1333_);
lean_inc(v_openDecls_1332_);
lean_inc(v_currNamespace_1331_);
lean_inc(v_ref_1330_);
lean_inc(v_maxRecDepth_1329_);
lean_inc(v_currRecDepth_1328_);
lean_inc(v_options_1327_);
lean_inc(v_fileMap_1326_);
lean_inc(v_fileName_1325_);
lean_dec(v_a_1235_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1361_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_env_1344_; lean_object* v_ref_1345_; lean_object* v___x_1347_; 
v_env_1344_ = lean_ctor_get(v___x_1324_, 0);
lean_inc_ref(v_env_1344_);
lean_dec(v___x_1324_);
v_ref_1345_ = l_Lean_replaceRef(v_optConfig_1229_, v_ref_1330_);
lean_dec(v_ref_1330_);
lean_dec(v_optConfig_1229_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 5, v_ref_1345_);
v___x_1347_ = v___x_1342_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_fileName_1325_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_fileMap_1326_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_options_1327_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_currRecDepth_1328_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_maxRecDepth_1329_);
lean_ctor_set(v_reuseFailAlloc_1360_, 5, v_ref_1345_);
lean_ctor_set(v_reuseFailAlloc_1360_, 6, v_currNamespace_1331_);
lean_ctor_set(v_reuseFailAlloc_1360_, 7, v_openDecls_1332_);
lean_ctor_set(v_reuseFailAlloc_1360_, 8, v_initHeartbeats_1333_);
lean_ctor_set(v_reuseFailAlloc_1360_, 9, v_maxHeartbeats_1334_);
lean_ctor_set(v_reuseFailAlloc_1360_, 10, v_quotContext_1335_);
lean_ctor_set(v_reuseFailAlloc_1360_, 11, v_currMacroScope_1336_);
lean_ctor_set(v_reuseFailAlloc_1360_, 12, v_cancelTk_x3f_1338_);
lean_ctor_set(v_reuseFailAlloc_1360_, 13, v_inheritedTraceOptions_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*14, v_diag_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*14 + 1, v_suppressElabErrors_1339_);
v___x_1347_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_));
v___x_1349_ = l_Lean_Environment_contains(v_env_1344_, v___x_1348_, v___x_1276_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v___x_1272_);
v___x_1350_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9);
v___x_1351_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_1350_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v___x_1347_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v___x_1347_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
v___y_1278_ = v_a_1231_;
v___y_1279_ = v_a_1232_;
v___y_1280_ = v_a_1233_;
v___y_1281_ = v_a_1234_;
v___y_1282_ = v___x_1347_;
v___y_1283_ = v_a_1236_;
goto v___jp_1277_;
}
}
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v___x_1272_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_optConfig_1229_);
v___x_1362_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__10));
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
v___jp_1238_:
{
if (v___y_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref(v___y_1239_);
v___x_1249_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1);
v___x_1250_ = l_Lean_MessageData_ofExpr(v___y_1247_);
v___x_1251_ = l_Lean_indentD(v___x_1250_);
v___x_1252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1249_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_Exception_toMessageData(v___y_1246_);
v___x_1256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_1256_, v___y_1243_, v___y_1242_, v___y_1245_, v___y_1241_, v___y_1244_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1242_);
return v___x_1257_;
}
else
{
lean_dec_ref(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec(v___y_1240_);
return v___y_1239_;
}
}
v___jp_1258_:
{
lean_object* v___x_1266_; 
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
lean_inc_ref(v___y_1259_);
v___x_1266_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(v___y_1259_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v___x_1266_;
}
else
{
lean_object* v_a_1267_; uint8_t v___x_1268_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
v___x_1268_ = l_Lean_Exception_isInterrupt(v_a_1267_);
if (v___x_1268_ == 0)
{
uint8_t v___x_1269_; 
lean_inc(v_a_1267_);
v___x_1269_ = l_Lean_Exception_isRuntime(v_a_1267_);
v___y_1239_ = v___x_1266_;
v___y_1240_ = v___y_1265_;
v___y_1241_ = v___y_1263_;
v___y_1242_ = v___y_1261_;
v___y_1243_ = v___y_1260_;
v___y_1244_ = v___y_1264_;
v___y_1245_ = v___y_1262_;
v___y_1246_ = v_a_1267_;
v___y_1247_ = v___y_1259_;
v___y_1248_ = v___x_1269_;
goto v___jp_1238_;
}
else
{
v___y_1239_ = v___x_1266_;
v___y_1240_ = v___y_1265_;
v___y_1241_ = v___y_1263_;
v___y_1242_ = v___y_1261_;
v___y_1243_ = v___y_1260_;
v___y_1244_ = v___y_1264_;
v___y_1245_ = v___y_1262_;
v___y_1246_ = v_a_1267_;
v___y_1247_ = v___y_1259_;
v___y_1248_ = v___x_1268_;
goto v___jp_1238_;
}
}
}
v___jp_1277_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_));
v___x_1285_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(v___x_1284_, v___x_1276_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1286_; 
lean_dec_ref(v___x_1285_);
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
v___x_1286_ = l_Lean_Elab_Tactic_elabConfig(v_recover_1270_, v___x_1284_, v___x_1272_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1307_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1307_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1307_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Lean_Expr_hasSyntheticSorry(v_a_1287_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; 
lean_del_object(v___x_1289_);
v___x_1292_ = l_Lean_Expr_hasSorry(v_a_1287_);
if (v___x_1292_ == 0)
{
v___y_1259_ = v_a_1287_;
v___y_1260_ = v___y_1278_;
v___y_1261_ = v___y_1279_;
v___y_1262_ = v___y_1280_;
v___y_1263_ = v___y_1281_;
v___y_1264_ = v___y_1282_;
v___y_1265_ = v___y_1283_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_a_1287_);
v___x_1293_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5);
v___x_1294_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_1293_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_dec(v_a_1287_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
v___x_1303_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_1303_, 0, v___x_1275_);
lean_ctor_set_uint8(v___x_1303_, 1, v___x_1276_);
lean_ctor_set_uint8(v___x_1303_, 2, v___x_1275_);
lean_ctor_set_uint8(v___x_1303_, 3, v___x_1276_);
lean_ctor_set_uint8(v___x_1303_, 4, v___x_1276_);
lean_ctor_set_uint8(v___x_1303_, 5, v___x_1275_);
lean_ctor_set_uint8(v___x_1303_, 6, v___x_1276_);
lean_ctor_set_uint8(v___x_1303_, 7, v___x_1276_);
lean_ctor_set_uint8(v___x_1303_, 8, v___x_1275_);
lean_ctor_set_uint8(v___x_1303_, 9, v___x_1275_);
lean_ctor_set_uint8(v___x_1303_, 10, v___x_1275_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1303_);
v___x_1305_ = v___x_1289_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
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
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
v_a_1308_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1286_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1286_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___x_1272_);
v_a_1316_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1285_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1285_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(lean_object* v_optConfig_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_optConfig_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec_ref(v_a_1365_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig(lean_object* v_optConfig_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_optConfig_1374_, v_a_1375_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(lean_object* v_optConfig_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Elab_Tactic_elabExtractLetsConfig(v_optConfig_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1(lean_object* v_00_u03b1_1396_, lean_object* v_msg_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v_msg_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___boxed(lean_object* v_00_u03b1_1406_, lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1(v_00_u03b1_1406_, v_msg_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2(lean_object* v_cls_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(v_cls_1416_, v___y_1421_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2(v_cls_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2(lean_object* v_00_u03b2_1434_, lean_object* v_m_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(v_m_1435_, v_a_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1438_, lean_object* v_m_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2(v_00_u03b2_1438_, v_m_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_m_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4(lean_object* v_msgData_1442_, lean_object* v_macroStack_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(v_msgData_1442_, v_macroStack_1443_, v___y_1448_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___boxed(lean_object* v_msgData_1452_, lean_object* v_macroStack_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4(v_msgData_1452_, v_macroStack_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1461_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
uint8_t v___x_1465_; 
v___x_1465_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(v_x_1463_, v_x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_res_1469_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1(v_00_u03b2_1466_, v_x_1467_, v_x_1468_);
lean_dec_ref(v_x_1468_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3(lean_object* v_cls_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___redArg(v_cls_1471_, v_msg_1472_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_1481_, lean_object* v_msg_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__3(v_cls_1481_, v_msg_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1491_, lean_object* v_a_1492_, lean_object* v_x_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6___redArg(v_a_1492_, v_x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1495_, lean_object* v_a_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__6(v_00_u03b2_1495_, v_a_1496_, v_x_1497_);
lean_dec(v_x_1497_);
lean_dec(v_a_1496_);
return v_res_1498_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1499_, lean_object* v_x_1500_, size_t v_x_1501_, lean_object* v_x_1502_){
_start:
{
uint8_t v___x_1503_; 
v___x_1503_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1500_, v_x_1501_, v_x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_){
_start:
{
size_t v_x_12982__boxed_1508_; uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_x_12982__boxed_1508_ = lean_unbox_usize(v_x_1506_);
lean_dec(v_x_1506_);
v_res_1509_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1504_, v_x_1505_, v_x_12982__boxed_1508_, v_x_1507_);
lean_dec_ref(v_x_1507_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_1511_, lean_object* v_keys_1512_, lean_object* v_vals_1513_, lean_object* v_heq_1514_, lean_object* v_i_1515_, lean_object* v_k_1516_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_1512_, v_i_1515_, v_k_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_1518_, lean_object* v_keys_1519_, lean_object* v_vals_1520_, lean_object* v_heq_1521_, lean_object* v_i_1522_, lean_object* v_k_1523_){
_start:
{
uint8_t v_res_1524_; lean_object* v_r_1525_; 
v_res_1524_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_1518_, v_keys_1519_, v_vals_1520_, v_heq_1521_, v_i_1522_, v_k_1523_);
lean_dec_ref(v_k_1523_);
lean_dec_ref(v_vals_1520_);
lean_dec_ref(v_keys_1519_);
v_r_1525_ = lean_box(v_res_1524_);
return v_r_1525_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v___x_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0);
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object* v_00_u03b1_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object* v_00_u03b1_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(v_00_u03b1_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(lean_object* v_msg_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_ref_1562_; lean_object* v___x_1563_; lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1572_; 
v_ref_1562_ = lean_ctor_get(v___y_1559_, 5);
v___x_1563_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
lean_inc(v_ref_1562_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v_ref_1562_);
lean_ctor_set(v___x_1568_, 1, v_a_1564_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 1);
lean_ctor_set(v___x_1566_, 0, v___x_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object* v_msg_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v_msg_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1579_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0));
v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0(lean_object* v_x_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_obj_once(&l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1);
v___x_1594_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_1593_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(lean_object* v_x_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Elab_Tactic_evalExtractLets___lam__0(v_x_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v_x_1595_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1(lean_object* v_h_1606_, lean_object* v___x_1607_, lean_object* v_a_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1610_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref(v___x_1618_);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
v___x_1620_ = l_Lean_MVarId_extractLetsLocalDecl(v_a_1619_, v_h_1606_, v___x_1607_, v_a_1608_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v_fst_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1649_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1620_);
v_fst_1622_ = lean_ctor_get(v_a_1621_, 0);
lean_inc(v_fst_1622_);
v_snd_1623_ = lean_ctor_get(v_a_1621_, 1);
lean_inc(v_snd_1623_);
lean_dec(v_a_1621_);
v_fst_1624_ = lean_ctor_get(v_fst_1622_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_fst_1622_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; 
v_unused_1650_ = lean_ctor_get(v_fst_1622_, 1);
lean_dec(v_unused_1650_);
v___x_1626_ = v_fst_1622_;
v_isShared_1627_ = v_isSharedCheck_1649_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_fst_1624_);
lean_dec(v_fst_1622_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1649_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = lean_box(0);
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 1);
lean_ctor_set(v___x_1626_, 1, v___x_1628_);
lean_ctor_set(v___x_1626_, 0, v_snd_1623_);
v___x_1630_ = v___x_1626_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_snd_1623_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1630_, v___y_1610_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v___x_1631_, 0);
lean_dec(v_unused_1639_);
v___x_1633_ = v___x_1631_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_dec(v___x_1631_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_fst_1624_);
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_fst_1624_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_fst_1624_);
v_a_1640_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1631_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1631_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
v_a_1651_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1620_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1620_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v_a_1608_);
lean_dec(v___x_1607_);
lean_dec(v_h_1606_);
v_a_1659_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1618_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1618_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(lean_object* v_h_1667_, lean_object* v___x_1668_, lean_object* v_a_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Elab_Tactic_evalExtractLets___lam__1(v_h_1667_, v___x_1668_, v_a_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2(lean_object* v___x_1680_, lean_object* v_a_1681_, lean_object* v_ids_1682_, lean_object* v_h_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___f_1693_; lean_object* v___x_1694_; 
v___f_1693_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed), 12, 3);
lean_closure_set(v___f_1693_, 0, v_h_1683_);
lean_closure_set(v___f_1693_, 1, v___x_1680_);
lean_closure_set(v___f_1693_, 2, v_a_1681_);
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1694_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1693_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_1682_, v_a_1695_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1696_;
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec_ref(v_ids_1682_);
v_a_1697_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1694_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1694_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(lean_object* v___x_1705_, lean_object* v_a_1706_, lean_object* v_ids_1707_, lean_object* v_h_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Elab_Tactic_evalExtractLets___lam__2(v___x_1705_, v_a_1706_, v_ids_1707_, v_h_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3(lean_object* v___x_1719_, lean_object* v_a_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1722_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1732_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1730_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
v___x_1732_ = l_Lean_MVarId_extractLets(v_a_1731_, v___x_1719_, v_a_1720_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v_fst_1734_; lean_object* v_snd_1735_; lean_object* v_fst_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1761_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref(v___x_1732_);
v_fst_1734_ = lean_ctor_get(v_a_1733_, 0);
lean_inc(v_fst_1734_);
v_snd_1735_ = lean_ctor_get(v_a_1733_, 1);
lean_inc(v_snd_1735_);
lean_dec(v_a_1733_);
v_fst_1736_ = lean_ctor_get(v_fst_1734_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_fst_1734_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_fst_1734_, 1);
lean_dec(v_unused_1762_);
v___x_1738_ = v_fst_1734_;
v_isShared_1739_ = v_isSharedCheck_1761_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_fst_1736_);
lean_dec(v_fst_1734_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1761_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = lean_box(0);
if (v_isShared_1739_ == 0)
{
lean_ctor_set_tag(v___x_1738_, 1);
lean_ctor_set(v___x_1738_, 1, v___x_1740_);
lean_ctor_set(v___x_1738_, 0, v_snd_1735_);
v___x_1742_ = v___x_1738_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_snd_1735_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1742_, v___y_1722_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v___x_1743_, 0);
lean_dec(v_unused_1751_);
v___x_1745_ = v___x_1743_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_dec(v___x_1743_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v_fst_1736_);
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_fst_1736_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_fst_1736_);
v_a_1752_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1743_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1743_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
v_a_1763_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1732_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1732_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec_ref(v_a_1720_);
lean_dec(v___x_1719_);
v_a_1771_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1730_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1730_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(lean_object* v___x_1779_, lean_object* v_a_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Elab_Tactic_evalExtractLets___lam__3(v___x_1779_, v_a_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4(lean_object* v___f_1791_, lean_object* v_ids_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; 
lean_inc(v___y_1800_);
lean_inc_ref(v___y_1799_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1797_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
v___x_1802_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1791_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1804_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1802_);
v___x_1804_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_1792_, v_a_1803_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
return v___x_1804_;
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v_ids_1792_);
v_a_1805_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1802_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1802_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(lean_object* v___f_1813_, lean_object* v_ids_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Elab_Tactic_evalExtractLets___lam__4(v___f_1813_, v_ids_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(size_t v_sz_1825_, size_t v_i_1826_, lean_object* v_bs_1827_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_usize_dec_lt(v_i_1826_, v_sz_1825_);
if (v___x_1828_ == 0)
{
return v_bs_1827_;
}
else
{
lean_object* v_v_1829_; lean_object* v___x_1830_; lean_object* v_bs_x27_1831_; lean_object* v___x_1832_; size_t v___x_1833_; size_t v___x_1834_; lean_object* v___x_1835_; 
v_v_1829_ = lean_array_uget(v_bs_1827_, v_i_1826_);
v___x_1830_ = lean_unsigned_to_nat(0u);
v_bs_x27_1831_ = lean_array_uset(v_bs_1827_, v_i_1826_, v___x_1830_);
v___x_1832_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_1829_);
lean_dec(v_v_1829_);
v___x_1833_ = ((size_t)1ULL);
v___x_1834_ = lean_usize_add(v_i_1826_, v___x_1833_);
v___x_1835_ = lean_array_uset(v_bs_x27_1831_, v_i_1826_, v___x_1832_);
v_i_1826_ = v___x_1834_;
v_bs_1827_ = v___x_1835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(lean_object* v_sz_1837_, lean_object* v_i_1838_, lean_object* v_bs_1839_){
_start:
{
size_t v_sz_boxed_1840_; size_t v_i_boxed_1841_; lean_object* v_res_1842_; 
v_sz_boxed_1840_ = lean_unbox_usize(v_sz_1837_);
lean_dec(v_sz_1837_);
v_i_boxed_1841_ = lean_unbox_usize(v_i_1838_);
lean_dec(v_i_1838_);
v_res_1842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_boxed_1840_, v_i_boxed_1841_, v_bs_1839_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets(lean_object* v_x_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
lean_inc(v_x_1863_);
v___x_1890_ = l_Lean_Syntax_isOfKind(v_x_1863_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_x_1863_);
v___x_1891_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1892_ = lean_unsigned_to_nat(1u);
v___x_1893_ = l_Lean_Syntax_getArg(v_x_1863_, v___x_1892_);
v___x_1894_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_1893_);
v___x_1895_ = l_Lean_Syntax_isOfKind(v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; 
lean_dec(v___x_1893_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_x_1863_);
v___x_1896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1896_;
}
else
{
lean_object* v___f_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_loc_x3f_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___f_1897_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__5));
v___x_1898_ = lean_unsigned_to_nat(2u);
v___x_1899_ = l_Lean_Syntax_getArg(v_x_1863_, v___x_1898_);
v___x_1937_ = lean_unsigned_to_nat(3u);
v___x_1938_ = l_Lean_Syntax_getArg(v_x_1863_, v___x_1937_);
lean_dec(v_x_1863_);
v___x_1939_ = l_Lean_Syntax_isNone(v___x_1938_);
if (v___x_1939_ == 0)
{
uint8_t v___x_1940_; 
lean_inc(v___x_1938_);
v___x_1940_ = l_Lean_Syntax_matchesNull(v___x_1938_, v___x_1892_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec(v___x_1938_);
lean_dec(v___x_1899_);
lean_dec(v___x_1893_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
v___x_1941_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1941_;
}
else
{
lean_object* v___x_1942_; lean_object* v_loc_x3f_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1942_ = lean_unsigned_to_nat(0u);
v_loc_x3f_1943_ = l_Lean_Syntax_getArg(v___x_1938_, v___x_1942_);
lean_dec(v___x_1938_);
v___x_1944_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_1943_);
v___x_1945_ = l_Lean_Syntax_isOfKind(v_loc_x3f_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
lean_dec(v_loc_x3f_1943_);
lean_dec(v___x_1899_);
lean_dec(v___x_1893_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
v___x_1946_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1946_;
}
else
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_loc_x3f_1943_);
v_loc_x3f_1901_ = v___x_1947_;
v___y_1902_ = v_a_1864_;
v___y_1903_ = v_a_1865_;
v___y_1904_ = v_a_1866_;
v___y_1905_ = v_a_1867_;
v___y_1906_ = v_a_1868_;
v___y_1907_ = v_a_1869_;
v___y_1908_ = v_a_1870_;
v___y_1909_ = v_a_1871_;
goto v___jp_1900_;
}
}
}
else
{
lean_object* v___x_1948_; 
lean_dec(v___x_1938_);
v___x_1948_ = lean_box(0);
v_loc_x3f_1901_ = v___x_1948_;
v___y_1902_ = v_a_1864_;
v___y_1903_ = v_a_1865_;
v___y_1904_ = v_a_1866_;
v___y_1905_ = v_a_1867_;
v___y_1906_ = v_a_1868_;
v___y_1907_ = v_a_1869_;
v___y_1908_ = v_a_1870_;
v___y_1909_ = v_a_1871_;
goto v___jp_1900_;
}
v___jp_1900_:
{
lean_object* v___x_1910_; 
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
v___x_1910_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v___x_1893_, v___y_1902_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v_ids_1912_; size_t v_sz_1913_; size_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___f_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1910_);
v_ids_1912_ = l_Lean_Syntax_getArgs(v___x_1899_);
lean_dec(v___x_1899_);
v_sz_1913_ = lean_array_size(v_ids_1912_);
v___x_1914_ = ((size_t)0ULL);
lean_inc_ref(v_ids_1912_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_1913_, v___x_1914_, v_ids_1912_);
v___x_1916_ = lean_array_to_list(v___x_1915_);
lean_inc_ref(v_ids_1912_);
lean_inc(v_a_1911_);
lean_inc(v___x_1916_);
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed), 13, 3);
lean_closure_set(v___f_1917_, 0, v___x_1916_);
lean_closure_set(v___f_1917_, 1, v_a_1911_);
lean_closure_set(v___f_1917_, 2, v_ids_1912_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_1918_, 0, v___x_1916_);
lean_closure_set(v___f_1918_, 1, v_a_1911_);
v___f_1919_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed), 11, 2);
lean_closure_set(v___f_1919_, 0, v___f_1918_);
lean_closure_set(v___f_1919_, 1, v_ids_1912_);
if (lean_obj_tag(v_loc_x3f_1901_) == 0)
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_box(0);
v___y_1874_ = v___y_1907_;
v___y_1875_ = v___f_1897_;
v___y_1876_ = v___y_1904_;
v___y_1877_ = v___y_1906_;
v___y_1878_ = v___y_1905_;
v___y_1879_ = v___y_1902_;
v___y_1880_ = v___y_1908_;
v___y_1881_ = v___f_1917_;
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___y_1903_;
v___y_1884_ = v___f_1919_;
v___y_1885_ = v___x_1920_;
goto v___jp_1873_;
}
else
{
lean_object* v_val_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_val_1921_ = lean_ctor_get(v_loc_x3f_1901_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_loc_x3f_1901_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v_loc_x3f_1901_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_val_1921_);
lean_dec(v_loc_x3f_1901_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_val_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
v___y_1874_ = v___y_1907_;
v___y_1875_ = v___f_1897_;
v___y_1876_ = v___y_1904_;
v___y_1877_ = v___y_1906_;
v___y_1878_ = v___y_1905_;
v___y_1879_ = v___y_1902_;
v___y_1880_ = v___y_1908_;
v___y_1881_ = v___f_1917_;
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___y_1903_;
v___y_1884_ = v___f_1919_;
v___y_1885_ = v___x_1926_;
goto v___jp_1873_;
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v_loc_x3f_1901_);
lean_dec(v___x_1899_);
v_a_1929_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1910_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1910_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
}
v___jp_1873_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = l_Lean_mkOptionalNode(v___y_1885_);
v___x_1887_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1886_);
lean_dec(v___x_1886_);
v___x_1888_ = l_Lean_Elab_Tactic_withLocation(v___x_1887_, v___y_1881_, v___y_1884_, v___y_1875_, v___y_1879_, v___y_1883_, v___y_1876_, v___y_1878_, v___y_1877_, v___y_1874_, v___y_1880_, v___y_1882_);
lean_dec(v___x_1887_);
return v___x_1888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___boxed(lean_object* v_x_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Elab_Tactic_evalExtractLets(v_x_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object* v_00_u03b1_1960_, lean_object* v_msg_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v_msg_1961_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object* v_00_u03b1_1972_, lean_object* v_msg_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(v_00_u03b1_1972_, v_msg_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1(){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1991_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1992_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
v___x_1993_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1));
v___x_1994_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___boxed), 10, 0);
v___x_1995_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1991_, v___x_1992_, v___x_1993_, v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(lean_object* v_e_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2009_; uint8_t v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2009_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_));
v___x_2010_ = 0;
v___x_2011_ = 1;
v___x_2012_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_2009_, v_e_2003_, v___x_2010_, v___x_2011_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3____boxed(lean_object* v_e_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(v_e_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(lean_object* v_e_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(v_e_2020_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3____boxed(lean_object* v_e_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(v_e_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
return v_res_2037_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_));
v___x_2039_ = l_Lean_MessageData_ofName(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0);
v___x_2041_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v___x_2040_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object* v_optConfig_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; uint8_t v___y_2065_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; uint8_t v_recover_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; uint8_t v___x_2093_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; 
v_recover_2087_ = lean_ctor_get_uint8(v_a_2047_, sizeof(void*)*1);
lean_inc(v_optConfig_2046_);
v___x_2088_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_2046_);
v___x_2089_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_2088_);
v___x_2090_ = lean_array_get_size(v___x_2089_);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_nat_dec_eq(v___x_2090_, v___x_2091_);
v___x_2093_ = 1;
if (v___x_2092_ == 0)
{
lean_object* v___x_2141_; lean_object* v_fileName_2142_; lean_object* v_fileMap_2143_; lean_object* v_options_2144_; lean_object* v_currRecDepth_2145_; lean_object* v_maxRecDepth_2146_; lean_object* v_ref_2147_; lean_object* v_currNamespace_2148_; lean_object* v_openDecls_2149_; lean_object* v_initHeartbeats_2150_; lean_object* v_maxHeartbeats_2151_; lean_object* v_quotContext_2152_; lean_object* v_currMacroScope_2153_; uint8_t v_diag_2154_; lean_object* v_cancelTk_x3f_2155_; uint8_t v_suppressElabErrors_2156_; lean_object* v_inheritedTraceOptions_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2178_; 
v___x_2141_ = lean_st_ref_get(v_a_2053_);
v_fileName_2142_ = lean_ctor_get(v_a_2052_, 0);
v_fileMap_2143_ = lean_ctor_get(v_a_2052_, 1);
v_options_2144_ = lean_ctor_get(v_a_2052_, 2);
v_currRecDepth_2145_ = lean_ctor_get(v_a_2052_, 3);
v_maxRecDepth_2146_ = lean_ctor_get(v_a_2052_, 4);
v_ref_2147_ = lean_ctor_get(v_a_2052_, 5);
v_currNamespace_2148_ = lean_ctor_get(v_a_2052_, 6);
v_openDecls_2149_ = lean_ctor_get(v_a_2052_, 7);
v_initHeartbeats_2150_ = lean_ctor_get(v_a_2052_, 8);
v_maxHeartbeats_2151_ = lean_ctor_get(v_a_2052_, 9);
v_quotContext_2152_ = lean_ctor_get(v_a_2052_, 10);
v_currMacroScope_2153_ = lean_ctor_get(v_a_2052_, 11);
v_diag_2154_ = lean_ctor_get_uint8(v_a_2052_, sizeof(void*)*14);
v_cancelTk_x3f_2155_ = lean_ctor_get(v_a_2052_, 12);
v_suppressElabErrors_2156_ = lean_ctor_get_uint8(v_a_2052_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2157_ = lean_ctor_get(v_a_2052_, 13);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_a_2052_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2159_ = v_a_2052_;
v_isShared_2160_ = v_isSharedCheck_2178_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_inheritedTraceOptions_2157_);
lean_inc(v_cancelTk_x3f_2155_);
lean_inc(v_currMacroScope_2153_);
lean_inc(v_quotContext_2152_);
lean_inc(v_maxHeartbeats_2151_);
lean_inc(v_initHeartbeats_2150_);
lean_inc(v_openDecls_2149_);
lean_inc(v_currNamespace_2148_);
lean_inc(v_ref_2147_);
lean_inc(v_maxRecDepth_2146_);
lean_inc(v_currRecDepth_2145_);
lean_inc(v_options_2144_);
lean_inc(v_fileMap_2143_);
lean_inc(v_fileName_2142_);
lean_dec(v_a_2052_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2178_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v_env_2161_; lean_object* v_ref_2162_; lean_object* v___x_2164_; 
v_env_2161_ = lean_ctor_get(v___x_2141_, 0);
lean_inc_ref(v_env_2161_);
lean_dec(v___x_2141_);
v_ref_2162_ = l_Lean_replaceRef(v_optConfig_2046_, v_ref_2147_);
lean_dec(v_ref_2147_);
lean_dec(v_optConfig_2046_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 5, v_ref_2162_);
v___x_2164_ = v___x_2159_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_fileName_2142_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_fileMap_2143_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_options_2144_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_currRecDepth_2145_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_maxRecDepth_2146_);
lean_ctor_set(v_reuseFailAlloc_2177_, 5, v_ref_2162_);
lean_ctor_set(v_reuseFailAlloc_2177_, 6, v_currNamespace_2148_);
lean_ctor_set(v_reuseFailAlloc_2177_, 7, v_openDecls_2149_);
lean_ctor_set(v_reuseFailAlloc_2177_, 8, v_initHeartbeats_2150_);
lean_ctor_set(v_reuseFailAlloc_2177_, 9, v_maxHeartbeats_2151_);
lean_ctor_set(v_reuseFailAlloc_2177_, 10, v_quotContext_2152_);
lean_ctor_set(v_reuseFailAlloc_2177_, 11, v_currMacroScope_2153_);
lean_ctor_set(v_reuseFailAlloc_2177_, 12, v_cancelTk_x3f_2155_);
lean_ctor_set(v_reuseFailAlloc_2177_, 13, v_inheritedTraceOptions_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2177_, sizeof(void*)*14, v_diag_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2177_, sizeof(void*)*14 + 1, v_suppressElabErrors_2156_);
v___x_2164_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_));
v___x_2166_ = l_Lean_Environment_contains(v_env_2161_, v___x_2165_, v___x_2093_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec_ref(v___x_2089_);
v___x_2167_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1);
v___x_2168_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_2167_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v___x_2164_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v___x_2164_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
v___y_2095_ = v_a_2048_;
v___y_2096_ = v_a_2049_;
v___y_2097_ = v_a_2050_;
v___y_2098_ = v_a_2051_;
v___y_2099_ = v___x_2164_;
v___y_2100_ = v_a_2053_;
goto v___jp_2094_;
}
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec_ref(v___x_2089_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_optConfig_2046_);
v___x_2179_ = ((lean_object*)(l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__2));
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
return v___x_2180_;
}
v___jp_2055_:
{
if (v___y_2065_ == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_dec_ref(v___y_2062_);
v___x_2066_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1);
v___x_2067_ = l_Lean_MessageData_ofExpr(v___y_2059_);
v___x_2068_ = l_Lean_indentD(v___x_2067_);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2066_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l_Lean_Exception_toMessageData(v___y_2058_);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_2073_, v___y_2057_, v___y_2064_, v___y_2061_, v___y_2063_, v___y_2056_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2064_);
return v___x_2074_;
}
else
{
lean_dec(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v___y_2062_;
}
}
v___jp_2075_:
{
lean_object* v___x_2083_; 
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc_ref(v___y_2076_);
v___x_2083_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(v___y_2076_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v___x_2083_;
}
else
{
lean_object* v_a_2084_; uint8_t v___x_2085_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
v___x_2085_ = l_Lean_Exception_isInterrupt(v_a_2084_);
if (v___x_2085_ == 0)
{
uint8_t v___x_2086_; 
lean_inc(v_a_2084_);
v___x_2086_ = l_Lean_Exception_isRuntime(v_a_2084_);
v___y_2056_ = v___y_2081_;
v___y_2057_ = v___y_2077_;
v___y_2058_ = v_a_2084_;
v___y_2059_ = v___y_2076_;
v___y_2060_ = v___y_2082_;
v___y_2061_ = v___y_2079_;
v___y_2062_ = v___x_2083_;
v___y_2063_ = v___y_2080_;
v___y_2064_ = v___y_2078_;
v___y_2065_ = v___x_2086_;
goto v___jp_2055_;
}
else
{
v___y_2056_ = v___y_2081_;
v___y_2057_ = v___y_2077_;
v___y_2058_ = v_a_2084_;
v___y_2059_ = v___y_2076_;
v___y_2060_ = v___y_2082_;
v___y_2061_ = v___y_2079_;
v___y_2062_ = v___x_2083_;
v___y_2063_ = v___y_2080_;
v___y_2064_ = v___y_2078_;
v___y_2065_ = v___x_2085_;
goto v___jp_2055_;
}
}
}
v___jp_2094_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_));
v___x_2102_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(v___x_2101_, v___x_2093_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v___x_2103_; 
lean_dec_ref(v___x_2102_);
lean_inc(v___y_2100_);
lean_inc_ref(v___y_2099_);
lean_inc(v___y_2098_);
lean_inc_ref(v___y_2097_);
lean_inc(v___y_2096_);
lean_inc_ref(v___y_2095_);
v___x_2103_ = l_Lean_Elab_Tactic_elabConfig(v_recover_2087_, v___x_2101_, v___x_2089_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2124_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2124_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2124_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
uint8_t v___x_2108_; 
v___x_2108_ = l_Lean_Expr_hasSyntheticSorry(v_a_2104_);
if (v___x_2108_ == 0)
{
uint8_t v___x_2109_; 
lean_del_object(v___x_2106_);
v___x_2109_ = l_Lean_Expr_hasSorry(v_a_2104_);
if (v___x_2109_ == 0)
{
v___y_2076_ = v_a_2104_;
v___y_2077_ = v___y_2095_;
v___y_2078_ = v___y_2096_;
v___y_2079_ = v___y_2097_;
v___y_2080_ = v___y_2098_;
v___y_2081_ = v___y_2099_;
v___y_2082_ = v___y_2100_;
goto v___jp_2075_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_a_2104_);
v___x_2110_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5);
v___x_2111_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_2110_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
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
lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_dec(v_a_2104_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
v___x_2120_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_2120_, 0, v___x_2092_);
lean_ctor_set_uint8(v___x_2120_, 1, v___x_2093_);
lean_ctor_set_uint8(v___x_2120_, 2, v___x_2092_);
lean_ctor_set_uint8(v___x_2120_, 3, v___x_2093_);
lean_ctor_set_uint8(v___x_2120_, 4, v___x_2093_);
lean_ctor_set_uint8(v___x_2120_, 5, v___x_2092_);
lean_ctor_set_uint8(v___x_2120_, 6, v___x_2093_);
lean_ctor_set_uint8(v___x_2120_, 7, v___x_2093_);
lean_ctor_set_uint8(v___x_2120_, 8, v___x_2092_);
lean_ctor_set_uint8(v___x_2120_, 9, v___x_2093_);
lean_ctor_set_uint8(v___x_2120_, 10, v___x_2093_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2120_);
v___x_2122_ = v___x_2106_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
v_a_2125_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2103_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2103_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v___x_2089_);
v_a_2133_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2102_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2102_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(lean_object* v_optConfig_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_optConfig_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec_ref(v_a_2182_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig(lean_object* v_optConfig_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_optConfig_2191_, v_a_2192_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(lean_object* v_optConfig_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Elab_Tactic_elabLiftLetsConfig(v_optConfig_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
return v_res_2212_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0));
v___x_2215_ = l_Lean_stringToMessageData(v___x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0(lean_object* v_x_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1);
v___x_2227_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_2226_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(lean_object* v_x_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Elab_Tactic_evalLiftLets___lam__0(v_x_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v_x_2228_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1(lean_object* v_a_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2241_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2251_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref(v___x_2249_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
v___x_2251_ = l_Lean_MVarId_liftLets(v_a_2250_, v_a_2239_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2254_, 0, v_a_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2254_, v___y_2241_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v___x_2255_;
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
v_a_2256_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2251_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2251_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec_ref(v_a_2239_);
v_a_2264_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2249_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2249_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(lean_object* v_a_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Elab_Tactic_evalLiftLets___lam__1(v_a_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2(lean_object* v___f_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(lean_object* v___f_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Elab_Tactic_evalLiftLets___lam__2(v___f_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3(lean_object* v_h_2305_, lean_object* v_a_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2308_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref(v___x_2316_);
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
lean_inc(v___y_2312_);
lean_inc_ref(v___y_2311_);
v___x_2318_ = l_Lean_MVarId_liftLetsLocalDecl(v_a_2317_, v_h_2305_, v_a_2306_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2321_, 0, v_a_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2321_, v___y_2308_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v___x_2322_;
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
v_a_2323_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2318_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2318_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec_ref(v_a_2306_);
lean_dec(v_h_2305_);
v_a_2331_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2316_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2316_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(lean_object* v_h_2339_, lean_object* v_a_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_Elab_Tactic_evalLiftLets___lam__3(v_h_2339_, v_a_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4(lean_object* v_a_2351_, lean_object* v_h_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___f_2362_; lean_object* v___x_2363_; 
v___f_2362_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_2362_, 0, v_h_2352_);
lean_closure_set(v___f_2362_, 1, v_a_2351_);
v___x_2363_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2362_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(lean_object* v_a_2364_, lean_object* v_h_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Elab_Tactic_evalLiftLets___lam__4(v_a_2364_, v_h_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets(lean_object* v_x_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
lean_inc(v_x_2383_);
v___x_2410_ = l_Lean_Syntax_isOfKind(v_x_2383_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; 
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_x_2383_);
v___x_2411_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2411_;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2412_ = lean_unsigned_to_nat(1u);
v___x_2413_ = l_Lean_Syntax_getArg(v_x_2383_, v___x_2412_);
v___x_2414_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_2413_);
v___x_2415_ = l_Lean_Syntax_isOfKind(v___x_2413_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; 
lean_dec(v___x_2413_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_x_2383_);
v___x_2416_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2416_;
}
else
{
lean_object* v___f_2417_; lean_object* v_loc_x3f_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___f_2417_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__2));
v___x_2450_ = lean_unsigned_to_nat(2u);
v___x_2451_ = l_Lean_Syntax_getArg(v_x_2383_, v___x_2450_);
lean_dec(v_x_2383_);
v___x_2452_ = l_Lean_Syntax_isNone(v___x_2451_);
if (v___x_2452_ == 0)
{
uint8_t v___x_2453_; 
lean_inc(v___x_2451_);
v___x_2453_ = l_Lean_Syntax_matchesNull(v___x_2451_, v___x_2412_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec(v___x_2451_);
lean_dec(v___x_2413_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
v___x_2454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2454_;
}
else
{
lean_object* v___x_2455_; lean_object* v_loc_x3f_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2455_ = lean_unsigned_to_nat(0u);
v_loc_x3f_2456_ = l_Lean_Syntax_getArg(v___x_2451_, v___x_2455_);
lean_dec(v___x_2451_);
v___x_2457_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_2456_);
v___x_2458_ = l_Lean_Syntax_isOfKind(v_loc_x3f_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; 
lean_dec(v_loc_x3f_2456_);
lean_dec(v___x_2413_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
v___x_2459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2459_;
}
else
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_loc_x3f_2456_);
v_loc_x3f_2419_ = v___x_2460_;
v___y_2420_ = v_a_2384_;
v___y_2421_ = v_a_2385_;
v___y_2422_ = v_a_2386_;
v___y_2423_ = v_a_2387_;
v___y_2424_ = v_a_2388_;
v___y_2425_ = v_a_2389_;
v___y_2426_ = v_a_2390_;
v___y_2427_ = v_a_2391_;
goto v___jp_2418_;
}
}
}
else
{
lean_object* v___x_2461_; 
lean_dec(v___x_2451_);
v___x_2461_ = lean_box(0);
v_loc_x3f_2419_ = v___x_2461_;
v___y_2420_ = v_a_2384_;
v___y_2421_ = v_a_2385_;
v___y_2422_ = v_a_2386_;
v___y_2423_ = v_a_2387_;
v___y_2424_ = v_a_2388_;
v___y_2425_ = v_a_2389_;
v___y_2426_ = v_a_2390_;
v___y_2427_ = v_a_2391_;
goto v___jp_2418_;
}
v___jp_2418_:
{
lean_object* v___x_2428_; 
lean_inc(v___y_2427_);
lean_inc_ref(v___y_2426_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
v___x_2428_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v___x_2413_, v___y_2420_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___f_2430_; lean_object* v___f_2431_; lean_object* v___f_2432_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref(v___x_2428_);
lean_inc(v_a_2429_);
v___f_2430_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2430_, 0, v_a_2429_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_2431_, 0, v___f_2430_);
v___f_2432_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed), 11, 1);
lean_closure_set(v___f_2432_, 0, v_a_2429_);
if (lean_obj_tag(v_loc_x3f_2419_) == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_box(0);
v___y_2394_ = v___f_2431_;
v___y_2395_ = v___y_2426_;
v___y_2396_ = v___y_2425_;
v___y_2397_ = v___y_2423_;
v___y_2398_ = v___y_2427_;
v___y_2399_ = v___y_2424_;
v___y_2400_ = v___y_2421_;
v___y_2401_ = v___f_2432_;
v___y_2402_ = v___y_2420_;
v___y_2403_ = v___f_2417_;
v___y_2404_ = v___y_2422_;
v___y_2405_ = v___x_2433_;
goto v___jp_2393_;
}
else
{
lean_object* v_val_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
v_val_2434_ = lean_ctor_get(v_loc_x3f_2419_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_loc_x3f_2419_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v_loc_x3f_2419_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_val_2434_);
lean_dec(v_loc_x3f_2419_);
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
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_val_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
v___y_2394_ = v___f_2431_;
v___y_2395_ = v___y_2426_;
v___y_2396_ = v___y_2425_;
v___y_2397_ = v___y_2423_;
v___y_2398_ = v___y_2427_;
v___y_2399_ = v___y_2424_;
v___y_2400_ = v___y_2421_;
v___y_2401_ = v___f_2432_;
v___y_2402_ = v___y_2420_;
v___y_2403_ = v___f_2417_;
v___y_2404_ = v___y_2422_;
v___y_2405_ = v___x_2439_;
goto v___jp_2393_;
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v_loc_x3f_2419_);
v_a_2442_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2428_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2428_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
}
v___jp_2393_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = l_Lean_mkOptionalNode(v___y_2405_);
v___x_2407_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2406_);
lean_dec(v___x_2406_);
v___x_2408_ = l_Lean_Elab_Tactic_withLocation(v___x_2407_, v___y_2401_, v___y_2394_, v___y_2403_, v___y_2402_, v___y_2400_, v___y_2404_, v___y_2397_, v___y_2399_, v___y_2396_, v___y_2395_, v___y_2398_);
lean_dec(v___x_2407_);
return v___x_2408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___boxed(lean_object* v_x_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Elab_Tactic_evalLiftLets(v_x_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1(){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2480_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2481_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
v___x_2482_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1));
v___x_2483_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___boxed), 10, 0);
v___x_2484_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2480_, v___x_2481_, v___x_2482_, v___x_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(lean_object* v_a_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
return v_res_2486_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0));
v___x_2489_ = l_Lean_stringToMessageData(v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0(lean_object* v_x_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1);
v___x_2501_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_2500_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(lean_object* v_x_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Elab_Tactic_evalLetToHave___lam__0(v_x_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v_x_2502_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(uint8_t v___x_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2515_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2525_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v___x_2523_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc_ref(v___y_2518_);
v___x_2525_ = l_Lean_MVarId_letToHave(v_a_2524_, v___x_2513_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref(v___x_2525_);
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_a_2526_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2528_, v___y_2515_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v___x_2529_;
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
v_a_2530_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2525_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2525_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
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
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
v_a_2538_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2523_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2523_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object* v___x_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
uint8_t v___x_1779__boxed_2556_; lean_object* v_res_2557_; 
v___x_1779__boxed_2556_ = lean_unbox(v___x_2546_);
v_res_2557_ = l_Lean_Elab_Tactic_evalLetToHave___lam__1(v___x_1779__boxed_2556_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(lean_object* v_h_2558_, uint8_t v___x_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2561_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref(v___x_2569_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
v___x_2571_ = l_Lean_MVarId_letToHaveLocalDecl(v_a_2570_, v_h_2558_, v___x_2559_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref(v___x_2571_);
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_a_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2574_, v___y_2561_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v___x_2575_;
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
v_a_2576_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2571_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2571_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v_h_2558_);
v_a_2584_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2569_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2569_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object* v_h_2592_, lean_object* v___x_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
uint8_t v___x_1855__boxed_2603_; lean_object* v_res_2604_; 
v___x_1855__boxed_2603_ = lean_unbox(v___x_2593_);
v_res_2604_ = l_Lean_Elab_Tactic_evalLetToHave___lam__3(v_h_2592_, v___x_1855__boxed_2603_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t v___x_2605_, lean_object* v_h_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; lean_object* v___f_2617_; lean_object* v___x_2618_; 
v___x_2616_ = lean_box(v___x_2605_);
v___f_2617_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed), 11, 2);
lean_closure_set(v___f_2617_, 0, v_h_2606_);
lean_closure_set(v___f_2617_, 1, v___x_2616_);
v___x_2618_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2617_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object* v___x_2619_, lean_object* v_h_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
uint8_t v___x_1931__boxed_2630_; lean_object* v_res_2631_; 
v___x_1931__boxed_2630_ = lean_unbox(v___x_2619_);
v_res_2631_ = l_Lean_Elab_Tactic_evalLetToHave___lam__2(v___x_1931__boxed_2630_, v_h_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave(lean_object* v_x_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
lean_inc(v_x_2639_);
v___x_2650_ = l_Lean_Syntax_isOfKind(v_x_2639_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; 
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_x_2639_);
v___x_2651_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2651_;
}
else
{
lean_object* v___f_2652_; lean_object* v___x_2653_; lean_object* v___f_2654_; lean_object* v___f_2655_; lean_object* v___x_2656_; lean_object* v___f_2657_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
v___f_2652_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__2));
v___x_2653_ = lean_box(v___x_2650_);
v___f_2654_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2654_, 0, v___x_2653_);
v___f_2655_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_2655_, 0, v___f_2654_);
v___x_2656_ = lean_box(v___x_2650_);
v___f_2657_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2657_, 0, v___x_2656_);
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = l_Lean_Syntax_getArg(v_x_2639_, v___x_2671_);
lean_dec(v_x_2639_);
v___x_2673_ = l_Lean_Syntax_isNone(v___x_2672_);
if (v___x_2673_ == 0)
{
uint8_t v___x_2674_; 
lean_inc(v___x_2672_);
v___x_2674_ = l_Lean_Syntax_matchesNull(v___x_2672_, v___x_2671_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_dec(v___x_2672_);
lean_dec_ref(v___f_2657_);
lean_dec_ref(v___f_2655_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
v___x_2675_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; lean_object* v_loc_x3f_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v___x_2676_ = lean_unsigned_to_nat(0u);
v_loc_x3f_2677_ = l_Lean_Syntax_getArg(v___x_2672_, v___x_2676_);
lean_dec(v___x_2672_);
v___x_2678_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_2677_);
v___x_2679_ = l_Lean_Syntax_isOfKind(v_loc_x3f_2677_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; 
lean_dec(v_loc_x3f_2677_);
lean_dec_ref(v___f_2657_);
lean_dec_ref(v___f_2655_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
v___x_2680_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2680_;
}
else
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v_loc_x3f_2677_);
v___y_2659_ = v_a_2643_;
v___y_2660_ = v_a_2640_;
v___y_2661_ = v_a_2647_;
v___y_2662_ = v_a_2645_;
v___y_2663_ = v_a_2642_;
v___y_2664_ = v_a_2641_;
v___y_2665_ = v_a_2644_;
v___y_2666_ = v_a_2646_;
v___y_2667_ = v___x_2681_;
goto v___jp_2658_;
}
}
}
else
{
lean_object* v___x_2682_; 
lean_dec(v___x_2672_);
v___x_2682_ = lean_box(0);
v___y_2659_ = v_a_2643_;
v___y_2660_ = v_a_2640_;
v___y_2661_ = v_a_2647_;
v___y_2662_ = v_a_2645_;
v___y_2663_ = v_a_2642_;
v___y_2664_ = v_a_2641_;
v___y_2665_ = v_a_2644_;
v___y_2666_ = v_a_2646_;
v___y_2667_ = v___x_2682_;
goto v___jp_2658_;
}
v___jp_2658_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2668_ = l_Lean_mkOptionalNode(v___y_2667_);
v___x_2669_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2668_);
lean_dec(v___x_2668_);
v___x_2670_ = l_Lean_Elab_Tactic_withLocation(v___x_2669_, v___f_2657_, v___f_2655_, v___f_2652_, v___y_2660_, v___y_2664_, v___y_2663_, v___y_2659_, v___y_2665_, v___y_2662_, v___y_2666_, v___y_2661_);
lean_dec(v___x_2669_);
return v___x_2670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___boxed(lean_object* v_x_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Elab_Tactic_evalLetToHave(v_x_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1(){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2701_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2702_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
v___x_2703_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1));
v___x_2704_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___boxed), 10, 0);
v___x_2705_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2701_, v___x_2702_, v___x_2703_, v___x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
return v_res_2707_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Lets(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_linter_tactic_unusedName = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_linter_tactic_unusedName);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Lets(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Lets(builtin);
}
#ifdef __cplusplus
}
#endif
