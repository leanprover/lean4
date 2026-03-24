// Lean compiler output
// Module: Lean.Meta.Tactic.Util
// Imports: public import Lean.Util.ForEachExprWhere public import Lean.Meta.PPGoal import Lean.Meta.AppBuilder
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MetavarContext_setMVarUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_MVarId_setType___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "terminalTacticsAsSorry"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 90, 215, 151, 242, 202, 226, 151)}};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 139, .m_capacity = 139, .m_length = 138, .m_data = "when enabled, terminal tactics such as `grind` and `omega` are replaced with `sorry`. Useful for debugging and fixing bootstrapping issues"};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 233, 55, 94, 186, 188, 252, 158)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 217, 134, 189, 91, 246, 107, 44)}};
static const lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_debug_terminalTacticsAsSorry;
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkTacticExMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Tactic `"};
static const lean_object* l_Lean_Meta_mkTacticExMsg___closed__0 = (const lean_object*)&l_Lean_Meta_mkTacticExMsg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkTacticExMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkTacticExMsg___closed__1;
static const lean_string_object l_Lean_Meta_mkTacticExMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` failed: "};
static const lean_object* l_Lean_Meta_mkTacticExMsg___closed__2 = (const lean_object*)&l_Lean_Meta_mkTacticExMsg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkTacticExMsg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkTacticExMsg___closed__3;
static const lean_string_object l_Lean_Meta_mkTacticExMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_Meta_mkTacticExMsg___closed__4 = (const lean_object*)&l_Lean_Meta_mkTacticExMsg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkTacticExMsg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkTacticExMsg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwTacticEx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` failed\n\n"};
static const lean_object* l_Lean_Meta_throwTacticEx___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwTacticEx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwTacticEx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwTacticEx___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` failed with a nested error:\n"};
static const lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__1;
static const lean_string_object l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nested"};
static const lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 50, 115, 245, 92, 68, 45, 137)}};
static const lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_checkNotAssigned___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "The metavariable below has already been assigned"};
static const lean_object* l_Lean_MVarId_checkNotAssigned___closed__0 = (const lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__1;
static const lean_string_object l_Lean_MVarId_checkNotAssigned___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "This likely indicates an internal error in this tactic or a prior one"};
static const lean_object* l_Lean_MVarId_checkNotAssigned___closed__2 = (const lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_checkNotAssigned___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__2_value)}};
static const lean_object* l_Lean_MVarId_checkNotAssigned___closed__3 = (const lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__3_value;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__4;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__5;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__6;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__7;
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 80, 134, 96, 135, 241, 87, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 105, 212, 82, 205, 98, 36, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(141, 108, 151, 68, 40, 185, 49, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 35, 20, 40, 241, 13, 114, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 161, 8, 73, 13, 24, 41, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 240, 21, 38, 82, 97, 50, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(240, 251, 182, 143, 63, 208, 115, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 226, 182, 237, 212, 141, 147, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 251, 116, 130, 175, 2, 54, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 96, 175, 63, 15, 15, 160, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1901113268) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(57, 118, 41, 237, 158, 247, 69, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(170, 149, 39, 205, 173, 64, 129, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 101, 131, 162, 224, 178, 204, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(23, 46, 117, 252, 169, 255, 192, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_admit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "admit"};
static const lean_object* l_Lean_MVarId_admit___closed__0 = (const lean_object*)&l_Lean_MVarId_admit___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_admit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_admit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 138, 207, 107, 141, 184, 85, 68)}};
static const lean_object* l_Lean_MVarId_admit___closed__1 = (const lean_object*)&l_Lean_MVarId_admit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0 = (const lean_object*)&l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MVarId_getNondepPropHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_getNondepPropHyps___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_getNondepPropHyps___closed__0 = (const lean_object*)&l_Lean_MVarId_getNondepPropHyps___closed__0_value;
static const lean_closure_object l_Lean_MVarId_getNondepPropHyps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_getNondepPropHyps___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_getNondepPropHyps___closed__1 = (const lean_object*)&l_Lean_MVarId_getNondepPropHyps___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_inferInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "`infer_instance` tactic failed to assign instance"};
static const lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_inferInstance___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_inferInstance___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_inferInstance___lam__0___closed__0_value)}};
static const lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_inferInstance___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_inferInstance___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__2;
static lean_once_cell_t l_Lean_MVarId_inferInstance___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_inferInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "infer_instance"};
static const lean_object* l_Lean_MVarId_inferInstance___closed__0 = (const lean_object*)&l_Lean_MVarId_inferInstance___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_inferInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_inferInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 181, 58, 140, 126, 222, 16, 71)}};
static const lean_object* l_Lean_MVarId_inferInstance___closed__1 = (const lean_object*)&l_Lean_MVarId_inferInstance___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_isSubsingleton___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Subsingleton"};
static const lean_object* l_Lean_MVarId_isSubsingleton___closed__0 = (const lean_object*)&l_Lean_MVarId_isSubsingleton___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_isSubsingleton___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_isSubsingleton___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 130, 42, 228, 248, 162, 23, 186)}};
static const lean_object* l_Lean_MVarId_isSubsingleton___closed__1 = (const lean_object*)&l_Lean_MVarId_isSubsingleton___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "skipAssignedInstances"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 172, 231, 36, 182, 217, 37, 75)}};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 113, .m_capacity = 113, .m_length = 112, .m_data = "in the `rw` and `simp` tactics, if an instance implicit argument is assigned, do not try to synthesize instance."};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 82, 89, 96, 183, 68, 254, 125)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 5, 107, 131, 111, 226, 218, 126)}};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag(lean_object* v_mvarId_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_MVarId_getDecl(v_mvarId_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_78_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_78_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_userName_74_; lean_object* v___x_76_; 
v_userName_74_ = lean_ctor_get(v_a_70_, 0);
lean_inc(v_userName_74_);
lean_dec(v_a_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v_userName_74_);
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_userName_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
else
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_a_79_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_69_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_69_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object* v_mvarId_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_MVarId_getTag(v_mvarId_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg(lean_object* v_mvarId_94_, lean_object* v_tag_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_98_; lean_object* v_mctx_99_; lean_object* v_cache_100_; lean_object* v_zetaDeltaFVarIds_101_; lean_object* v_postponed_102_; lean_object* v_diag_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_114_; 
v___x_98_ = lean_st_ref_take(v_a_96_);
v_mctx_99_ = lean_ctor_get(v___x_98_, 0);
v_cache_100_ = lean_ctor_get(v___x_98_, 1);
v_zetaDeltaFVarIds_101_ = lean_ctor_get(v___x_98_, 2);
v_postponed_102_ = lean_ctor_get(v___x_98_, 3);
v_diag_103_ = lean_ctor_get(v___x_98_, 4);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_114_ == 0)
{
v___x_105_ = v___x_98_;
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_diag_103_);
lean_inc(v_postponed_102_);
lean_inc(v_zetaDeltaFVarIds_101_);
lean_inc(v_cache_100_);
lean_inc(v_mctx_99_);
lean_dec(v___x_98_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = l_Lean_MetavarContext_setMVarUserName(v_mctx_99_, v_mvarId_94_, v_tag_95_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_107_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_cache_100_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_zetaDeltaFVarIds_101_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_postponed_102_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_diag_103_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_st_ref_set(v_a_96_, v___x_109_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg___boxed(lean_object* v_mvarId_115_, lean_object* v_tag_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_MVarId_setTag___redArg(v_mvarId_115_, v_tag_116_, v_a_117_);
lean_dec(v_a_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag(lean_object* v_mvarId_120_, lean_object* v_tag_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_MVarId_setTag___redArg(v_mvarId_120_, v_tag_121_, v_a_123_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object* v_mvarId_128_, lean_object* v_tag_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_MVarId_setTag(v_mvarId_128_, v_tag_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object* v_suffix_136_, lean_object* v_x_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_erase_macro_scopes(v_suffix_136_);
v___x_139_ = l_Lean_Name_append(v_x_137_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object* v_tag_140_, lean_object* v_suffix_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = l_Lean_Name_hasMacroScopes(v_tag_140_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_appendTag___lam__0(v_suffix_141_, v_tag_140_);
return v___x_143_;
}
else
{
lean_object* v_view_144_; lean_object* v_name_145_; lean_object* v_imported_146_; lean_object* v_ctx_147_; lean_object* v_scopes_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_157_; 
v_view_144_ = l_Lean_extractMacroScopes(v_tag_140_);
v_name_145_ = lean_ctor_get(v_view_144_, 0);
v_imported_146_ = lean_ctor_get(v_view_144_, 1);
v_ctx_147_ = lean_ctor_get(v_view_144_, 2);
v_scopes_148_ = lean_ctor_get(v_view_144_, 3);
v_isSharedCheck_157_ = !lean_is_exclusive(v_view_144_);
if (v_isSharedCheck_157_ == 0)
{
v___x_150_ = v_view_144_;
v_isShared_151_ = v_isSharedCheck_157_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_scopes_148_);
lean_inc(v_ctx_147_);
lean_inc(v_imported_146_);
lean_inc(v_name_145_);
lean_dec(v_view_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_157_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = l_Lean_Meta_appendTag___lam__0(v_suffix_141_, v_name_145_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_152_);
v___x_154_ = v___x_150_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_imported_146_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_ctx_147_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_scopes_148_);
v___x_154_ = v_reuseFailAlloc_156_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_MacroScopesView_review(v___x_154_);
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix(lean_object* v_mvarId_158_, lean_object* v_suffix_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_165_; 
lean_inc(v_mvarId_158_);
v___x_165_ = l_Lean_MVarId_getTag(v_mvarId_158_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref(v___x_165_);
v___x_167_ = l_Lean_Meta_appendTag(v_a_166_, v_suffix_159_);
v___x_168_ = l_Lean_MVarId_setTag___redArg(v_mvarId_158_, v___x_167_, v_a_161_);
return v___x_168_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec(v_suffix_159_);
lean_dec(v_mvarId_158_);
v_a_169_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_165_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_165_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object* v_mvarId_177_, lean_object* v_suffix_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Meta_appendTagSuffix(v_mvarId_177_, v_suffix_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object* v_type_185_, lean_object* v_tag_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_type_185_);
v___x_193_ = 2;
v___x_194_ = l_Lean_Meta_mkFreshExprMVar(v___x_192_, v___x_193_, v_tag_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object* v_type_195_, lean_object* v_tag_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_195_, v_tag_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
return v_res_202_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__1(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__0));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__3(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__2));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__5(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__4));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object* v_tacticName_212_, lean_object* v_mvarId_213_, lean_object* v_msg_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_215_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_216_ = l_Lean_MessageData_ofName(v_tacticName_212_);
v___x_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__3, &l_Lean_Meta_mkTacticExMsg___closed__3_once, _init_l_Lean_Meta_mkTacticExMsg___closed__3);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_msg_214_);
v___x_221_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__5, &l_Lean_Meta_mkTacticExMsg___closed__5_once, _init_l_Lean_Meta_mkTacticExMsg___closed__5);
v___x_222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_mvarId_213_);
v___x_224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; lean_object* v_env_232_; lean_object* v___x_233_; lean_object* v_mctx_234_; lean_object* v_lctx_235_; lean_object* v_options_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_231_ = lean_st_ref_get(v___y_229_);
v_env_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_ref(v_env_232_);
lean_dec(v___x_231_);
v___x_233_ = lean_st_ref_get(v___y_227_);
v_mctx_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_mctx_234_);
lean_dec(v___x_233_);
v_lctx_235_ = lean_ctor_get(v___y_226_, 2);
v_options_236_ = lean_ctor_get(v___y_228_, 2);
lean_inc_ref(v_options_236_);
lean_inc_ref(v_lctx_235_);
v___x_237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_237_, 0, v_env_232_);
lean_ctor_set(v___x_237_, 1, v_mctx_234_);
lean_ctor_set(v___x_237_, 2, v_lctx_235_);
lean_ctor_set(v___x_237_, 3, v_options_236_);
v___x_238_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_msgData_225_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object* v_msgData_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_ref_253_; lean_object* v___x_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_ref_253_ = lean_ctor_get(v___y_250_, 5);
v___x_254_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_inc(v_ref_253_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_ref_253_);
lean_ctor_set(v___x_259_, 1, v_a_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_Meta_throwTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_throwTacticEx___redArg___closed__0));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object* v_tacticName_274_, lean_object* v_mvarId_275_, lean_object* v_msg_x3f_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
if (lean_obj_tag(v_msg_x3f_276_) == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_282_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_283_ = l_Lean_MessageData_ofName(v_tacticName_274_);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_obj_once(&l_Lean_Meta_throwTacticEx___redArg___closed__1, &l_Lean_Meta_throwTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwTacticEx___redArg___closed__1);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v_mvarId_275_);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_288_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
return v___x_289_;
}
else
{
lean_object* v_val_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_val_290_ = lean_ctor_get(v_msg_x3f_276_, 0);
lean_inc(v_val_290_);
lean_dec_ref(v_msg_x3f_276_);
v___x_291_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_274_, v_mvarId_275_, v_val_290_);
v___x_292_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_291_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object* v_tacticName_293_, lean_object* v_mvarId_294_, lean_object* v_msg_x3f_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_293_, v_mvarId_294_, v_msg_x3f_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object* v_00_u03b1_302_, lean_object* v_tacticName_303_, lean_object* v_mvarId_304_, lean_object* v_msg_x3f_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_303_, v_mvarId_304_, v_msg_x3f_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object* v_00_u03b1_312_, lean_object* v_tacticName_313_, lean_object* v_mvarId_314_, lean_object* v_msg_x3f_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Meta_throwTacticEx(v_00_u03b1_312_, v_tacticName_313_, v_mvarId_314_, v_msg_x3f_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object* v_00_u03b1_322_, lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object* v_00_u03b1_330_, lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(v_00_u03b1_330_, v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_337_;
}
}
static lean_object* _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0));
v___x_340_ = l_Lean_stringToMessageData(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object* v_tacticName_344_, lean_object* v_ex_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_nestedMsg_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_msg_357_; lean_object* v_kind_358_; uint8_t v___x_359_; 
v_nestedMsg_351_ = l_Lean_Exception_toMessageData(v_ex_345_);
v___x_352_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_353_ = l_Lean_MessageData_ofName(v_tacticName_344_);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_obj_once(&l_Lean_Meta_throwNestedTacticEx___redArg___closed__1, &l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_inc_ref(v_nestedMsg_351_);
v_msg_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_357_, 0, v___x_356_);
lean_ctor_set(v_msg_357_, 1, v_nestedMsg_351_);
v_kind_358_ = l_Lean_MessageData_kind(v_nestedMsg_351_);
lean_dec_ref(v_nestedMsg_351_);
v___x_359_ = l_Lean_Name_isAnonymous(v_kind_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_361_ = l_Lean_Name_append(v___x_360_, v_kind_358_);
v___x_362_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v_msg_357_);
v___x_363_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_362_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_dec(v_kind_358_);
v___x_364_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_357_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_365_, lean_object* v_ex_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_365_, v_ex_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_373_, lean_object* v_tacticName_374_, lean_object* v_ex_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_374_, v_ex_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_382_, lean_object* v_tacticName_383_, lean_object* v_ex_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_382_, v_tacticName_383_, v_ex_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_391_, lean_object* v_i_392_, lean_object* v_k_393_){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_array_get_size(v_keys_391_);
v___x_395_ = lean_nat_dec_lt(v_i_392_, v___x_394_);
if (v___x_395_ == 0)
{
lean_dec(v_i_392_);
return v___x_395_;
}
else
{
lean_object* v_k_x27_396_; uint8_t v___x_397_; 
v_k_x27_396_ = lean_array_fget_borrowed(v_keys_391_, v_i_392_);
v___x_397_ = l_Lean_instBEqMVarId_beq(v_k_393_, v_k_x27_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v_i_392_, v___x_398_);
lean_dec(v_i_392_);
v_i_392_ = v___x_399_;
goto _start;
}
else
{
lean_dec(v_i_392_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_401_, lean_object* v_i_402_, lean_object* v_k_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_401_, v_i_402_, v_k_403_);
lean_dec(v_k_403_);
lean_dec_ref(v_keys_401_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; 
v___x_406_ = ((size_t)5ULL);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_shift_left(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; 
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_411_ = lean_usize_sub(v___x_410_, v___x_409_);
return v___x_411_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_412_, size_t v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_412_) == 0)
{
lean_object* v_es_415_; lean_object* v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; lean_object* v_j_420_; lean_object* v___x_421_; 
v_es_415_ = lean_ctor_get(v_x_412_, 0);
lean_inc_ref(v_es_415_);
lean_dec_ref(v_x_412_);
v___x_416_ = lean_box(2);
v___x_417_ = ((size_t)5ULL);
v___x_418_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_419_ = lean_usize_land(v_x_413_, v___x_418_);
v_j_420_ = lean_usize_to_nat(v___x_419_);
v___x_421_ = lean_array_get(v___x_416_, v_es_415_, v_j_420_);
lean_dec(v_j_420_);
lean_dec_ref(v_es_415_);
switch(lean_obj_tag(v___x_421_))
{
case 0:
{
lean_object* v_key_422_; uint8_t v___x_423_; 
v_key_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_key_422_);
lean_dec_ref(v___x_421_);
v___x_423_ = l_Lean_instBEqMVarId_beq(v_x_414_, v_key_422_);
lean_dec(v_key_422_);
return v___x_423_;
}
case 1:
{
lean_object* v_node_424_; size_t v___x_425_; 
v_node_424_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_node_424_);
lean_dec_ref(v___x_421_);
v___x_425_ = lean_usize_shift_right(v_x_413_, v___x_417_);
v_x_412_ = v_node_424_;
v_x_413_ = v___x_425_;
goto _start;
}
default: 
{
uint8_t v___x_427_; 
v___x_427_ = 0;
return v___x_427_;
}
}
}
else
{
lean_object* v_ks_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_ks_428_ = lean_ctor_get(v_x_412_, 0);
lean_inc_ref(v_ks_428_);
lean_dec_ref(v_x_412_);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_428_, v___x_429_, v_x_414_);
lean_dec_ref(v_ks_428_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
size_t v_x_630__boxed_434_; uint8_t v_res_435_; lean_object* v_r_436_; 
v_x_630__boxed_434_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_435_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_431_, v_x_630__boxed_434_, v_x_433_);
lean_dec(v_x_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
uint64_t v___x_439_; size_t v___x_440_; uint8_t v___x_441_; 
v___x_439_ = l_Lean_instHashableMVarId_hash(v_x_438_);
v___x_440_ = lean_uint64_to_usize(v___x_439_);
v___x_441_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_437_, v___x_440_, v_x_438_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_442_, v_x_443_);
lean_dec(v_x_443_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object* v_mvarId_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; lean_object* v_mctx_450_; lean_object* v_eAssignment_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_449_ = lean_st_ref_get(v___y_447_);
v_mctx_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc_ref(v_mctx_450_);
lean_dec(v___x_449_);
v_eAssignment_451_ = lean_ctor_get(v_mctx_450_, 7);
lean_inc_ref(v_eAssignment_451_);
lean_dec_ref(v_mctx_450_);
v___x_452_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_451_, v_mvarId_446_);
v___x_453_ = lean_box(v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object* v_mvarId_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec(v_mvarId_455_);
return v_res_458_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__1(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__0));
v___x_461_ = l_Lean_stringToMessageData(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__4(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__3));
v___x_466_ = l_Lean_MessageData_ofFormat(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__5(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__4, &l_Lean_MVarId_checkNotAssigned___closed__4_once, _init_l_Lean_MVarId_checkNotAssigned___closed__4);
v___x_468_ = l_Lean_MessageData_note(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__6(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__5, &l_Lean_MVarId_checkNotAssigned___closed__5_once, _init_l_Lean_MVarId_checkNotAssigned___closed__5);
v___x_470_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__1, &l_Lean_MVarId_checkNotAssigned___closed__1_once, _init_l_Lean_MVarId_checkNotAssigned___closed__1);
v___x_471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__7(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__6, &l_Lean_MVarId_checkNotAssigned___closed__6_once, _init_l_Lean_MVarId_checkNotAssigned___closed__6);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object* v_mvarId_474_, lean_object* v_tacticName_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_493_; 
v___x_481_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_474_, v_a_477_);
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_493_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_493_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_493_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v___x_486_; 
v___x_486_ = lean_unbox(v_a_482_);
lean_dec(v_a_482_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_489_; 
lean_dec(v_tacticName_475_);
lean_dec(v_mvarId_474_);
v___x_487_ = lean_box(0);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_del_object(v___x_484_);
v___x_491_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__7, &l_Lean_MVarId_checkNotAssigned___closed__7_once, _init_l_Lean_MVarId_checkNotAssigned___closed__7);
v___x_492_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_475_, v_mvarId_474_, v___x_491_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object* v_mvarId_494_, lean_object* v_tacticName_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_494_, v_tacticName_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object* v_mvarId_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_502_, v___y_504_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object* v_mvarId_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v_mvarId_509_);
return v_res_515_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object* v_00_u03b2_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_517_, v_x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_520_, lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_520_, v_x_521_, v_x_522_);
lean_dec(v_x_522_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_525_, lean_object* v_x_526_, size_t v_x_527_, lean_object* v_x_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_526_, v_x_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
size_t v_x_815__boxed_534_; uint8_t v_res_535_; lean_object* v_r_536_; 
v_x_815__boxed_534_ = lean_unbox_usize(v_x_532_);
lean_dec(v_x_532_);
v_res_535_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_530_, v_x_531_, v_x_815__boxed_534_, v_x_533_);
lean_dec(v_x_533_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_537_, lean_object* v_keys_538_, lean_object* v_vals_539_, lean_object* v_heq_540_, lean_object* v_i_541_, lean_object* v_k_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_538_, v_i_541_, v_k_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_544_, lean_object* v_keys_545_, lean_object* v_vals_546_, lean_object* v_heq_547_, lean_object* v_i_548_, lean_object* v_k_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_544_, v_keys_545_, v_vals_546_, v_heq_547_, v_i_548_, v_k_549_);
lean_dec(v_k_549_);
lean_dec_ref(v_vals_546_);
lean_dec_ref(v_keys_545_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object* v_mvarId_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_MVarId_getDecl(v_mvarId_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_type_563_; lean_object* v___x_565_; 
v_type_563_ = lean_ctor_get(v_a_559_, 2);
lean_inc_ref(v_type_563_);
lean_dec(v_a_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_type_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_type_563_);
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
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_568_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_558_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_558_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object* v_mvarId_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_MVarId_getType(v_mvarId_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object* v_e_583_, lean_object* v___y_584_){
_start:
{
uint8_t v___x_586_; 
v___x_586_ = l_Lean_Expr_hasMVar(v_e_583_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_e_583_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; lean_object* v_mctx_589_; lean_object* v___x_590_; lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_593_; lean_object* v_cache_594_; lean_object* v_zetaDeltaFVarIds_595_; lean_object* v_postponed_596_; lean_object* v_diag_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_606_; 
v___x_588_ = lean_st_ref_get(v___y_584_);
v_mctx_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc_ref(v_mctx_589_);
lean_dec(v___x_588_);
v___x_590_ = l_Lean_instantiateMVarsCore(v_mctx_589_, v_e_583_);
v_fst_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_fst_591_);
v_snd_592_ = lean_ctor_get(v___x_590_, 1);
lean_inc(v_snd_592_);
lean_dec_ref(v___x_590_);
v___x_593_ = lean_st_ref_take(v___y_584_);
v_cache_594_ = lean_ctor_get(v___x_593_, 1);
v_zetaDeltaFVarIds_595_ = lean_ctor_get(v___x_593_, 2);
v_postponed_596_ = lean_ctor_get(v___x_593_, 3);
v_diag_597_ = lean_ctor_get(v___x_593_, 4);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_593_, 0);
lean_dec(v_unused_607_);
v___x_599_ = v___x_593_;
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_diag_597_);
lean_inc(v_postponed_596_);
lean_inc(v_zetaDeltaFVarIds_595_);
lean_inc(v_cache_594_);
lean_dec(v___x_593_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v_snd_592_);
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_snd_592_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_cache_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_zetaDeltaFVarIds_595_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_postponed_596_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_diag_597_);
v___x_602_ = v_reuseFailAlloc_605_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_st_ref_set(v___y_584_, v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v_fst_591_);
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object* v_e_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_608_, v___y_609_);
lean_dec(v___y_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object* v_e_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_612_, v___y_614_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object* v_e_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object* v_mvarId_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_MVarId_getType(v_mvarId_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
lean_inc(v_a_628_);
v___x_634_ = lean_whnf(v_a_633_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref(v___x_634_);
v___x_636_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_635_, v_a_628_);
lean_dec(v_a_628_);
return v___x_636_;
}
else
{
lean_dec(v_a_628_);
return v___x_634_;
}
}
else
{
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object* v_mvarId_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_MVarId_getType_x27(v_mvarId_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_710_ = 0;
v___x_711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_712_ = l_Lean_registerTraceClass(v___x_709_, v___x_710_, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object* v_mvarId_715_, lean_object* v_x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_715_, v_x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_731_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_722_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_722_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object* v_mvarId_739_, lean_object* v_x_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_739_, v_x_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object* v_00_u03b1_747_, lean_object* v_mvarId_748_, lean_object* v_x_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_748_, v_x_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object* v_00_u03b1_756_, lean_object* v_mvarId_757_, lean_object* v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(v_00_u03b1_756_, v_mvarId_757_, v_x_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_ks_769_; lean_object* v_vs_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_794_; 
v_ks_769_ = lean_ctor_get(v_x_765_, 0);
v_vs_770_ = lean_ctor_get(v_x_765_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_794_ == 0)
{
v___x_772_ = v_x_765_;
v_isShared_773_ = v_isSharedCheck_794_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_vs_770_);
lean_inc(v_ks_769_);
lean_dec(v_x_765_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_794_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_array_get_size(v_ks_769_);
v___x_775_ = lean_nat_dec_lt(v_x_766_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec(v_x_766_);
v___x_776_ = lean_array_push(v_ks_769_, v_x_767_);
v___x_777_ = lean_array_push(v_vs_770_, v_x_768_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_777_);
lean_ctor_set(v___x_772_, 0, v___x_776_);
v___x_779_ = v___x_772_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v_k_x27_781_; uint8_t v___x_782_; 
v_k_x27_781_ = lean_array_fget_borrowed(v_ks_769_, v_x_766_);
v___x_782_ = l_Lean_instBEqMVarId_beq(v_x_767_, v_k_x27_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_784_; 
if (v_isShared_773_ == 0)
{
v___x_784_ = v___x_772_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_ks_769_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_vs_770_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_add(v_x_766_, v___x_785_);
lean_dec(v_x_766_);
v_x_765_ = v___x_784_;
v_x_766_ = v___x_786_;
goto _start;
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = lean_array_fset(v_ks_769_, v_x_766_, v_x_767_);
v___x_790_ = lean_array_fset(v_vs_770_, v_x_766_, v_x_768_);
lean_dec(v_x_766_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_790_);
lean_ctor_set(v___x_772_, 0, v___x_789_);
v___x_792_ = v___x_772_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_795_, lean_object* v_k_796_, lean_object* v_v_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_795_, v___x_798_, v_k_796_, v_v_797_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object* v_x_801_, size_t v_x_802_, size_t v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
if (lean_obj_tag(v_x_801_) == 0)
{
lean_object* v_es_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v_j_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v_es_806_ = lean_ctor_get(v_x_801_, 0);
v___x_807_ = ((size_t)5ULL);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_810_ = lean_usize_land(v_x_802_, v___x_809_);
v_j_811_ = lean_usize_to_nat(v___x_810_);
v___x_812_ = lean_array_get_size(v_es_806_);
v___x_813_ = lean_nat_dec_lt(v_j_811_, v___x_812_);
if (v___x_813_ == 0)
{
lean_dec(v_j_811_);
lean_dec(v_x_805_);
lean_dec(v_x_804_);
return v_x_801_;
}
else
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_850_; 
lean_inc_ref(v_es_806_);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_801_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v_x_801_, 0);
lean_dec(v_unused_851_);
v___x_815_ = v_x_801_;
v_isShared_816_ = v_isSharedCheck_850_;
goto v_resetjp_814_;
}
else
{
lean_dec(v_x_801_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_850_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_v_817_; lean_object* v___x_818_; lean_object* v_xs_x27_819_; lean_object* v___y_821_; 
v_v_817_ = lean_array_fget(v_es_806_, v_j_811_);
v___x_818_ = lean_box(0);
v_xs_x27_819_ = lean_array_fset(v_es_806_, v_j_811_, v___x_818_);
switch(lean_obj_tag(v_v_817_))
{
case 0:
{
lean_object* v_key_826_; lean_object* v_val_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_837_; 
v_key_826_ = lean_ctor_get(v_v_817_, 0);
v_val_827_ = lean_ctor_get(v_v_817_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_v_817_);
if (v_isSharedCheck_837_ == 0)
{
v___x_829_ = v_v_817_;
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_val_827_);
lean_inc(v_key_826_);
lean_dec(v_v_817_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_instBEqMVarId_beq(v_x_804_, v_key_826_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_del_object(v___x_829_);
v___x_832_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_826_, v_val_827_, v_x_804_, v_x_805_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___y_821_ = v___x_833_;
goto v___jp_820_;
}
else
{
lean_object* v___x_835_; 
lean_dec(v_val_827_);
lean_dec(v_key_826_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v_x_805_);
lean_ctor_set(v___x_829_, 0, v_x_804_);
v___x_835_ = v___x_829_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_x_804_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_x_805_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
v___y_821_ = v___x_835_;
goto v___jp_820_;
}
}
}
}
case 1:
{
lean_object* v_node_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_848_; 
v_node_838_ = lean_ctor_get(v_v_817_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_v_817_);
if (v_isSharedCheck_848_ == 0)
{
v___x_840_ = v_v_817_;
v_isShared_841_ = v_isSharedCheck_848_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_node_838_);
lean_dec(v_v_817_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_848_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_842_ = lean_usize_shift_right(v_x_802_, v___x_807_);
v___x_843_ = lean_usize_add(v_x_803_, v___x_808_);
v___x_844_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_838_, v___x_842_, v___x_843_, v_x_804_, v_x_805_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_844_);
v___x_846_ = v___x_840_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v___y_821_ = v___x_846_;
goto v___jp_820_;
}
}
}
default: 
{
lean_object* v___x_849_; 
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_x_804_);
lean_ctor_set(v___x_849_, 1, v_x_805_);
v___y_821_ = v___x_849_;
goto v___jp_820_;
}
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_array_fset(v_xs_x27_819_, v_j_811_, v___y_821_);
lean_dec(v_j_811_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_822_);
v___x_824_ = v___x_815_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
else
{
lean_object* v_ks_852_; lean_object* v_vs_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_873_; 
v_ks_852_ = lean_ctor_get(v_x_801_, 0);
v_vs_853_ = lean_ctor_get(v_x_801_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_801_);
if (v_isSharedCheck_873_ == 0)
{
v___x_855_ = v_x_801_;
v_isShared_856_ = v_isSharedCheck_873_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_vs_853_);
lean_inc(v_ks_852_);
lean_dec(v_x_801_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_873_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_ks_852_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_vs_853_);
v___x_858_ = v_reuseFailAlloc_872_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v_newNode_859_; uint8_t v___y_861_; size_t v___x_867_; uint8_t v___x_868_; 
v_newNode_859_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_858_, v_x_804_, v_x_805_);
v___x_867_ = ((size_t)7ULL);
v___x_868_ = lean_usize_dec_le(v___x_867_, v_x_803_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_869_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_859_);
v___x_870_ = lean_unsigned_to_nat(4u);
v___x_871_ = lean_nat_dec_lt(v___x_869_, v___x_870_);
lean_dec(v___x_869_);
v___y_861_ = v___x_871_;
goto v___jp_860_;
}
else
{
v___y_861_ = v___x_868_;
goto v___jp_860_;
}
v___jp_860_:
{
if (v___y_861_ == 0)
{
lean_object* v_ks_862_; lean_object* v_vs_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_ks_862_ = lean_ctor_get(v_newNode_859_, 0);
lean_inc_ref(v_ks_862_);
v_vs_863_ = lean_ctor_get(v_newNode_859_, 1);
lean_inc_ref(v_vs_863_);
lean_dec_ref(v_newNode_859_);
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_866_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_803_, v_ks_862_, v_vs_863_, v___x_864_, v___x_865_);
lean_dec_ref(v_vs_863_);
lean_dec_ref(v_ks_862_);
return v___x_866_;
}
else
{
return v_newNode_859_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_874_, lean_object* v_keys_875_, lean_object* v_vals_876_, lean_object* v_i_877_, lean_object* v_entries_878_){
_start:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_array_get_size(v_keys_875_);
v___x_880_ = lean_nat_dec_lt(v_i_877_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec(v_i_877_);
return v_entries_878_;
}
else
{
lean_object* v_k_881_; lean_object* v_v_882_; uint64_t v___x_883_; size_t v_h_884_; size_t v___x_885_; lean_object* v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; size_t v_h_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_k_881_ = lean_array_fget_borrowed(v_keys_875_, v_i_877_);
v_v_882_ = lean_array_fget_borrowed(v_vals_876_, v_i_877_);
v___x_883_ = l_Lean_instHashableMVarId_hash(v_k_881_);
v_h_884_ = lean_uint64_to_usize(v___x_883_);
v___x_885_ = ((size_t)5ULL);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = ((size_t)1ULL);
v___x_888_ = lean_usize_sub(v_depth_874_, v___x_887_);
v___x_889_ = lean_usize_mul(v___x_885_, v___x_888_);
v_h_890_ = lean_usize_shift_right(v_h_884_, v___x_889_);
v___x_891_ = lean_nat_add(v_i_877_, v___x_886_);
lean_dec(v_i_877_);
lean_inc(v_v_882_);
lean_inc(v_k_881_);
v___x_892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_878_, v_h_890_, v_depth_874_, v_k_881_, v_v_882_);
v_i_877_ = v___x_891_;
v_entries_878_ = v___x_892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_894_, lean_object* v_keys_895_, lean_object* v_vals_896_, lean_object* v_i_897_, lean_object* v_entries_898_){
_start:
{
size_t v_depth_boxed_899_; lean_object* v_res_900_; 
v_depth_boxed_899_ = lean_unbox_usize(v_depth_894_);
lean_dec(v_depth_894_);
v_res_900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_899_, v_keys_895_, v_vals_896_, v_i_897_, v_entries_898_);
lean_dec_ref(v_vals_896_);
lean_dec_ref(v_keys_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
size_t v_x_1046__boxed_906_; size_t v_x_1047__boxed_907_; lean_object* v_res_908_; 
v_x_1046__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_x_1047__boxed_907_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_res_908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_901_, v_x_1046__boxed_906_, v_x_1047__boxed_907_, v_x_904_, v_x_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
uint64_t v___x_912_; size_t v___x_913_; size_t v___x_914_; lean_object* v___x_915_; 
v___x_912_ = l_Lean_instHashableMVarId_hash(v_x_910_);
v___x_913_ = lean_uint64_to_usize(v___x_912_);
v___x_914_ = ((size_t)1ULL);
v___x_915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_909_, v___x_913_, v___x_914_, v_x_910_, v_x_911_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object* v_mvarId_916_, lean_object* v_val_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_mctx_921_; lean_object* v_cache_922_; lean_object* v_zetaDeltaFVarIds_923_; lean_object* v_postponed_924_; lean_object* v_diag_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_952_; 
v___x_920_ = lean_st_ref_take(v___y_918_);
v_mctx_921_ = lean_ctor_get(v___x_920_, 0);
v_cache_922_ = lean_ctor_get(v___x_920_, 1);
v_zetaDeltaFVarIds_923_ = lean_ctor_get(v___x_920_, 2);
v_postponed_924_ = lean_ctor_get(v___x_920_, 3);
v_diag_925_ = lean_ctor_get(v___x_920_, 4);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_952_ == 0)
{
v___x_927_ = v___x_920_;
v_isShared_928_ = v_isSharedCheck_952_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_diag_925_);
lean_inc(v_postponed_924_);
lean_inc(v_zetaDeltaFVarIds_923_);
lean_inc(v_cache_922_);
lean_inc(v_mctx_921_);
lean_dec(v___x_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_952_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_depth_929_; lean_object* v_levelAssignDepth_930_; lean_object* v_mvarCounter_931_; lean_object* v_lDepth_932_; lean_object* v_decls_933_; lean_object* v_userNames_934_; lean_object* v_lAssignment_935_; lean_object* v_eAssignment_936_; lean_object* v_dAssignment_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_951_; 
v_depth_929_ = lean_ctor_get(v_mctx_921_, 0);
v_levelAssignDepth_930_ = lean_ctor_get(v_mctx_921_, 1);
v_mvarCounter_931_ = lean_ctor_get(v_mctx_921_, 2);
v_lDepth_932_ = lean_ctor_get(v_mctx_921_, 3);
v_decls_933_ = lean_ctor_get(v_mctx_921_, 4);
v_userNames_934_ = lean_ctor_get(v_mctx_921_, 5);
v_lAssignment_935_ = lean_ctor_get(v_mctx_921_, 6);
v_eAssignment_936_ = lean_ctor_get(v_mctx_921_, 7);
v_dAssignment_937_ = lean_ctor_get(v_mctx_921_, 8);
v_isSharedCheck_951_ = !lean_is_exclusive(v_mctx_921_);
if (v_isSharedCheck_951_ == 0)
{
v___x_939_ = v_mctx_921_;
v_isShared_940_ = v_isSharedCheck_951_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_dAssignment_937_);
lean_inc(v_eAssignment_936_);
lean_inc(v_lAssignment_935_);
lean_inc(v_userNames_934_);
lean_inc(v_decls_933_);
lean_inc(v_lDepth_932_);
lean_inc(v_mvarCounter_931_);
lean_inc(v_levelAssignDepth_930_);
lean_inc(v_depth_929_);
lean_dec(v_mctx_921_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_951_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_936_, v_mvarId_916_, v_val_917_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 7, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_depth_929_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_levelAssignDepth_930_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_mvarCounter_931_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_lDepth_932_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_decls_933_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v_userNames_934_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_lAssignment_935_);
lean_ctor_set(v_reuseFailAlloc_950_, 7, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 8, v_dAssignment_937_);
v___x_943_ = v_reuseFailAlloc_950_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_943_);
v___x_945_ = v___x_927_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_cache_922_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_zetaDeltaFVarIds_923_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_postponed_924_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_diag_925_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_st_ref_set(v___y_918_, v___x_945_);
v___x_947_ = lean_box(0);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object* v_mvarId_953_, lean_object* v_val_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_953_, v_val_954_, v___y_955_);
lean_dec(v___y_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object* v_mvarId_958_, lean_object* v___x_959_, uint8_t v_synthetic_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
lean_inc(v_mvarId_958_);
v___x_966_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_958_, v___x_959_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_967_; 
lean_dec_ref(v___x_966_);
lean_inc(v_mvarId_958_);
v___x_967_ = l_Lean_MVarId_getType(v_mvarId_958_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref(v___x_967_);
v___x_969_ = 1;
lean_inc(v___y_962_);
v___x_970_ = l_Lean_Meta_mkLabeledSorry(v_a_968_, v_synthetic_960_, v___x_969_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v___x_970_);
v___x_972_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_958_, v_a_971_, v___y_962_);
lean_dec(v___y_962_);
return v___x_972_;
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v___y_962_);
lean_dec(v_mvarId_958_);
v_a_973_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_970_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v_mvarId_958_);
v_a_981_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_967_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_967_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v_mvarId_958_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object* v_mvarId_989_, lean_object* v___x_990_, lean_object* v_synthetic_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v_synthetic_boxed_997_; lean_object* v_res_998_; 
v_synthetic_boxed_997_ = lean_unbox(v_synthetic_991_);
v_res_998_ = l_Lean_MVarId_admit___lam__0(v_mvarId_989_, v___x_990_, v_synthetic_boxed_997_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object* v_mvarId_1002_, uint8_t v_synthetic_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
v___x_1009_ = ((lean_object*)(l_Lean_MVarId_admit___closed__1));
v___x_1010_ = lean_box(v_synthetic_1003_);
lean_inc(v_mvarId_1002_);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_MVarId_admit___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1011_, 0, v_mvarId_1002_);
lean_closure_set(v___f_1011_, 1, v___x_1009_);
lean_closure_set(v___f_1011_, 2, v___x_1010_);
v___x_1012_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_1002_, v___f_1011_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object* v_mvarId_1013_, lean_object* v_synthetic_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_synthetic_boxed_1020_; lean_object* v_res_1021_; 
v_synthetic_boxed_1020_ = lean_unbox(v_synthetic_1014_);
v_res_1021_ = l_Lean_MVarId_admit(v_mvarId_1013_, v_synthetic_boxed_1020_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object* v_mvarId_1022_, lean_object* v_val_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_1022_, v_val_1023_, v___y_1025_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object* v_mvarId_1030_, lean_object* v_val_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1030_, v_val_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object* v_00_u03b2_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_1039_, v_x_1040_, v_x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1043_, lean_object* v_x_1044_, size_t v_x_1045_, size_t v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_1044_, v_x_1045_, v_x_1046_, v_x_1047_, v_x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
size_t v_x_1383__boxed_1056_; size_t v_x_1384__boxed_1057_; lean_object* v_res_1058_; 
v_x_1383__boxed_1056_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_x_1384__boxed_1057_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_res_1058_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1050_, v_x_1051_, v_x_1383__boxed_1056_, v_x_1384__boxed_1057_, v_x_1054_, v_x_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1059_, lean_object* v_n_1060_, lean_object* v_k_1061_, lean_object* v_v_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1060_, v_k_1061_, v_v_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1064_, size_t v_depth_1065_, lean_object* v_keys_1066_, lean_object* v_vals_1067_, lean_object* v_heq_1068_, lean_object* v_i_1069_, lean_object* v_entries_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1065_, v_keys_1066_, v_vals_1067_, v_i_1069_, v_entries_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1072_, lean_object* v_depth_1073_, lean_object* v_keys_1074_, lean_object* v_vals_1075_, lean_object* v_heq_1076_, lean_object* v_i_1077_, lean_object* v_entries_1078_){
_start:
{
size_t v_depth_boxed_1079_; lean_object* v_res_1080_; 
v_depth_boxed_1079_ = lean_unbox_usize(v_depth_1073_);
lean_dec(v_depth_1073_);
v_res_1080_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1072_, v_depth_boxed_1079_, v_keys_1074_, v_vals_1075_, v_heq_1076_, v_i_1077_, v_entries_1078_);
lean_dec_ref(v_vals_1075_);
lean_dec_ref(v_keys_1074_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1082_, v_x_1083_, v_x_1084_, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object* v_mvarId_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___x_1093_; 
lean_inc(v_mvarId_1087_);
v___x_1093_ = l_Lean_MVarId_getType(v_mvarId_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = l_Lean_Expr_headBeta(v_a_1094_);
v___x_1096_ = l_Lean_MVarId_setType___redArg(v_mvarId_1087_, v___x_1095_, v_a_1089_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_mvarId_1087_);
v_a_1097_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1093_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1093_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object* v_mvarId_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_MVarId_headBetaType(v_mvarId_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object* v_a_1112_, lean_object* v_x_1113_){
_start:
{
if (lean_obj_tag(v_x_1113_) == 0)
{
uint8_t v___x_1114_; 
v___x_1114_ = 0;
return v___x_1114_;
}
else
{
lean_object* v_key_1115_; lean_object* v_tail_1116_; uint8_t v___x_1117_; 
v_key_1115_ = lean_ctor_get(v_x_1113_, 0);
v_tail_1116_ = lean_ctor_get(v_x_1113_, 2);
v___x_1117_ = l_Lean_instBEqFVarId_beq(v_key_1115_, v_a_1112_);
if (v___x_1117_ == 0)
{
v_x_1113_ = v_tail_1116_;
goto _start;
}
else
{
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object* v_a_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1119_, v_x_1120_);
lean_dec(v_x_1120_);
lean_dec(v_a_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object* v_a_1123_, lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 0)
{
return v_x_1124_;
}
else
{
lean_object* v_key_1125_; lean_object* v_value_1126_; lean_object* v_tail_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
v_key_1125_ = lean_ctor_get(v_x_1124_, 0);
v_value_1126_ = lean_ctor_get(v_x_1124_, 1);
v_tail_1127_ = lean_ctor_get(v_x_1124_, 2);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1124_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1129_ = v_x_1124_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_tail_1127_);
lean_inc(v_value_1126_);
lean_inc(v_key_1125_);
lean_dec(v_x_1124_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_instBEqFVarId_beq(v_key_1125_, v_a_1123_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1123_, v_tail_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 2, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_key_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_value_1126_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_del_object(v___x_1129_);
lean_dec(v_value_1126_);
lean_dec(v_key_1125_);
return v_tail_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object* v_a_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1137_, v_x_1138_);
lean_dec(v_a_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object* v_m_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_size_1142_; lean_object* v_buckets_1143_; lean_object* v___x_1144_; uint64_t v___x_1145_; uint64_t v___x_1146_; uint64_t v___x_1147_; uint64_t v_fold_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; uint64_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; lean_object* v_bkt_1157_; uint8_t v___x_1158_; 
v_size_1142_ = lean_ctor_get(v_m_1140_, 0);
v_buckets_1143_ = lean_ctor_get(v_m_1140_, 1);
v___x_1144_ = lean_array_get_size(v_buckets_1143_);
v___x_1145_ = l_Lean_instHashableFVarId_hash(v_a_1141_);
v___x_1146_ = 32ULL;
v___x_1147_ = lean_uint64_shift_right(v___x_1145_, v___x_1146_);
v_fold_1148_ = lean_uint64_xor(v___x_1145_, v___x_1147_);
v___x_1149_ = 16ULL;
v___x_1150_ = lean_uint64_shift_right(v_fold_1148_, v___x_1149_);
v___x_1151_ = lean_uint64_xor(v_fold_1148_, v___x_1150_);
v___x_1152_ = lean_uint64_to_usize(v___x_1151_);
v___x_1153_ = lean_usize_of_nat(v___x_1144_);
v___x_1154_ = ((size_t)1ULL);
v___x_1155_ = lean_usize_sub(v___x_1153_, v___x_1154_);
v___x_1156_ = lean_usize_land(v___x_1152_, v___x_1155_);
v_bkt_1157_ = lean_array_uget_borrowed(v_buckets_1143_, v___x_1156_);
v___x_1158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1141_, v_bkt_1157_);
if (v___x_1158_ == 0)
{
return v_m_1140_;
}
else
{
lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1171_; 
lean_inc(v_bkt_1157_);
lean_inc_ref(v_buckets_1143_);
lean_inc(v_size_1142_);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_m_1140_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; lean_object* v_unused_1173_; 
v_unused_1172_ = lean_ctor_get(v_m_1140_, 1);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_m_1140_, 0);
lean_dec(v_unused_1173_);
v___x_1160_ = v_m_1140_;
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
else
{
lean_dec(v_m_1140_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v_buckets_x27_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1162_ = lean_box(0);
v_buckets_x27_1163_ = lean_array_uset(v_buckets_1143_, v___x_1156_, v___x_1162_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_sub(v_size_1142_, v___x_1164_);
lean_dec(v_size_1142_);
v___x_1166_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1141_, v_bkt_1157_);
v___x_1167_ = lean_array_uset(v_buckets_x27_1163_, v___x_1156_, v___x_1166_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1167_);
lean_ctor_set(v___x_1160_, 0, v___x_1165_);
v___x_1169_ = v___x_1160_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object* v_m_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_1174_, v_a_1175_);
lean_dec(v_a_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object* v_e_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1184_ = lean_st_ref_take(v___y_1178_);
v___x_1185_ = l_Lean_Expr_fvarId_x21(v_e_1177_);
v___x_1186_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1184_, v___x_1185_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_st_ref_set(v___y_1178_, v___x_1186_);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object* v_e_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v_e_1190_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object* v_____r_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_st_ref_get(v___y_1199_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object* v_____r_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
return v_res_1214_;
}
}
static size_t _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; 
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = ((size_t)8192ULL);
v___x_1217_ = lean_usize_sub(v___x_1216_, v___x_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object* v_e_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v_visited_1222_; size_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; lean_object* v___x_1226_; size_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1221_ = lean_st_ref_get(v_a_1219_);
v_visited_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc_ref(v_visited_1222_);
lean_dec(v___x_1221_);
v___x_1223_ = lean_ptr_addr(v_e_1218_);
v___x_1224_ = lean_usize_once(&l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0, &l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0);
v___x_1225_ = lean_usize_mod(v___x_1223_, v___x_1224_);
v___x_1226_ = lean_array_uget(v_visited_1222_, v___x_1225_);
lean_dec_ref(v_visited_1222_);
v___x_1227_ = lean_ptr_addr(v___x_1226_);
lean_dec(v___x_1226_);
v___x_1228_ = lean_usize_dec_eq(v___x_1227_, v___x_1223_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v_visited_1230_; lean_object* v_checked_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1242_; 
v___x_1229_ = lean_st_ref_take(v_a_1219_);
v_visited_1230_ = lean_ctor_get(v___x_1229_, 0);
v_checked_1231_ = lean_ctor_get(v___x_1229_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1233_ = v___x_1229_;
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_checked_1231_);
lean_inc(v_visited_1230_);
lean_dec(v___x_1229_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = lean_array_uset(v_visited_1230_, v___x_1225_, v_e_1218_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_checked_1231_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_st_ref_set(v_a_1219_, v___x_1237_);
v___x_1239_ = lean_box(v___x_1228_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v_e_1218_);
v___x_1243_ = lean_box(v___x_1228_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_e_1245_, lean_object* v_a_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1245_, v_a_1246_);
lean_dec(v_a_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object* v_a_1249_, lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
uint8_t v___x_1251_; 
v___x_1251_ = 0;
return v___x_1251_;
}
else
{
lean_object* v_key_1252_; lean_object* v_tail_1253_; uint8_t v___x_1254_; 
v_key_1252_ = lean_ctor_get(v_x_1250_, 0);
v_tail_1253_ = lean_ctor_get(v_x_1250_, 2);
v___x_1254_ = lean_expr_eqv(v_key_1252_, v_a_1249_);
if (v___x_1254_ == 0)
{
v_x_1250_ = v_tail_1253_;
goto _start;
}
else
{
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_a_1256_, lean_object* v_x_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1256_, v_x_1257_);
lean_dec(v_x_1257_);
lean_dec_ref(v_a_1256_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 0)
{
return v_x_1260_;
}
else
{
lean_object* v_key_1262_; lean_object* v_value_1263_; lean_object* v_tail_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1287_; 
v_key_1262_ = lean_ctor_get(v_x_1261_, 0);
v_value_1263_ = lean_ctor_get(v_x_1261_, 1);
v_tail_1264_ = lean_ctor_get(v_x_1261_, 2);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_x_1261_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1266_ = v_x_1261_;
v_isShared_1267_ = v_isSharedCheck_1287_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_tail_1264_);
lean_inc(v_value_1263_);
lean_inc(v_key_1262_);
lean_dec(v_x_1261_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1287_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; uint64_t v_fold_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; uint64_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1268_ = lean_array_get_size(v_x_1260_);
v___x_1269_ = l_Lean_Expr_hash(v_key_1262_);
v___x_1270_ = 32ULL;
v___x_1271_ = lean_uint64_shift_right(v___x_1269_, v___x_1270_);
v_fold_1272_ = lean_uint64_xor(v___x_1269_, v___x_1271_);
v___x_1273_ = 16ULL;
v___x_1274_ = lean_uint64_shift_right(v_fold_1272_, v___x_1273_);
v___x_1275_ = lean_uint64_xor(v_fold_1272_, v___x_1274_);
v___x_1276_ = lean_uint64_to_usize(v___x_1275_);
v___x_1277_ = lean_usize_of_nat(v___x_1268_);
v___x_1278_ = ((size_t)1ULL);
v___x_1279_ = lean_usize_sub(v___x_1277_, v___x_1278_);
v___x_1280_ = lean_usize_land(v___x_1276_, v___x_1279_);
v___x_1281_ = lean_array_uget_borrowed(v_x_1260_, v___x_1280_);
lean_inc(v___x_1281_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 2, v___x_1281_);
v___x_1283_ = v___x_1266_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_key_1262_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_value_1263_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_array_uset(v_x_1260_, v___x_1280_, v___x_1283_);
v_x_1260_ = v___x_1284_;
v_x_1261_ = v_tail_1264_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object* v_i_1288_, lean_object* v_source_1289_, lean_object* v_target_1290_){
_start:
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = lean_array_get_size(v_source_1289_);
v___x_1292_ = lean_nat_dec_lt(v_i_1288_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_dec_ref(v_source_1289_);
lean_dec(v_i_1288_);
return v_target_1290_;
}
else
{
lean_object* v_es_1293_; lean_object* v___x_1294_; lean_object* v_source_1295_; lean_object* v_target_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_es_1293_ = lean_array_fget(v_source_1289_, v_i_1288_);
v___x_1294_ = lean_box(0);
v_source_1295_ = lean_array_fset(v_source_1289_, v_i_1288_, v___x_1294_);
v_target_1296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_1290_, v_es_1293_);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_add(v_i_1288_, v___x_1297_);
lean_dec(v_i_1288_);
v_i_1288_ = v___x_1298_;
v_source_1289_ = v_source_1295_;
v_target_1290_ = v_target_1296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object* v_data_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_nbuckets_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1301_ = lean_array_get_size(v_data_1300_);
v___x_1302_ = lean_unsigned_to_nat(2u);
v_nbuckets_1303_ = lean_nat_mul(v___x_1301_, v___x_1302_);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_mk_array(v_nbuckets_1303_, v___x_1305_);
v___x_1307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1304_, v_data_1300_, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_m_1308_, lean_object* v_a_1309_, lean_object* v_b_1310_){
_start:
{
lean_object* v_size_1311_; lean_object* v_buckets_1312_; lean_object* v___x_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; uint64_t v_fold_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; lean_object* v_bkt_1326_; uint8_t v___x_1327_; 
v_size_1311_ = lean_ctor_get(v_m_1308_, 0);
v_buckets_1312_ = lean_ctor_get(v_m_1308_, 1);
v___x_1313_ = lean_array_get_size(v_buckets_1312_);
v___x_1314_ = l_Lean_Expr_hash(v_a_1309_);
v___x_1315_ = 32ULL;
v___x_1316_ = lean_uint64_shift_right(v___x_1314_, v___x_1315_);
v_fold_1317_ = lean_uint64_xor(v___x_1314_, v___x_1316_);
v___x_1318_ = 16ULL;
v___x_1319_ = lean_uint64_shift_right(v_fold_1317_, v___x_1318_);
v___x_1320_ = lean_uint64_xor(v_fold_1317_, v___x_1319_);
v___x_1321_ = lean_uint64_to_usize(v___x_1320_);
v___x_1322_ = lean_usize_of_nat(v___x_1313_);
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_sub(v___x_1322_, v___x_1323_);
v___x_1325_ = lean_usize_land(v___x_1321_, v___x_1324_);
v_bkt_1326_ = lean_array_uget_borrowed(v_buckets_1312_, v___x_1325_);
v___x_1327_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1309_, v_bkt_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1348_; 
lean_inc_ref(v_buckets_1312_);
lean_inc(v_size_1311_);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_m_1308_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; lean_object* v_unused_1350_; 
v_unused_1349_ = lean_ctor_get(v_m_1308_, 1);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_m_1308_, 0);
lean_dec(v_unused_1350_);
v___x_1329_ = v_m_1308_;
v_isShared_1330_ = v_isSharedCheck_1348_;
goto v_resetjp_1328_;
}
else
{
lean_dec(v_m_1308_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1348_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v_size_x27_1332_; lean_object* v___x_1333_; lean_object* v_buckets_x27_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1331_ = lean_unsigned_to_nat(1u);
v_size_x27_1332_ = lean_nat_add(v_size_1311_, v___x_1331_);
lean_dec(v_size_1311_);
lean_inc(v_bkt_1326_);
v___x_1333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1333_, 0, v_a_1309_);
lean_ctor_set(v___x_1333_, 1, v_b_1310_);
lean_ctor_set(v___x_1333_, 2, v_bkt_1326_);
v_buckets_x27_1334_ = lean_array_uset(v_buckets_1312_, v___x_1325_, v___x_1333_);
v___x_1335_ = lean_unsigned_to_nat(4u);
v___x_1336_ = lean_nat_mul(v_size_x27_1332_, v___x_1335_);
v___x_1337_ = lean_unsigned_to_nat(3u);
v___x_1338_ = lean_nat_div(v___x_1336_, v___x_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_array_get_size(v_buckets_x27_1334_);
v___x_1340_ = lean_nat_dec_le(v___x_1338_, v___x_1339_);
lean_dec(v___x_1338_);
if (v___x_1340_ == 0)
{
lean_object* v_val_1341_; lean_object* v___x_1343_; 
v_val_1341_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_1334_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v_val_1341_);
lean_ctor_set(v___x_1329_, 0, v_size_x27_1332_);
v___x_1343_ = v___x_1329_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_size_x27_1332_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_val_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
else
{
lean_object* v___x_1346_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v_buckets_x27_1334_);
lean_ctor_set(v___x_1329_, 0, v_size_x27_1332_);
v___x_1346_ = v___x_1329_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_size_x27_1332_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_buckets_x27_1334_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_dec(v_b_1310_);
lean_dec_ref(v_a_1309_);
return v_m_1308_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_m_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_buckets_1353_; lean_object* v___x_1354_; uint64_t v___x_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v_fold_1358_; uint64_t v___x_1359_; uint64_t v___x_1360_; uint64_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_buckets_1353_ = lean_ctor_get(v_m_1351_, 1);
v___x_1354_ = lean_array_get_size(v_buckets_1353_);
v___x_1355_ = l_Lean_Expr_hash(v_a_1352_);
v___x_1356_ = 32ULL;
v___x_1357_ = lean_uint64_shift_right(v___x_1355_, v___x_1356_);
v_fold_1358_ = lean_uint64_xor(v___x_1355_, v___x_1357_);
v___x_1359_ = 16ULL;
v___x_1360_ = lean_uint64_shift_right(v_fold_1358_, v___x_1359_);
v___x_1361_ = lean_uint64_xor(v_fold_1358_, v___x_1360_);
v___x_1362_ = lean_uint64_to_usize(v___x_1361_);
v___x_1363_ = lean_usize_of_nat(v___x_1354_);
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_sub(v___x_1363_, v___x_1364_);
v___x_1366_ = lean_usize_land(v___x_1362_, v___x_1365_);
v___x_1367_ = lean_array_uget_borrowed(v_buckets_1353_, v___x_1366_);
v___x_1368_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1352_, v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_m_1369_, lean_object* v_a_1370_){
_start:
{
uint8_t v_res_1371_; lean_object* v_r_1372_; 
v_res_1371_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1369_, v_a_1370_);
lean_dec_ref(v_a_1370_);
lean_dec_ref(v_m_1369_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object* v_e_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v_checked_1377_; uint8_t v___x_1378_; 
v___x_1376_ = lean_st_ref_get(v_a_1374_);
v_checked_1377_ = lean_ctor_get(v___x_1376_, 1);
lean_inc_ref(v_checked_1377_);
lean_dec(v___x_1376_);
v___x_1378_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_1377_, v_e_1373_);
lean_dec_ref(v_checked_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v_visited_1380_; lean_object* v_checked_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1393_; 
v___x_1379_ = lean_st_ref_take(v_a_1374_);
v_visited_1380_ = lean_ctor_get(v___x_1379_, 0);
v_checked_1381_ = lean_ctor_get(v___x_1379_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1383_ = v___x_1379_;
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_checked_1381_);
lean_inc(v_visited_1380_);
lean_dec(v___x_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_1381_, v_e_1373_, v___x_1385_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1386_);
v___x_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_visited_1380_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = lean_st_ref_set(v_a_1374_, v___x_1388_);
v___x_1390_ = lean_box(v___x_1378_);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec_ref(v_e_1373_);
v___x_1394_ = lean_box(v___x_1378_);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_e_1396_, lean_object* v_a_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1396_, v_a_1397_);
lean_dec(v_a_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object* v_p_1400_, lean_object* v_f_1401_, uint8_t v_stopWhenVisited_1402_, lean_object* v_e_1403_, lean_object* v_a_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v_d_1417_; lean_object* v_b_1418_; lean_object* v___y_1419_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___x_1449_; 
lean_inc_ref(v_e_1403_);
v___x_1449_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1482_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1482_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1482_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_unbox(v_a_1450_);
lean_dec(v_a_1450_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
lean_del_object(v___x_1452_);
lean_inc_ref(v_p_1400_);
lean_inc_ref(v_e_1403_);
v___x_1455_ = lean_apply_1(v_p_1400_, v_e_1403_);
v___x_1456_ = lean_unbox(v___x_1455_);
if (v___x_1456_ == 0)
{
v___y_1423_ = v_a_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
v___y_1427_ = v___y_1408_;
v___y_1428_ = v___y_1409_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1457_; 
lean_inc_ref(v_e_1403_);
v___x_1457_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; uint8_t v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = lean_unbox(v_a_1458_);
lean_dec(v_a_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_inc_ref(v_f_1401_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v_e_1403_);
v___x_1460_ = lean_apply_7(v_f_1401_, v_e_1403_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, lean_box(0));
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1468_; 
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v___x_1460_, 0);
lean_dec(v_unused_1469_);
v___x_1462_ = v___x_1460_;
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
else
{
lean_dec(v___x_1460_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
if (v_stopWhenVisited_1402_ == 0)
{
lean_del_object(v___x_1462_);
v___y_1423_ = v_a_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
v___y_1427_ = v___y_1408_;
v___y_1428_ = v___y_1409_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v_e_1403_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
v___x_1464_ = lean_box(0);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1464_);
v___x_1466_ = v___x_1462_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v_e_1403_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
return v___x_1460_;
}
}
else
{
v___y_1423_ = v_a_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
v___y_1427_ = v___y_1408_;
v___y_1428_ = v___y_1409_;
goto v___jp_1422_;
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v_e_1403_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
v_a_1470_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1457_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1457_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1480_; 
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v_e_1403_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
v___x_1478_ = lean_box(0);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1478_);
v___x_1480_ = v___x_1452_;
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
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v_e_1403_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
v_a_1483_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1449_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1449_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
v___jp_1411_:
{
lean_object* v___x_1420_; 
lean_inc(v___y_1415_);
lean_inc_ref(v___y_1412_);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1416_);
lean_inc(v___y_1414_);
lean_inc_ref(v_f_1401_);
lean_inc_ref(v_p_1400_);
v___x_1420_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1400_, v_f_1401_, v_stopWhenVisited_1402_, v_d_1417_, v___y_1419_, v___y_1414_, v___y_1416_, v___y_1413_, v___y_1412_, v___y_1415_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_dec_ref(v___x_1420_);
v_e_1403_ = v_b_1418_;
v_a_1404_ = v___y_1419_;
v___y_1405_ = v___y_1414_;
v___y_1406_ = v___y_1416_;
v___y_1407_ = v___y_1413_;
v___y_1408_ = v___y_1412_;
v___y_1409_ = v___y_1415_;
goto _start;
}
else
{
lean_dec_ref(v_b_1418_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
return v___x_1420_;
}
}
v___jp_1422_:
{
switch(lean_obj_tag(v_e_1403_))
{
case 7:
{
lean_object* v_binderType_1429_; lean_object* v_body_1430_; 
v_binderType_1429_ = lean_ctor_get(v_e_1403_, 1);
lean_inc_ref(v_binderType_1429_);
v_body_1430_ = lean_ctor_get(v_e_1403_, 2);
lean_inc_ref(v_body_1430_);
lean_dec_ref(v_e_1403_);
v___y_1412_ = v___y_1427_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v___y_1424_;
v___y_1415_ = v___y_1428_;
v___y_1416_ = v___y_1425_;
v_d_1417_ = v_binderType_1429_;
v_b_1418_ = v_body_1430_;
v___y_1419_ = v___y_1423_;
goto v___jp_1411_;
}
case 6:
{
lean_object* v_binderType_1431_; lean_object* v_body_1432_; 
v_binderType_1431_ = lean_ctor_get(v_e_1403_, 1);
lean_inc_ref(v_binderType_1431_);
v_body_1432_ = lean_ctor_get(v_e_1403_, 2);
lean_inc_ref(v_body_1432_);
lean_dec_ref(v_e_1403_);
v___y_1412_ = v___y_1427_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v___y_1424_;
v___y_1415_ = v___y_1428_;
v___y_1416_ = v___y_1425_;
v_d_1417_ = v_binderType_1431_;
v_b_1418_ = v_body_1432_;
v___y_1419_ = v___y_1423_;
goto v___jp_1411_;
}
case 8:
{
lean_object* v_type_1433_; lean_object* v_value_1434_; lean_object* v_body_1435_; lean_object* v___x_1436_; 
v_type_1433_ = lean_ctor_get(v_e_1403_, 1);
lean_inc_ref(v_type_1433_);
v_value_1434_ = lean_ctor_get(v_e_1403_, 2);
lean_inc_ref(v_value_1434_);
v_body_1435_ = lean_ctor_get(v_e_1403_, 3);
lean_inc_ref(v_body_1435_);
lean_dec_ref(v_e_1403_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v_f_1401_);
lean_inc_ref(v_p_1400_);
v___x_1436_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1400_, v_f_1401_, v_stopWhenVisited_1402_, v_type_1433_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v___x_1437_; 
lean_dec_ref(v___x_1436_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v_f_1401_);
lean_inc_ref(v_p_1400_);
v___x_1437_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1400_, v_f_1401_, v_stopWhenVisited_1402_, v_value_1434_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_dec_ref(v___x_1437_);
v_e_1403_ = v_body_1435_;
v_a_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
goto _start;
}
else
{
lean_dec_ref(v_body_1435_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
return v___x_1437_;
}
}
else
{
lean_dec_ref(v_body_1435_);
lean_dec_ref(v_value_1434_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
return v___x_1436_;
}
}
case 5:
{
lean_object* v_fn_1439_; lean_object* v_arg_1440_; lean_object* v___x_1441_; 
v_fn_1439_ = lean_ctor_get(v_e_1403_, 0);
lean_inc_ref(v_fn_1439_);
v_arg_1440_ = lean_ctor_get(v_e_1403_, 1);
lean_inc_ref(v_arg_1440_);
lean_dec_ref(v_e_1403_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v_f_1401_);
lean_inc_ref(v_p_1400_);
v___x_1441_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1400_, v_f_1401_, v_stopWhenVisited_1402_, v_fn_1439_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_dec_ref(v___x_1441_);
v_e_1403_ = v_arg_1440_;
v_a_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1440_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
return v___x_1441_;
}
}
case 10:
{
lean_object* v_expr_1443_; 
v_expr_1443_ = lean_ctor_get(v_e_1403_, 1);
lean_inc_ref(v_expr_1443_);
lean_dec_ref(v_e_1403_);
v_e_1403_ = v_expr_1443_;
v_a_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
goto _start;
}
case 11:
{
lean_object* v_struct_1445_; 
v_struct_1445_ = lean_ctor_get(v_e_1403_, 2);
lean_inc_ref(v_struct_1445_);
lean_dec_ref(v_e_1403_);
v_e_1403_ = v_struct_1445_;
v_a_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
goto _start;
}
default: 
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v_e_1403_);
lean_dec_ref(v_f_1401_);
lean_dec_ref(v_p_1400_);
v___x_1447_ = lean_box(0);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object* v_p_1491_, lean_object* v_f_1492_, lean_object* v_stopWhenVisited_1493_, lean_object* v_e_1494_, lean_object* v_a_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1502_; lean_object* v_res_1503_; 
v_stopWhenVisited_boxed_1502_ = lean_unbox(v_stopWhenVisited_1493_);
v_res_1503_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1491_, v_f_1492_, v_stopWhenVisited_boxed_1502_, v_e_1494_, v_a_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v_a_1495_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_1504_, lean_object* v_f_1505_, lean_object* v_e_1506_, uint8_t v_stopWhenVisited_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = l_Lean_ForEachExprWhere_initCache;
v___x_1515_ = lean_st_mk_ref(v___x_1514_);
v___x_1516_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1504_, v_f_1505_, v_stopWhenVisited_1507_, v_e_1506_, v___x_1515_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1525_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_st_ref_get(v___x_1515_);
lean_dec(v___x_1515_);
lean_dec(v___x_1521_);
if (v_isShared_1520_ == 0)
{
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1517_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
else
{
lean_dec(v___x_1515_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_1526_, lean_object* v_f_1527_, lean_object* v_e_1528_, lean_object* v_stopWhenVisited_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1536_; lean_object* v_res_1537_; 
v_stopWhenVisited_boxed_1536_ = lean_unbox(v_stopWhenVisited_1529_);
v_res_1537_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1526_, v_f_1527_, v_e_1528_, v_stopWhenVisited_boxed_1536_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object* v___f_1539_, lean_object* v___f_1540_, uint8_t v___x_1541_, lean_object* v_e_1542_, lean_object* v_candidates_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_1542_, v___y_1545_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; lean_object* v___y_1553_; uint8_t v___x_1563_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = lean_st_mk_ref(v_candidates_1543_);
v___x_1563_ = l_Lean_Expr_hasFVar(v_a_1550_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec(v_a_1550_);
lean_dec_ref(v___f_1540_);
v___x_1564_ = lean_box(0);
lean_inc(v___x_1551_);
v___x_1565_ = lean_apply_7(v___f_1539_, v___x_1564_, v___x_1551_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, lean_box(0));
v___y_1553_ = v___x_1565_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
lean_inc(v___y_1547_);
lean_inc_ref(v___y_1546_);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___x_1551_);
v___x_1567_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1566_, v___f_1540_, v_a_1550_, v___x_1541_, v___x_1551_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1567_);
lean_inc(v___x_1551_);
v___x_1569_ = lean_apply_7(v___f_1539_, v_a_1568_, v___x_1551_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, lean_box(0));
v___y_1553_ = v___x_1569_;
goto v___jp_1552_;
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v___x_1551_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v___f_1539_);
v_a_1570_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1567_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1567_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
v___jp_1552_:
{
if (lean_obj_tag(v___y_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1562_; 
v_a_1554_ = lean_ctor_get(v___y_1553_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___y_1553_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1556_ = v___y_1553_;
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___y_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = lean_st_ref_get(v___x_1551_);
lean_dec(v___x_1551_);
lean_dec(v___x_1558_);
if (v_isShared_1557_ == 0)
{
v___x_1560_ = v___x_1556_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1554_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_dec(v___x_1551_);
return v___y_1553_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_candidates_1543_);
lean_dec_ref(v___f_1540_);
lean_dec_ref(v___f_1539_);
v_a_1578_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1549_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1549_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object* v___f_1586_, lean_object* v___f_1587_, lean_object* v___x_1588_, lean_object* v_e_1589_, lean_object* v_candidates_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v___x_17981__boxed_1596_; lean_object* v_res_1597_; 
v___x_17981__boxed_1596_ = lean_unbox(v___x_1588_);
v_res_1597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1586_, v___f_1587_, v___x_17981__boxed_1596_, v_e_1589_, v_candidates_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_e_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1605_ = lean_st_ref_take(v___y_1599_);
v___x_1606_ = l_Lean_Expr_fvarId_x21(v_e_1598_);
v___x_1607_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1605_, v___x_1606_);
lean_dec(v___x_1606_);
v___x_1608_ = lean_st_ref_set(v___y_1599_, v___x_1607_);
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_e_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_e_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v_e_1611_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_____r_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_st_ref_get(v___y_1620_);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_____r_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_____r_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_x_1636_, lean_object* v_x_1637_){
_start:
{
if (lean_obj_tag(v_x_1637_) == 0)
{
return v_x_1636_;
}
else
{
lean_object* v_key_1638_; lean_object* v_value_1639_; lean_object* v_tail_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1663_; 
v_key_1638_ = lean_ctor_get(v_x_1637_, 0);
v_value_1639_ = lean_ctor_get(v_x_1637_, 1);
v_tail_1640_ = lean_ctor_get(v_x_1637_, 2);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1642_ = v_x_1637_;
v_isShared_1643_ = v_isSharedCheck_1663_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_tail_1640_);
lean_inc(v_value_1639_);
lean_inc(v_key_1638_);
lean_dec(v_x_1637_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1663_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; uint64_t v___x_1645_; uint64_t v___x_1646_; uint64_t v___x_1647_; uint64_t v_fold_1648_; uint64_t v___x_1649_; uint64_t v___x_1650_; uint64_t v___x_1651_; size_t v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; size_t v___x_1655_; size_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1644_ = lean_array_get_size(v_x_1636_);
v___x_1645_ = l_Lean_instHashableFVarId_hash(v_key_1638_);
v___x_1646_ = 32ULL;
v___x_1647_ = lean_uint64_shift_right(v___x_1645_, v___x_1646_);
v_fold_1648_ = lean_uint64_xor(v___x_1645_, v___x_1647_);
v___x_1649_ = 16ULL;
v___x_1650_ = lean_uint64_shift_right(v_fold_1648_, v___x_1649_);
v___x_1651_ = lean_uint64_xor(v_fold_1648_, v___x_1650_);
v___x_1652_ = lean_uint64_to_usize(v___x_1651_);
v___x_1653_ = lean_usize_of_nat(v___x_1644_);
v___x_1654_ = ((size_t)1ULL);
v___x_1655_ = lean_usize_sub(v___x_1653_, v___x_1654_);
v___x_1656_ = lean_usize_land(v___x_1652_, v___x_1655_);
v___x_1657_ = lean_array_uget_borrowed(v_x_1636_, v___x_1656_);
lean_inc(v___x_1657_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 2, v___x_1657_);
v___x_1659_ = v___x_1642_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_key_1638_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_value_1639_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_array_uset(v_x_1636_, v___x_1656_, v___x_1659_);
v_x_1636_ = v___x_1660_;
v_x_1637_ = v_tail_1640_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object* v_i_1664_, lean_object* v_source_1665_, lean_object* v_target_1666_){
_start:
{
lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1667_ = lean_array_get_size(v_source_1665_);
v___x_1668_ = lean_nat_dec_lt(v_i_1664_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_dec_ref(v_source_1665_);
lean_dec(v_i_1664_);
return v_target_1666_;
}
else
{
lean_object* v_es_1669_; lean_object* v___x_1670_; lean_object* v_source_1671_; lean_object* v_target_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_es_1669_ = lean_array_fget(v_source_1665_, v_i_1664_);
v___x_1670_ = lean_box(0);
v_source_1671_ = lean_array_fset(v_source_1665_, v_i_1664_, v___x_1670_);
v_target_1672_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_1666_, v_es_1669_);
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = lean_nat_add(v_i_1664_, v___x_1673_);
lean_dec(v_i_1664_);
v_i_1664_ = v___x_1674_;
v_source_1665_ = v_source_1671_;
v_target_1666_ = v_target_1672_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object* v_data_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v_nbuckets_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1677_ = lean_array_get_size(v_data_1676_);
v___x_1678_ = lean_unsigned_to_nat(2u);
v_nbuckets_1679_ = lean_nat_mul(v___x_1677_, v___x_1678_);
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_mk_array(v_nbuckets_1679_, v___x_1681_);
v___x_1683_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1680_, v_data_1676_, v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1684_, lean_object* v_a_1685_, lean_object* v_b_1686_){
_start:
{
lean_object* v_size_1687_; lean_object* v_buckets_1688_; lean_object* v___x_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; uint64_t v_fold_1693_; uint64_t v___x_1694_; uint64_t v___x_1695_; uint64_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; lean_object* v_bkt_1702_; uint8_t v___x_1703_; 
v_size_1687_ = lean_ctor_get(v_m_1684_, 0);
v_buckets_1688_ = lean_ctor_get(v_m_1684_, 1);
v___x_1689_ = lean_array_get_size(v_buckets_1688_);
v___x_1690_ = l_Lean_instHashableFVarId_hash(v_a_1685_);
v___x_1691_ = 32ULL;
v___x_1692_ = lean_uint64_shift_right(v___x_1690_, v___x_1691_);
v_fold_1693_ = lean_uint64_xor(v___x_1690_, v___x_1692_);
v___x_1694_ = 16ULL;
v___x_1695_ = lean_uint64_shift_right(v_fold_1693_, v___x_1694_);
v___x_1696_ = lean_uint64_xor(v_fold_1693_, v___x_1695_);
v___x_1697_ = lean_uint64_to_usize(v___x_1696_);
v___x_1698_ = lean_usize_of_nat(v___x_1689_);
v___x_1699_ = ((size_t)1ULL);
v___x_1700_ = lean_usize_sub(v___x_1698_, v___x_1699_);
v___x_1701_ = lean_usize_land(v___x_1697_, v___x_1700_);
v_bkt_1702_ = lean_array_uget_borrowed(v_buckets_1688_, v___x_1701_);
v___x_1703_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1685_, v_bkt_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1724_; 
lean_inc_ref(v_buckets_1688_);
lean_inc(v_size_1687_);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_m_1684_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; lean_object* v_unused_1726_; 
v_unused_1725_ = lean_ctor_get(v_m_1684_, 1);
lean_dec(v_unused_1725_);
v_unused_1726_ = lean_ctor_get(v_m_1684_, 0);
lean_dec(v_unused_1726_);
v___x_1705_ = v_m_1684_;
v_isShared_1706_ = v_isSharedCheck_1724_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v_m_1684_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1724_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v_size_x27_1708_; lean_object* v___x_1709_; lean_object* v_buckets_x27_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1707_ = lean_unsigned_to_nat(1u);
v_size_x27_1708_ = lean_nat_add(v_size_1687_, v___x_1707_);
lean_dec(v_size_1687_);
lean_inc(v_bkt_1702_);
v___x_1709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1709_, 0, v_a_1685_);
lean_ctor_set(v___x_1709_, 1, v_b_1686_);
lean_ctor_set(v___x_1709_, 2, v_bkt_1702_);
v_buckets_x27_1710_ = lean_array_uset(v_buckets_1688_, v___x_1701_, v___x_1709_);
v___x_1711_ = lean_unsigned_to_nat(4u);
v___x_1712_ = lean_nat_mul(v_size_x27_1708_, v___x_1711_);
v___x_1713_ = lean_unsigned_to_nat(3u);
v___x_1714_ = lean_nat_div(v___x_1712_, v___x_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_array_get_size(v_buckets_x27_1710_);
v___x_1716_ = lean_nat_dec_le(v___x_1714_, v___x_1715_);
lean_dec(v___x_1714_);
if (v___x_1716_ == 0)
{
lean_object* v_val_1717_; lean_object* v___x_1719_; 
v_val_1717_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1710_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v_val_1717_);
lean_ctor_set(v___x_1705_, 0, v_size_x27_1708_);
v___x_1719_ = v___x_1705_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_size_x27_1708_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_val_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
else
{
lean_object* v___x_1722_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v_buckets_x27_1710_);
lean_ctor_set(v___x_1705_, 0, v_size_x27_1708_);
v___x_1722_ = v___x_1705_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_size_x27_1708_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_buckets_x27_1710_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
else
{
lean_dec(v_b_1686_);
lean_dec(v_a_1685_);
return v_m_1684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1729_, size_t v_sz_1730_, size_t v_i_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_lt(v_i_1731_, v_sz_1730_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_b_1732_);
return v___x_1739_;
}
else
{
lean_object* v_snd_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1804_; 
v_snd_1740_ = lean_ctor_get(v_b_1732_, 1);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_b_1732_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v_b_1732_, 0);
lean_dec(v_unused_1805_);
v___x_1742_ = v_b_1732_;
v_isShared_1743_ = v_isSharedCheck_1804_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_snd_1740_);
lean_dec(v_b_1732_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1804_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v_a_1746_; lean_object* v_a_1753_; 
v___x_1744_ = lean_box(0);
v_a_1753_ = lean_array_uget_borrowed(v_as_1729_, v_i_1731_);
if (lean_obj_tag(v_a_1753_) == 0)
{
v_a_1746_ = v_snd_1740_;
goto v___jp_1745_;
}
else
{
lean_object* v_val_1754_; lean_object* v___y_1756_; uint8_t v___x_1760_; 
v_val_1754_ = lean_ctor_get(v_a_1753_, 0);
v___x_1760_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1754_);
if (v___x_1760_ == 0)
{
lean_object* v___f_1761_; lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v_candidates_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___x_1782_; 
v___f_1761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1763_ = l_Lean_LocalDecl_type(v_val_1754_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc_ref(v___x_1763_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1762_, v___f_1761_, v___x_1760_, v___x_1763_, v_snd_1740_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = l_Lean_LocalDecl_value_x3f(v_val_1754_, v___x_1760_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
v_candidates_1765_ = v_a_1783_;
v___y_1766_ = v___y_1733_;
v___y_1767_ = v___y_1734_;
v___y_1768_ = v___y_1735_;
v___y_1769_ = v___y_1736_;
goto v___jp_1764_;
}
else
{
lean_object* v_val_1785_; lean_object* v___x_1786_; 
v_val_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_val_1785_);
lean_dec_ref(v___x_1784_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1762_, v___f_1761_, v___x_1760_, v_val_1785_, v_a_1783_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v___x_1786_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
v_candidates_1765_ = v_a_1787_;
v___y_1766_ = v___y_1733_;
v___y_1767_ = v___y_1734_;
v___y_1768_ = v___y_1735_;
v___y_1769_ = v___y_1736_;
goto v___jp_1764_;
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v___x_1763_);
lean_del_object(v___x_1742_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
v_a_1788_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1786_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1786_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v___x_1763_);
lean_del_object(v___x_1742_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
v_a_1796_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1782_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1782_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
v___jp_1764_:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Meta_isProp(v___x_1763_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; uint8_t v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = lean_unbox(v_a_1771_);
lean_dec(v_a_1771_);
if (v___x_1772_ == 0)
{
v_a_1746_ = v_candidates_1765_;
goto v___jp_1745_;
}
else
{
uint8_t v___x_1773_; 
v___x_1773_ = l_Lean_LocalDecl_hasValue(v_val_1754_, v___x_1760_);
if (v___x_1773_ == 0)
{
v___y_1756_ = v_candidates_1765_;
goto v___jp_1755_;
}
else
{
if (v___x_1760_ == 0)
{
v_a_1746_ = v_candidates_1765_;
goto v___jp_1745_;
}
else
{
v___y_1756_ = v_candidates_1765_;
goto v___jp_1755_;
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref(v_candidates_1765_);
lean_del_object(v___x_1742_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
v_a_1774_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1770_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1770_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
else
{
v_a_1746_ = v_snd_1740_;
goto v___jp_1745_;
}
v___jp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = l_Lean_LocalDecl_fvarId(v_val_1754_);
v___x_1758_ = lean_box(0);
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1756_, v___x_1757_, v___x_1758_);
v_a_1746_ = v___x_1759_;
goto v___jp_1745_;
}
}
v___jp_1745_:
{
lean_object* v___x_1748_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v_a_1746_);
lean_ctor_set(v___x_1742_, 0, v___x_1744_);
v___x_1748_ = v___x_1742_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_a_1746_);
v___x_1748_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
size_t v___x_1749_; size_t v___x_1750_; 
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_add(v_i_1731_, v___x_1749_);
v_i_1731_ = v___x_1750_;
v_b_1732_ = v___x_1748_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1806_, lean_object* v_sz_1807_, lean_object* v_i_1808_, lean_object* v_b_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
size_t v_sz_boxed_1815_; size_t v_i_boxed_1816_; lean_object* v_res_1817_; 
v_sz_boxed_1815_ = lean_unbox_usize(v_sz_1807_);
lean_dec(v_sz_1807_);
v_i_boxed_1816_ = lean_unbox_usize(v_i_1808_);
lean_dec(v_i_1808_);
v_res_1817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1806_, v_sz_boxed_1815_, v_i_boxed_1816_, v_b_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec_ref(v_as_1806_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1818_, size_t v_sz_1819_, size_t v_i_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_usize_dec_lt(v_i_1820_, v_sz_1819_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_b_1821_);
return v___x_1828_;
}
else
{
lean_object* v_snd_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1893_; 
v_snd_1829_ = lean_ctor_get(v_b_1821_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_b_1821_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v_b_1821_, 0);
lean_dec(v_unused_1894_);
v___x_1831_ = v_b_1821_;
v_isShared_1832_ = v_isSharedCheck_1893_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_snd_1829_);
lean_dec(v_b_1821_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1893_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v_a_1835_; lean_object* v_a_1842_; 
v___x_1833_ = lean_box(0);
v_a_1842_ = lean_array_uget_borrowed(v_as_1818_, v_i_1820_);
if (lean_obj_tag(v_a_1842_) == 0)
{
v_a_1835_ = v_snd_1829_;
goto v___jp_1834_;
}
else
{
lean_object* v_val_1843_; lean_object* v___y_1845_; uint8_t v___x_1849_; 
v_val_1843_ = lean_ctor_get(v_a_1842_, 0);
v___x_1849_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1843_);
if (v___x_1849_ == 0)
{
lean_object* v___f_1850_; lean_object* v___f_1851_; lean_object* v___x_1852_; lean_object* v_candidates_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___x_1871_; 
v___f_1850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1852_ = l_Lean_LocalDecl_type(v_val_1843_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
lean_inc_ref(v___x_1852_);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1851_, v___f_1850_, v___x_1849_, v___x_1852_, v_snd_1829_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___x_1871_);
v___x_1873_ = l_Lean_LocalDecl_value_x3f(v_val_1843_, v___x_1849_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
v_candidates_1854_ = v_a_1872_;
v___y_1855_ = v___y_1822_;
v___y_1856_ = v___y_1823_;
v___y_1857_ = v___y_1824_;
v___y_1858_ = v___y_1825_;
goto v___jp_1853_;
}
else
{
lean_object* v_val_1874_; lean_object* v___x_1875_; 
v_val_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_val_1874_);
lean_dec_ref(v___x_1873_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1851_, v___f_1850_, v___x_1849_, v_val_1874_, v_a_1872_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref(v___x_1875_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
v_candidates_1854_ = v_a_1876_;
v___y_1855_ = v___y_1822_;
v___y_1856_ = v___y_1823_;
v___y_1857_ = v___y_1824_;
v___y_1858_ = v___y_1825_;
goto v___jp_1853_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v___x_1852_);
lean_del_object(v___x_1831_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
v_a_1877_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1875_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec_ref(v___x_1852_);
lean_del_object(v___x_1831_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
v_a_1885_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1871_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1871_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
v___jp_1853_:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_Meta_isProp(v___x_1852_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; uint8_t v___x_1861_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = lean_unbox(v_a_1860_);
lean_dec(v_a_1860_);
if (v___x_1861_ == 0)
{
v_a_1835_ = v_candidates_1854_;
goto v___jp_1834_;
}
else
{
uint8_t v___x_1862_; 
v___x_1862_ = l_Lean_LocalDecl_hasValue(v_val_1843_, v___x_1849_);
if (v___x_1862_ == 0)
{
v___y_1845_ = v_candidates_1854_;
goto v___jp_1844_;
}
else
{
if (v___x_1849_ == 0)
{
v_a_1835_ = v_candidates_1854_;
goto v___jp_1834_;
}
else
{
v___y_1845_ = v_candidates_1854_;
goto v___jp_1844_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_candidates_1854_);
lean_del_object(v___x_1831_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
v_a_1863_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1859_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1859_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
else
{
v_a_1835_ = v_snd_1829_;
goto v___jp_1834_;
}
v___jp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = l_Lean_LocalDecl_fvarId(v_val_1843_);
v___x_1847_ = lean_box(0);
v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1845_, v___x_1846_, v___x_1847_);
v_a_1835_ = v___x_1848_;
goto v___jp_1834_;
}
}
v___jp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 1, v_a_1835_);
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1837_ = v___x_1831_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_a_1835_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
size_t v___x_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = ((size_t)1ULL);
v___x_1839_ = lean_usize_add(v_i_1820_, v___x_1838_);
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1818_, v_sz_1819_, v___x_1839_, v___x_1837_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
return v___x_1840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object* v_as_1895_, lean_object* v_sz_1896_, lean_object* v_i_1897_, lean_object* v_b_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
size_t v_sz_boxed_1904_; size_t v_i_boxed_1905_; lean_object* v_res_1906_; 
v_sz_boxed_1904_ = lean_unbox_usize(v_sz_1896_);
lean_dec(v_sz_1896_);
v_i_boxed_1905_ = lean_unbox_usize(v_i_1897_);
lean_dec(v_i_1897_);
v_res_1906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1895_, v_sz_boxed_1904_, v_i_boxed_1905_, v_b_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec_ref(v_as_1895_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object* v_as_1907_, size_t v_sz_1908_, size_t v_i_1909_, lean_object* v_b_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_usize_dec_lt(v_i_1909_, v_sz_1908_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_b_1910_);
return v___x_1917_;
}
else
{
lean_object* v_snd_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1982_; 
v_snd_1918_ = lean_ctor_get(v_b_1910_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_b_1910_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_b_1910_, 0);
lean_dec(v_unused_1983_);
v___x_1920_ = v_b_1910_;
v_isShared_1921_ = v_isSharedCheck_1982_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_snd_1918_);
lean_dec(v_b_1910_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1982_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v_a_1924_; lean_object* v_a_1931_; 
v___x_1922_ = lean_box(0);
v_a_1931_ = lean_array_uget_borrowed(v_as_1907_, v_i_1909_);
if (lean_obj_tag(v_a_1931_) == 0)
{
v_a_1924_ = v_snd_1918_;
goto v___jp_1923_;
}
else
{
lean_object* v_val_1932_; lean_object* v___y_1934_; uint8_t v___x_1938_; 
v_val_1932_ = lean_ctor_get(v_a_1931_, 0);
v___x_1938_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1932_);
if (v___x_1938_ == 0)
{
lean_object* v___f_1939_; lean_object* v___f_1940_; lean_object* v___x_1941_; lean_object* v_candidates_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___x_1960_; 
v___f_1939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1941_ = l_Lean_LocalDecl_type(v_val_1932_);
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc_ref(v___x_1941_);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1940_, v___f_1939_, v___x_1938_, v___x_1941_, v_snd_1918_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1962_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref(v___x_1960_);
v___x_1962_ = l_Lean_LocalDecl_value_x3f(v_val_1932_, v___x_1938_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
v_candidates_1943_ = v_a_1961_;
v___y_1944_ = v___y_1911_;
v___y_1945_ = v___y_1912_;
v___y_1946_ = v___y_1913_;
v___y_1947_ = v___y_1914_;
goto v___jp_1942_;
}
else
{
lean_object* v_val_1963_; lean_object* v___x_1964_; 
v_val_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_val_1963_);
lean_dec_ref(v___x_1962_);
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1940_, v___f_1939_, v___x_1938_, v_val_1963_, v_a_1961_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref(v___x_1964_);
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
v_candidates_1943_ = v_a_1965_;
v___y_1944_ = v___y_1911_;
v___y_1945_ = v___y_1912_;
v___y_1946_ = v___y_1913_;
v___y_1947_ = v___y_1914_;
goto v___jp_1942_;
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v___x_1941_);
lean_del_object(v___x_1920_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
v_a_1966_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1964_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1964_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v___x_1941_);
lean_del_object(v___x_1920_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
v_a_1974_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1960_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1960_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
v___jp_1942_:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_Meta_isProp(v___x_1941_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; uint8_t v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1948_);
v___x_1950_ = lean_unbox(v_a_1949_);
lean_dec(v_a_1949_);
if (v___x_1950_ == 0)
{
v_a_1924_ = v_candidates_1943_;
goto v___jp_1923_;
}
else
{
uint8_t v___x_1951_; 
v___x_1951_ = l_Lean_LocalDecl_hasValue(v_val_1932_, v___x_1938_);
if (v___x_1951_ == 0)
{
v___y_1934_ = v_candidates_1943_;
goto v___jp_1933_;
}
else
{
if (v___x_1938_ == 0)
{
v_a_1924_ = v_candidates_1943_;
goto v___jp_1923_;
}
else
{
v___y_1934_ = v_candidates_1943_;
goto v___jp_1933_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_candidates_1943_);
lean_del_object(v___x_1920_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
v_a_1952_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1948_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1948_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
else
{
v_a_1924_ = v_snd_1918_;
goto v___jp_1923_;
}
v___jp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = l_Lean_LocalDecl_fvarId(v_val_1932_);
v___x_1936_ = lean_box(0);
v___x_1937_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1934_, v___x_1935_, v___x_1936_);
v_a_1924_ = v___x_1937_;
goto v___jp_1923_;
}
}
v___jp_1923_:
{
lean_object* v___x_1926_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v_a_1924_);
lean_ctor_set(v___x_1920_, 0, v___x_1922_);
v___x_1926_ = v___x_1920_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_a_1924_);
v___x_1926_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
size_t v___x_1927_; size_t v___x_1928_; 
v___x_1927_ = ((size_t)1ULL);
v___x_1928_ = lean_usize_add(v_i_1909_, v___x_1927_);
v_i_1909_ = v___x_1928_;
v_b_1910_ = v___x_1926_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object* v_as_1984_, lean_object* v_sz_1985_, lean_object* v_i_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
size_t v_sz_boxed_1993_; size_t v_i_boxed_1994_; lean_object* v_res_1995_; 
v_sz_boxed_1993_ = lean_unbox_usize(v_sz_1985_);
lean_dec(v_sz_1985_);
v_i_boxed_1994_ = lean_unbox_usize(v_i_1986_);
lean_dec(v_i_1986_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1984_, v_sz_boxed_1993_, v_i_boxed_1994_, v_b_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec_ref(v_as_1984_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object* v_as_1996_, size_t v_sz_1997_, size_t v_i_1998_, lean_object* v_b_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_1998_, v_sz_1997_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_b_1999_);
return v___x_2006_;
}
else
{
lean_object* v_snd_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2071_; 
v_snd_2007_ = lean_ctor_get(v_b_1999_, 1);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_b_1999_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v_b_1999_, 0);
lean_dec(v_unused_2072_);
v___x_2009_ = v_b_1999_;
v_isShared_2010_ = v_isSharedCheck_2071_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snd_2007_);
lean_dec(v_b_1999_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2071_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v_a_2013_; lean_object* v_a_2020_; 
v___x_2011_ = lean_box(0);
v_a_2020_ = lean_array_uget_borrowed(v_as_1996_, v_i_1998_);
if (lean_obj_tag(v_a_2020_) == 0)
{
v_a_2013_ = v_snd_2007_;
goto v___jp_2012_;
}
else
{
lean_object* v_val_2021_; lean_object* v___y_2023_; uint8_t v___x_2027_; 
v_val_2021_ = lean_ctor_get(v_a_2020_, 0);
v___x_2027_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2021_);
if (v___x_2027_ == 0)
{
lean_object* v___f_2028_; lean_object* v___f_2029_; lean_object* v___x_2030_; lean_object* v_candidates_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___x_2049_; 
v___f_2028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2030_ = l_Lean_LocalDecl_type(v_val_2021_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
lean_inc_ref(v___x_2030_);
v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2029_, v___f_2028_, v___x_2027_, v___x_2030_, v_snd_2007_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = l_Lean_LocalDecl_value_x3f(v_val_2021_, v___x_2027_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
v_candidates_2032_ = v_a_2050_;
v___y_2033_ = v___y_2000_;
v___y_2034_ = v___y_2001_;
v___y_2035_ = v___y_2002_;
v___y_2036_ = v___y_2003_;
goto v___jp_2031_;
}
else
{
lean_object* v_val_2052_; lean_object* v___x_2053_; 
v_val_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_val_2052_);
lean_dec_ref(v___x_2051_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2029_, v___f_2028_, v___x_2027_, v_val_2052_, v_a_2050_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
v_candidates_2032_ = v_a_2054_;
v___y_2033_ = v___y_2000_;
v___y_2034_ = v___y_2001_;
v___y_2035_ = v___y_2002_;
v___y_2036_ = v___y_2003_;
goto v___jp_2031_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v___x_2030_);
lean_del_object(v___x_2009_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
v_a_2055_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2053_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref(v___x_2030_);
lean_del_object(v___x_2009_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
v_a_2063_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2049_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2049_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
v___jp_2031_:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_Meta_isProp(v___x_2030_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; uint8_t v___x_2039_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = lean_unbox(v_a_2038_);
lean_dec(v_a_2038_);
if (v___x_2039_ == 0)
{
v_a_2013_ = v_candidates_2032_;
goto v___jp_2012_;
}
else
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Lean_LocalDecl_hasValue(v_val_2021_, v___x_2027_);
if (v___x_2040_ == 0)
{
v___y_2023_ = v_candidates_2032_;
goto v___jp_2022_;
}
else
{
if (v___x_2027_ == 0)
{
v_a_2013_ = v_candidates_2032_;
goto v___jp_2012_;
}
else
{
v___y_2023_ = v_candidates_2032_;
goto v___jp_2022_;
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_candidates_2032_);
lean_del_object(v___x_2009_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
v_a_2041_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2037_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2037_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
else
{
v_a_2013_ = v_snd_2007_;
goto v___jp_2012_;
}
v___jp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = l_Lean_LocalDecl_fvarId(v_val_2021_);
v___x_2025_ = lean_box(0);
v___x_2026_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2023_, v___x_2024_, v___x_2025_);
v_a_2013_ = v___x_2026_;
goto v___jp_2012_;
}
}
v___jp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v_a_2013_);
lean_ctor_set(v___x_2009_, 0, v___x_2011_);
v___x_2015_ = v___x_2009_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_a_2013_);
v___x_2015_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
size_t v___x_2016_; size_t v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = ((size_t)1ULL);
v___x_2017_ = lean_usize_add(v_i_1998_, v___x_2016_);
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1996_, v_sz_1997_, v___x_2017_, v___x_2015_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2073_, lean_object* v_sz_2074_, lean_object* v_i_2075_, lean_object* v_b_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
size_t v_sz_boxed_2082_; size_t v_i_boxed_2083_; lean_object* v_res_2084_; 
v_sz_boxed_2082_ = lean_unbox_usize(v_sz_2074_);
lean_dec(v_sz_2074_);
v_i_boxed_2083_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_res_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2073_, v_sz_boxed_2082_, v_i_boxed_2083_, v_b_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec_ref(v_as_2073_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_inh_2085_, lean_object* v_n_2086_, lean_object* v_b_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
if (lean_obj_tag(v_n_2086_) == 0)
{
lean_object* v_cs_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2127_; 
v_cs_2093_ = lean_ctor_get(v_n_2086_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_n_2086_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2095_ = v_n_2086_;
v_isShared_2096_ = v_isSharedCheck_2127_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_cs_2093_);
lean_dec(v_n_2086_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2127_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; size_t v_sz_2099_; size_t v___x_2100_; lean_object* v___x_2101_; 
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_b_2087_);
v_sz_2099_ = lean_array_size(v_cs_2093_);
v___x_2100_ = ((size_t)0ULL);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_inh_2085_, v_cs_2093_, v_sz_2099_, v___x_2100_, v___x_2098_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec_ref(v_cs_2093_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2118_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2118_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2118_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_fst_2106_; 
v_fst_2106_ = lean_ctor_get(v_a_2102_, 0);
if (lean_obj_tag(v_fst_2106_) == 0)
{
lean_object* v_snd_2107_; lean_object* v___x_2109_; 
v_snd_2107_ = lean_ctor_get(v_a_2102_, 1);
lean_inc(v_snd_2107_);
lean_dec(v_a_2102_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 1);
lean_ctor_set(v___x_2095_, 0, v_snd_2107_);
v___x_2109_ = v___x_2095_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_snd_2107_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2109_);
v___x_2111_ = v___x_2104_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
else
{
lean_object* v_val_2114_; lean_object* v___x_2116_; 
lean_inc_ref(v_fst_2106_);
lean_dec(v_a_2102_);
lean_del_object(v___x_2095_);
v_val_2114_ = lean_ctor_get(v_fst_2106_, 0);
lean_inc(v_val_2114_);
lean_dec_ref(v_fst_2106_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v_val_2114_);
v___x_2116_ = v___x_2104_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_val_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_del_object(v___x_2095_);
v_a_2119_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2101_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2101_);
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
}
else
{
lean_object* v_vs_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2162_; 
v_vs_2128_ = lean_ctor_get(v_n_2086_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_n_2086_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2130_ = v_n_2086_;
v_isShared_2131_ = v_isSharedCheck_2162_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_vs_2128_);
lean_dec(v_n_2086_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2162_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; size_t v_sz_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2132_ = lean_box(0);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v_b_2087_);
v_sz_2134_ = lean_array_size(v_vs_2128_);
v___x_2135_ = ((size_t)0ULL);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2128_, v_sz_2134_, v___x_2135_, v___x_2133_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec_ref(v_vs_2128_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2153_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2153_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2153_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_fst_2141_; 
v_fst_2141_ = lean_ctor_get(v_a_2137_, 0);
if (lean_obj_tag(v_fst_2141_) == 0)
{
lean_object* v_snd_2142_; lean_object* v___x_2144_; 
v_snd_2142_ = lean_ctor_get(v_a_2137_, 1);
lean_inc(v_snd_2142_);
lean_dec(v_a_2137_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v_snd_2142_);
v___x_2144_ = v___x_2130_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_snd_2142_);
v___x_2144_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2146_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2144_);
v___x_2146_ = v___x_2139_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
else
{
lean_object* v_val_2149_; lean_object* v___x_2151_; 
lean_inc_ref(v_fst_2141_);
lean_dec(v_a_2137_);
lean_del_object(v___x_2130_);
v_val_2149_ = lean_ctor_get(v_fst_2141_, 0);
lean_inc(v_val_2149_);
lean_dec_ref(v_fst_2141_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v_val_2149_);
v___x_2151_ = v___x_2139_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_val_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_del_object(v___x_2130_);
v_a_2154_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2136_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2136_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_inh_2163_, lean_object* v_as_2164_, size_t v_sz_2165_, size_t v_i_2166_, lean_object* v_b_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_usize_dec_lt(v_i_2166_, v_sz_2165_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_b_2167_);
return v___x_2174_;
}
else
{
lean_object* v_snd_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2209_; 
v_snd_2175_ = lean_ctor_get(v_b_2167_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_b_2167_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v_b_2167_, 0);
lean_dec(v_unused_2210_);
v___x_2177_ = v_b_2167_;
v_isShared_2178_ = v_isSharedCheck_2209_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snd_2175_);
lean_dec(v_b_2167_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2209_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_array_uget_borrowed(v_as_2164_, v_i_2166_);
lean_inc(v___y_2171_);
lean_inc_ref(v___y_2170_);
lean_inc(v___y_2169_);
lean_inc_ref(v___y_2168_);
lean_inc(v_snd_2175_);
lean_inc(v_a_2179_);
v___x_2180_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_inh_2163_, v_a_2179_, v_snd_2175_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2200_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2200_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2200_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
if (lean_obj_tag(v_a_2181_) == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
v___x_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2181_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2185_);
v___x_2187_ = v___x_2177_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_snd_2175_);
v___x_2187_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2187_);
v___x_2189_ = v___x_2183_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_del_object(v___x_2183_);
lean_dec(v_snd_2175_);
v_a_2192_ = lean_ctor_get(v_a_2181_, 0);
lean_inc(v_a_2192_);
lean_dec_ref(v_a_2181_);
v___x_2193_ = lean_box(0);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v_a_2192_);
lean_ctor_set(v___x_2177_, 0, v___x_2193_);
v___x_2195_ = v___x_2177_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_a_2192_);
v___x_2195_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
size_t v___x_2196_; size_t v___x_2197_; 
v___x_2196_ = ((size_t)1ULL);
v___x_2197_ = lean_usize_add(v_i_2166_, v___x_2196_);
v_i_2166_ = v___x_2197_;
v_b_2167_ = v___x_2195_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_del_object(v___x_2177_);
lean_dec(v_snd_2175_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
v_a_2201_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2180_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2180_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_inh_2211_, lean_object* v_as_2212_, lean_object* v_sz_2213_, lean_object* v_i_2214_, lean_object* v_b_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
size_t v_sz_boxed_2221_; size_t v_i_boxed_2222_; lean_object* v_res_2223_; 
v_sz_boxed_2221_ = lean_unbox_usize(v_sz_2213_);
lean_dec(v_sz_2213_);
v_i_boxed_2222_ = lean_unbox_usize(v_i_2214_);
lean_dec(v_i_2214_);
v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_inh_2211_, v_as_2212_, v_sz_boxed_2221_, v_i_boxed_2222_, v_b_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec_ref(v_as_2212_);
lean_dec_ref(v_inh_2211_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_inh_2224_, lean_object* v_n_2225_, lean_object* v_b_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_inh_2224_, v_n_2225_, v_b_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec_ref(v_inh_2224_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2233_, lean_object* v_init_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_root_2240_; lean_object* v_tail_2241_; lean_object* v___x_2242_; 
v_root_2240_ = lean_ctor_get(v_t_2233_, 0);
lean_inc_ref(v_root_2240_);
v_tail_2241_ = lean_ctor_get(v_t_2233_, 1);
lean_inc_ref(v_tail_2241_);
lean_dec_ref(v_t_2233_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
lean_inc(v___y_2236_);
lean_inc_ref(v___y_2235_);
lean_inc_ref(v_init_2234_);
v___x_2242_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2234_, v_root_2240_, v_init_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec_ref(v_init_2234_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2279_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2279_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2279_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
if (lean_obj_tag(v_a_2243_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; 
lean_dec_ref(v_tail_2241_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
v_a_2247_ = lean_ctor_get(v_a_2243_, 0);
lean_inc(v_a_2247_);
lean_dec_ref(v_a_2243_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v_a_2247_);
v___x_2249_ = v___x_2245_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; size_t v_sz_2254_; size_t v___x_2255_; lean_object* v___x_2256_; 
lean_del_object(v___x_2245_);
v_a_2251_ = lean_ctor_get(v_a_2243_, 0);
lean_inc(v_a_2251_);
lean_dec_ref(v_a_2243_);
v___x_2252_ = lean_box(0);
v___x_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
lean_ctor_set(v___x_2253_, 1, v_a_2251_);
v_sz_2254_ = lean_array_size(v_tail_2241_);
v___x_2255_ = ((size_t)0ULL);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2241_, v_sz_2254_, v___x_2255_, v___x_2253_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec_ref(v_tail_2241_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2270_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2270_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2270_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_fst_2261_; 
v_fst_2261_ = lean_ctor_get(v_a_2257_, 0);
if (lean_obj_tag(v_fst_2261_) == 0)
{
lean_object* v_snd_2262_; lean_object* v___x_2264_; 
v_snd_2262_ = lean_ctor_get(v_a_2257_, 1);
lean_inc(v_snd_2262_);
lean_dec(v_a_2257_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v_snd_2262_);
v___x_2264_ = v___x_2259_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_snd_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
else
{
lean_object* v_val_2266_; lean_object* v___x_2268_; 
lean_inc_ref(v_fst_2261_);
lean_dec(v_a_2257_);
v_val_2266_ = lean_ctor_get(v_fst_2261_, 0);
lean_inc(v_val_2266_);
lean_dec_ref(v_fst_2261_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v_val_2266_);
v___x_2268_ = v___x_2259_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_val_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
v_a_2271_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2256_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2256_);
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
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v_tail_2241_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
v_a_2280_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2242_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2242_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2288_, lean_object* v_init_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2288_, v_init_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_buckets_2298_; lean_object* v___x_2299_; uint64_t v___x_2300_; uint64_t v___x_2301_; uint64_t v___x_2302_; uint64_t v_fold_2303_; uint64_t v___x_2304_; uint64_t v___x_2305_; uint64_t v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; size_t v___x_2310_; size_t v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v_buckets_2298_ = lean_ctor_get(v_m_2296_, 1);
v___x_2299_ = lean_array_get_size(v_buckets_2298_);
v___x_2300_ = l_Lean_instHashableFVarId_hash(v_a_2297_);
v___x_2301_ = 32ULL;
v___x_2302_ = lean_uint64_shift_right(v___x_2300_, v___x_2301_);
v_fold_2303_ = lean_uint64_xor(v___x_2300_, v___x_2302_);
v___x_2304_ = 16ULL;
v___x_2305_ = lean_uint64_shift_right(v_fold_2303_, v___x_2304_);
v___x_2306_ = lean_uint64_xor(v_fold_2303_, v___x_2305_);
v___x_2307_ = lean_uint64_to_usize(v___x_2306_);
v___x_2308_ = lean_usize_of_nat(v___x_2299_);
v___x_2309_ = ((size_t)1ULL);
v___x_2310_ = lean_usize_sub(v___x_2308_, v___x_2309_);
v___x_2311_ = lean_usize_land(v___x_2307_, v___x_2310_);
v___x_2312_ = lean_array_uget_borrowed(v_buckets_2298_, v___x_2311_);
v___x_2313_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2297_, v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2314_, lean_object* v_a_2315_){
_start:
{
uint8_t v_res_2316_; lean_object* v_r_2317_; 
v_res_2316_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2314_, v_a_2315_);
lean_dec(v_a_2315_);
lean_dec_ref(v_m_2314_);
v_r_2317_ = lean_box(v_res_2316_);
return v_r_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2318_, lean_object* v_as_2319_, size_t v_sz_2320_, size_t v_i_2321_, lean_object* v_b_2322_){
_start:
{
uint8_t v___x_2324_; 
v___x_2324_ = lean_usize_dec_lt(v_i_2321_, v_sz_2320_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_b_2322_);
return v___x_2325_;
}
else
{
lean_object* v_snd_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2344_; 
v_snd_2326_ = lean_ctor_get(v_b_2322_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_b_2322_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v_b_2322_, 0);
lean_dec(v_unused_2345_);
v___x_2328_ = v_b_2322_;
v_isShared_2329_ = v_isSharedCheck_2344_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_snd_2326_);
lean_dec(v_b_2322_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2344_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v_a_2332_; lean_object* v_a_2339_; 
v___x_2330_ = lean_box(0);
v_a_2339_ = lean_array_uget_borrowed(v_as_2319_, v_i_2321_);
if (lean_obj_tag(v_a_2339_) == 0)
{
v_a_2332_ = v_snd_2326_;
goto v___jp_2331_;
}
else
{
lean_object* v_val_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v_val_2340_ = lean_ctor_get(v_a_2339_, 0);
v___x_2341_ = l_Lean_LocalDecl_fvarId(v_val_2340_);
v___x_2342_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2318_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_dec(v___x_2341_);
v_a_2332_ = v_snd_2326_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_array_push(v_snd_2326_, v___x_2341_);
v_a_2332_ = v___x_2343_;
goto v___jp_2331_;
}
}
v___jp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v_a_2332_);
lean_ctor_set(v___x_2328_, 0, v___x_2330_);
v___x_2334_ = v___x_2328_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_a_2332_);
v___x_2334_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
size_t v___x_2335_; size_t v___x_2336_; 
v___x_2335_ = ((size_t)1ULL);
v___x_2336_ = lean_usize_add(v_i_2321_, v___x_2335_);
v_i_2321_ = v___x_2336_;
v_b_2322_ = v___x_2334_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2346_, lean_object* v_as_2347_, lean_object* v_sz_2348_, lean_object* v_i_2349_, lean_object* v_b_2350_, lean_object* v___y_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2348_);
lean_dec(v_sz_2348_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2349_);
lean_dec(v_i_2349_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2346_, v_as_2347_, v_sz_boxed_2352_, v_i_boxed_2353_, v_b_2350_);
lean_dec_ref(v_as_2347_);
lean_dec_ref(v_a_2346_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2355_, lean_object* v_as_2356_, size_t v_sz_2357_, size_t v_i_2358_, lean_object* v_b_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_usize_dec_lt(v_i_2358_, v_sz_2357_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v_b_2359_);
return v___x_2366_;
}
else
{
lean_object* v_snd_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2385_; 
v_snd_2367_ = lean_ctor_get(v_b_2359_, 1);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_b_2359_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v_b_2359_, 0);
lean_dec(v_unused_2386_);
v___x_2369_ = v_b_2359_;
v_isShared_2370_ = v_isSharedCheck_2385_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_snd_2367_);
lean_dec(v_b_2359_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2385_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v_a_2373_; lean_object* v_a_2380_; 
v___x_2371_ = lean_box(0);
v_a_2380_ = lean_array_uget_borrowed(v_as_2356_, v_i_2358_);
if (lean_obj_tag(v_a_2380_) == 0)
{
v_a_2373_ = v_snd_2367_;
goto v___jp_2372_;
}
else
{
lean_object* v_val_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; 
v_val_2381_ = lean_ctor_get(v_a_2380_, 0);
v___x_2382_ = l_Lean_LocalDecl_fvarId(v_val_2381_);
v___x_2383_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2355_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_dec(v___x_2382_);
v_a_2373_ = v_snd_2367_;
goto v___jp_2372_;
}
else
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_array_push(v_snd_2367_, v___x_2382_);
v_a_2373_ = v___x_2384_;
goto v___jp_2372_;
}
}
v___jp_2372_:
{
lean_object* v___x_2375_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 1, v_a_2373_);
lean_ctor_set(v___x_2369_, 0, v___x_2371_);
v___x_2375_ = v___x_2369_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_a_2373_);
v___x_2375_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
size_t v___x_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = ((size_t)1ULL);
v___x_2377_ = lean_usize_add(v_i_2358_, v___x_2376_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2355_, v_as_2356_, v_sz_2357_, v___x_2377_, v___x_2375_);
return v___x_2378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2387_, lean_object* v_as_2388_, lean_object* v_sz_2389_, lean_object* v_i_2390_, lean_object* v_b_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
size_t v_sz_boxed_2397_; size_t v_i_boxed_2398_; lean_object* v_res_2399_; 
v_sz_boxed_2397_ = lean_unbox_usize(v_sz_2389_);
lean_dec(v_sz_2389_);
v_i_boxed_2398_ = lean_unbox_usize(v_i_2390_);
lean_dec(v_i_2390_);
v_res_2399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2387_, v_as_2388_, v_sz_boxed_2397_, v_i_boxed_2398_, v_b_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec_ref(v_as_2388_);
lean_dec_ref(v_a_2387_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_a_2400_, lean_object* v_inh_2401_, lean_object* v_n_2402_, lean_object* v_b_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
if (lean_obj_tag(v_n_2402_) == 0)
{
lean_object* v_cs_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2443_; 
v_cs_2409_ = lean_ctor_get(v_n_2402_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_n_2402_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2411_ = v_n_2402_;
v_isShared_2412_ = v_isSharedCheck_2443_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_cs_2409_);
lean_dec(v_n_2402_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2443_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; size_t v_sz_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2413_ = lean_box(0);
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v_b_2403_);
v_sz_2415_ = lean_array_size(v_cs_2409_);
v___x_2416_ = ((size_t)0ULL);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_a_2400_, v_inh_2401_, v_cs_2409_, v_sz_2415_, v___x_2416_, v___x_2414_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref(v_cs_2409_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2434_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2434_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2434_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_fst_2422_; 
v_fst_2422_ = lean_ctor_get(v_a_2418_, 0);
if (lean_obj_tag(v_fst_2422_) == 0)
{
lean_object* v_snd_2423_; lean_object* v___x_2425_; 
v_snd_2423_ = lean_ctor_get(v_a_2418_, 1);
lean_inc(v_snd_2423_);
lean_dec(v_a_2418_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 1);
lean_ctor_set(v___x_2411_, 0, v_snd_2423_);
v___x_2425_ = v___x_2411_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_snd_2423_);
v___x_2425_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2427_; 
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2425_);
v___x_2427_ = v___x_2420_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_val_2430_; lean_object* v___x_2432_; 
lean_inc_ref(v_fst_2422_);
lean_dec(v_a_2418_);
lean_del_object(v___x_2411_);
v_val_2430_ = lean_ctor_get(v_fst_2422_, 0);
lean_inc(v_val_2430_);
lean_dec_ref(v_fst_2422_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v_val_2430_);
v___x_2432_ = v___x_2420_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_val_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_del_object(v___x_2411_);
v_a_2435_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2417_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2417_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
else
{
lean_object* v_vs_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2478_; 
v_vs_2444_ = lean_ctor_get(v_n_2402_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_n_2402_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2446_ = v_n_2402_;
v_isShared_2447_ = v_isSharedCheck_2478_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_vs_2444_);
lean_dec(v_n_2402_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2478_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; size_t v_sz_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2448_ = lean_box(0);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
lean_ctor_set(v___x_2449_, 1, v_b_2403_);
v_sz_2450_ = lean_array_size(v_vs_2444_);
v___x_2451_ = ((size_t)0ULL);
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2400_, v_vs_2444_, v_sz_2450_, v___x_2451_, v___x_2449_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref(v_vs_2444_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2469_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2469_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2469_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_fst_2457_; 
v_fst_2457_ = lean_ctor_get(v_a_2453_, 0);
if (lean_obj_tag(v_fst_2457_) == 0)
{
lean_object* v_snd_2458_; lean_object* v___x_2460_; 
v_snd_2458_ = lean_ctor_get(v_a_2453_, 1);
lean_inc(v_snd_2458_);
lean_dec(v_a_2453_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v_snd_2458_);
v___x_2460_ = v___x_2446_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_snd_2458_);
v___x_2460_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
lean_object* v___x_2462_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2460_);
v___x_2462_ = v___x_2455_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_val_2465_; lean_object* v___x_2467_; 
lean_inc_ref(v_fst_2457_);
lean_dec(v_a_2453_);
lean_del_object(v___x_2446_);
v_val_2465_ = lean_ctor_get(v_fst_2457_, 0);
lean_inc(v_val_2465_);
lean_dec_ref(v_fst_2457_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v_val_2465_);
v___x_2467_ = v___x_2455_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_val_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_del_object(v___x_2446_);
v_a_2470_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2452_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2452_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_a_2479_, lean_object* v_inh_2480_, lean_object* v_as_2481_, size_t v_sz_2482_, size_t v_i_2483_, lean_object* v_b_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_usize_dec_lt(v_i_2483_, v_sz_2482_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_b_2484_);
return v___x_2491_;
}
else
{
lean_object* v_snd_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2526_; 
v_snd_2492_ = lean_ctor_get(v_b_2484_, 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_b_2484_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v_b_2484_, 0);
lean_dec(v_unused_2527_);
v___x_2494_ = v_b_2484_;
v_isShared_2495_ = v_isSharedCheck_2526_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_snd_2492_);
lean_dec(v_b_2484_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2526_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_a_2496_; lean_object* v___x_2497_; 
v_a_2496_ = lean_array_uget_borrowed(v_as_2481_, v_i_2483_);
lean_inc(v_snd_2492_);
lean_inc(v_a_2496_);
v___x_2497_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_a_2479_, v_inh_2480_, v_a_2496_, v_snd_2492_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2517_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2517_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2517_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
if (lean_obj_tag(v_a_2498_) == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_a_2498_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2502_);
v___x_2504_ = v___x_2494_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_snd_2492_);
v___x_2504_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2506_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2504_);
v___x_2506_ = v___x_2500_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
lean_del_object(v___x_2500_);
lean_dec(v_snd_2492_);
v_a_2509_ = lean_ctor_get(v_a_2498_, 0);
lean_inc(v_a_2509_);
lean_dec_ref(v_a_2498_);
v___x_2510_ = lean_box(0);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 1, v_a_2509_);
lean_ctor_set(v___x_2494_, 0, v___x_2510_);
v___x_2512_ = v___x_2494_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_a_2509_);
v___x_2512_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
size_t v___x_2513_; size_t v___x_2514_; 
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_add(v_i_2483_, v___x_2513_);
v_i_2483_ = v___x_2514_;
v_b_2484_ = v___x_2512_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_del_object(v___x_2494_);
lean_dec(v_snd_2492_);
v_a_2518_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2497_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2497_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_a_2528_, lean_object* v_inh_2529_, lean_object* v_as_2530_, lean_object* v_sz_2531_, lean_object* v_i_2532_, lean_object* v_b_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
size_t v_sz_boxed_2539_; size_t v_i_boxed_2540_; lean_object* v_res_2541_; 
v_sz_boxed_2539_ = lean_unbox_usize(v_sz_2531_);
lean_dec(v_sz_2531_);
v_i_boxed_2540_ = lean_unbox_usize(v_i_2532_);
lean_dec(v_i_2532_);
v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_a_2528_, v_inh_2529_, v_as_2530_, v_sz_boxed_2539_, v_i_boxed_2540_, v_b_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec_ref(v_as_2530_);
lean_dec_ref(v_inh_2529_);
lean_dec_ref(v_a_2528_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_a_2542_, lean_object* v_inh_2543_, lean_object* v_n_2544_, lean_object* v_b_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_a_2542_, v_inh_2543_, v_n_2544_, v_b_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v_inh_2543_);
lean_dec_ref(v_a_2542_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2552_, lean_object* v_as_2553_, size_t v_sz_2554_, size_t v_i_2555_, lean_object* v_b_2556_){
_start:
{
uint8_t v___x_2558_; 
v___x_2558_ = lean_usize_dec_lt(v_i_2555_, v_sz_2554_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_b_2556_);
return v___x_2559_;
}
else
{
lean_object* v_snd_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2578_; 
v_snd_2560_ = lean_ctor_get(v_b_2556_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_b_2556_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; 
v_unused_2579_ = lean_ctor_get(v_b_2556_, 0);
lean_dec(v_unused_2579_);
v___x_2562_ = v_b_2556_;
v_isShared_2563_ = v_isSharedCheck_2578_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snd_2560_);
lean_dec(v_b_2556_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2578_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v_a_2566_; lean_object* v_a_2573_; 
v___x_2564_ = lean_box(0);
v_a_2573_ = lean_array_uget_borrowed(v_as_2553_, v_i_2555_);
if (lean_obj_tag(v_a_2573_) == 0)
{
v_a_2566_ = v_snd_2560_;
goto v___jp_2565_;
}
else
{
lean_object* v_val_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v_val_2574_ = lean_ctor_get(v_a_2573_, 0);
v___x_2575_ = l_Lean_LocalDecl_fvarId(v_val_2574_);
v___x_2576_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2552_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_dec(v___x_2575_);
v_a_2566_ = v_snd_2560_;
goto v___jp_2565_;
}
else
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_array_push(v_snd_2560_, v___x_2575_);
v_a_2566_ = v___x_2577_;
goto v___jp_2565_;
}
}
v___jp_2565_:
{
lean_object* v___x_2568_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v_a_2566_);
lean_ctor_set(v___x_2562_, 0, v___x_2564_);
v___x_2568_ = v___x_2562_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_a_2566_);
v___x_2568_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
size_t v___x_2569_; size_t v___x_2570_; 
v___x_2569_ = ((size_t)1ULL);
v___x_2570_ = lean_usize_add(v_i_2555_, v___x_2569_);
v_i_2555_ = v___x_2570_;
v_b_2556_ = v___x_2568_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2580_, lean_object* v_as_2581_, lean_object* v_sz_2582_, lean_object* v_i_2583_, lean_object* v_b_2584_, lean_object* v___y_2585_){
_start:
{
size_t v_sz_boxed_2586_; size_t v_i_boxed_2587_; lean_object* v_res_2588_; 
v_sz_boxed_2586_ = lean_unbox_usize(v_sz_2582_);
lean_dec(v_sz_2582_);
v_i_boxed_2587_ = lean_unbox_usize(v_i_2583_);
lean_dec(v_i_2583_);
v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2580_, v_as_2581_, v_sz_boxed_2586_, v_i_boxed_2587_, v_b_2584_);
lean_dec_ref(v_as_2581_);
lean_dec_ref(v_a_2580_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2589_, lean_object* v_as_2590_, size_t v_sz_2591_, size_t v_i_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
uint8_t v___x_2599_; 
v___x_2599_ = lean_usize_dec_lt(v_i_2592_, v_sz_2591_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v_b_2593_);
return v___x_2600_;
}
else
{
lean_object* v_snd_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2619_; 
v_snd_2601_ = lean_ctor_get(v_b_2593_, 1);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_b_2593_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; 
v_unused_2620_ = lean_ctor_get(v_b_2593_, 0);
lean_dec(v_unused_2620_);
v___x_2603_ = v_b_2593_;
v_isShared_2604_ = v_isSharedCheck_2619_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_snd_2601_);
lean_dec(v_b_2593_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2619_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v_a_2607_; lean_object* v_a_2614_; 
v___x_2605_ = lean_box(0);
v_a_2614_ = lean_array_uget_borrowed(v_as_2590_, v_i_2592_);
if (lean_obj_tag(v_a_2614_) == 0)
{
v_a_2607_ = v_snd_2601_;
goto v___jp_2606_;
}
else
{
lean_object* v_val_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v_val_2615_ = lean_ctor_get(v_a_2614_, 0);
v___x_2616_ = l_Lean_LocalDecl_fvarId(v_val_2615_);
v___x_2617_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2589_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_dec(v___x_2616_);
v_a_2607_ = v_snd_2601_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_array_push(v_snd_2601_, v___x_2616_);
v_a_2607_ = v___x_2618_;
goto v___jp_2606_;
}
}
v___jp_2606_:
{
lean_object* v___x_2609_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 1, v_a_2607_);
lean_ctor_set(v___x_2603_, 0, v___x_2605_);
v___x_2609_ = v___x_2603_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_a_2607_);
v___x_2609_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
size_t v___x_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = ((size_t)1ULL);
v___x_2611_ = lean_usize_add(v_i_2592_, v___x_2610_);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2589_, v_as_2590_, v_sz_2591_, v___x_2611_, v___x_2609_);
return v___x_2612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2621_, lean_object* v_as_2622_, lean_object* v_sz_2623_, lean_object* v_i_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
size_t v_sz_boxed_2631_; size_t v_i_boxed_2632_; lean_object* v_res_2633_; 
v_sz_boxed_2631_ = lean_unbox_usize(v_sz_2623_);
lean_dec(v_sz_2623_);
v_i_boxed_2632_ = lean_unbox_usize(v_i_2624_);
lean_dec(v_i_2624_);
v_res_2633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2621_, v_as_2622_, v_sz_boxed_2631_, v_i_boxed_2632_, v_b_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v_as_2622_);
lean_dec_ref(v_a_2621_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2634_, lean_object* v_t_2635_, lean_object* v_init_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_root_2642_; lean_object* v_tail_2643_; lean_object* v___x_2644_; 
v_root_2642_ = lean_ctor_get(v_t_2635_, 0);
lean_inc_ref(v_root_2642_);
v_tail_2643_ = lean_ctor_get(v_t_2635_, 1);
lean_inc_ref(v_tail_2643_);
lean_dec_ref(v_t_2635_);
lean_inc_ref(v_init_2636_);
v___x_2644_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_a_2634_, v_init_2636_, v_root_2642_, v_init_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec_ref(v_init_2636_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2681_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2681_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2681_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
if (lean_obj_tag(v_a_2645_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; 
lean_dec_ref(v_tail_2643_);
v_a_2649_ = lean_ctor_get(v_a_2645_, 0);
lean_inc(v_a_2649_);
lean_dec_ref(v_a_2645_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v_a_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; size_t v_sz_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
lean_del_object(v___x_2647_);
v_a_2653_ = lean_ctor_get(v_a_2645_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v_a_2645_);
v___x_2654_ = lean_box(0);
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
lean_ctor_set(v___x_2655_, 1, v_a_2653_);
v_sz_2656_ = lean_array_size(v_tail_2643_);
v___x_2657_ = ((size_t)0ULL);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2634_, v_tail_2643_, v_sz_2656_, v___x_2657_, v___x_2655_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec_ref(v_tail_2643_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2672_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_fst_2663_; 
v_fst_2663_ = lean_ctor_get(v_a_2659_, 0);
if (lean_obj_tag(v_fst_2663_) == 0)
{
lean_object* v_snd_2664_; lean_object* v___x_2666_; 
v_snd_2664_ = lean_ctor_get(v_a_2659_, 1);
lean_inc(v_snd_2664_);
lean_dec(v_a_2659_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v_snd_2664_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_snd_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
else
{
lean_object* v_val_2668_; lean_object* v___x_2670_; 
lean_inc_ref(v_fst_2663_);
lean_dec(v_a_2659_);
v_val_2668_ = lean_ctor_get(v_fst_2663_, 0);
lean_inc(v_val_2668_);
lean_dec_ref(v_fst_2663_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v_val_2668_);
v___x_2670_ = v___x_2661_;
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
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
v_a_2673_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2658_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2658_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec_ref(v_tail_2643_);
v_a_2682_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2644_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2644_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2690_, lean_object* v_t_2691_, lean_object* v_init_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2690_, v_t_2691_, v_init_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec_ref(v_a_2690_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2701_, lean_object* v_mvarId_2702_, lean_object* v___f_2703_, lean_object* v___f_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_lctx_2710_; lean_object* v_decls_2711_; lean_object* v___x_2712_; 
v_lctx_2710_ = lean_ctor_get(v___y_2705_, 2);
v_decls_2711_ = lean_ctor_get(v_lctx_2710_, 1);
lean_inc_ref(v_decls_2711_);
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc_ref(v_decls_2711_);
v___x_2712_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2711_, v_candidates_2701_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2714_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref(v___x_2712_);
v___x_2714_ = l_Lean_MVarId_getType(v_mvarId_2702_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; lean_object* v_a_2717_; lean_object* v___x_2718_; lean_object* v___y_2720_; uint8_t v___x_2744_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref(v___x_2714_);
v___x_2716_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2715_, v___y_2706_);
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref(v___x_2716_);
v___x_2718_ = lean_st_mk_ref(v_a_2713_);
v___x_2744_ = l_Lean_Expr_hasFVar(v_a_2717_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec(v_a_2717_);
lean_dec_ref(v___f_2704_);
v___x_2745_ = lean_box(0);
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___x_2718_);
v___x_2746_ = lean_apply_7(v___f_2703_, v___x_2745_, v___x_2718_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, lean_box(0));
v___y_2720_ = v___x_2746_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2748_ = 0;
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___x_2718_);
v___x_2749_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2747_, v___f_2704_, v_a_2717_, v___x_2748_, v___x_2718_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref(v___x_2749_);
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___x_2718_);
v___x_2751_ = lean_apply_7(v___f_2703_, v_a_2750_, v___x_2718_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, lean_box(0));
v___y_2720_ = v___x_2751_;
goto v___jp_2719_;
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v___x_2718_);
lean_dec_ref(v_decls_2711_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec_ref(v___f_2703_);
v_a_2752_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2749_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2749_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
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
v___jp_2719_:
{
if (lean_obj_tag(v___y_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2735_; 
v_a_2721_ = lean_ctor_get(v___y_2720_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___y_2720_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2723_ = v___y_2720_;
v_isShared_2724_ = v_isSharedCheck_2735_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___y_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2735_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v_size_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2725_ = lean_st_ref_get(v___x_2718_);
lean_dec(v___x_2718_);
lean_dec(v___x_2725_);
v_size_2726_ = lean_ctor_get(v_a_2721_, 0);
v___x_2727_ = lean_unsigned_to_nat(0u);
v___x_2728_ = lean_nat_dec_eq(v_size_2726_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_del_object(v___x_2723_);
v___x_2729_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_2730_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2721_, v_decls_2711_, v___x_2729_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v_a_2721_);
return v___x_2730_;
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
lean_dec(v_a_2721_);
lean_dec_ref(v_decls_2711_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
v___x_2731_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2731_);
v___x_2733_ = v___x_2723_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v___x_2718_);
lean_dec_ref(v_decls_2711_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
v_a_2736_ = lean_ctor_get(v___y_2720_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___y_2720_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___y_2720_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___y_2720_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_a_2713_);
lean_dec_ref(v_decls_2711_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec_ref(v___f_2704_);
lean_dec_ref(v___f_2703_);
v_a_2760_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2714_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2714_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v_decls_2711_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec_ref(v___f_2704_);
lean_dec_ref(v___f_2703_);
lean_dec(v_mvarId_2702_);
v_a_2768_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2712_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2712_);
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
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2776_, lean_object* v_mvarId_2777_, lean_object* v___f_2778_, lean_object* v___f_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2776_, v_mvarId_2777_, v___f_2778_, v___f_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___f_2794_; lean_object* v___f_2795_; lean_object* v_candidates_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; 
v___f_2794_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2795_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2796_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2788_);
v___f_2797_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2797_, 0, v_candidates_2796_);
lean_closure_set(v___f_2797_, 1, v_mvarId_2788_);
lean_closure_set(v___f_2797_, 2, v___f_2795_);
lean_closure_set(v___f_2797_, 3, v___f_2794_);
v___x_2798_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2788_, v___f_2797_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2806_, lean_object* v_m_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2807_, v_a_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2810_, lean_object* v_m_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2810_, v_m_2811_, v_a_2812_);
lean_dec(v_a_2812_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2814_, lean_object* v_m_2815_, lean_object* v_a_2816_, lean_object* v_b_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2815_, v_a_2816_, v_b_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2819_, lean_object* v_m_2820_, lean_object* v_a_2821_){
_start:
{
uint8_t v___x_2822_; 
v___x_2822_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2820_, v_a_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2823_, lean_object* v_m_2824_, lean_object* v_a_2825_){
_start:
{
uint8_t v_res_2826_; lean_object* v_r_2827_; 
v_res_2826_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2823_, v_m_2824_, v_a_2825_);
lean_dec(v_a_2825_);
lean_dec_ref(v_m_2824_);
v_r_2827_ = lean_box(v_res_2826_);
return v_r_2827_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2828_, lean_object* v_a_2829_, lean_object* v_x_2830_){
_start:
{
uint8_t v___x_2831_; 
v___x_2831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2829_, v_x_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2832_, lean_object* v_a_2833_, lean_object* v_x_2834_){
_start:
{
uint8_t v_res_2835_; lean_object* v_r_2836_; 
v_res_2835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2832_, v_a_2833_, v_x_2834_);
lean_dec(v_x_2834_);
lean_dec(v_a_2833_);
v_r_2836_ = lean_box(v_res_2835_);
return v_r_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2837_, lean_object* v_a_2838_, lean_object* v_x_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2838_, v_x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2841_, lean_object* v_a_2842_, lean_object* v_x_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2841_, v_a_2842_, v_x_2843_);
lean_dec(v_a_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2845_, lean_object* v_a_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2845_, v_a_2846_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2854_, lean_object* v_a_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2854_, v_a_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec(v_a_2855_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2863_, lean_object* v_data_2864_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2866_, lean_object* v_a_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2866_, v_a_2867_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2875_, lean_object* v_a_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2875_, v_a_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v_a_2876_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2884_, lean_object* v_i_2885_, lean_object* v_source_2886_, lean_object* v_target_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2885_, v_source_2886_, v_target_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2889_, lean_object* v_as_2890_, size_t v_sz_2891_, size_t v_i_2892_, lean_object* v_b_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2889_, v_as_2890_, v_sz_2891_, v_i_2892_, v_b_2893_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2900_, lean_object* v_as_2901_, lean_object* v_sz_2902_, lean_object* v_i_2903_, lean_object* v_b_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
size_t v_sz_boxed_2910_; size_t v_i_boxed_2911_; lean_object* v_res_2912_; 
v_sz_boxed_2910_ = lean_unbox_usize(v_sz_2902_);
lean_dec(v_sz_2902_);
v_i_boxed_2911_ = lean_unbox_usize(v_i_2903_);
lean_dec(v_i_2903_);
v_res_2912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2900_, v_as_2901_, v_sz_boxed_2910_, v_i_boxed_2911_, v_b_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec_ref(v_as_2901_);
lean_dec_ref(v_a_2900_);
return v_res_2912_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2913_, lean_object* v_m_2914_, lean_object* v_a_2915_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2914_, v_a_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2917_, lean_object* v_m_2918_, lean_object* v_a_2919_){
_start:
{
uint8_t v_res_2920_; lean_object* v_r_2921_; 
v_res_2920_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2917_, v_m_2918_, v_a_2919_);
lean_dec_ref(v_a_2919_);
lean_dec_ref(v_m_2918_);
v_r_2921_ = lean_box(v_res_2920_);
return v_r_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2922_, lean_object* v_m_2923_, lean_object* v_a_2924_, lean_object* v_b_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2923_, v_a_2924_, v_b_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2928_, v_x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2931_, lean_object* v_as_2932_, size_t v_sz_2933_, size_t v_i_2934_, lean_object* v_b_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2931_, v_as_2932_, v_sz_2933_, v_i_2934_, v_b_2935_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_2942_, lean_object* v_as_2943_, lean_object* v_sz_2944_, lean_object* v_i_2945_, lean_object* v_b_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
size_t v_sz_boxed_2952_; size_t v_i_boxed_2953_; lean_object* v_res_2954_; 
v_sz_boxed_2952_ = lean_unbox_usize(v_sz_2944_);
lean_dec(v_sz_2944_);
v_i_boxed_2953_ = lean_unbox_usize(v_i_2945_);
lean_dec(v_i_2945_);
v_res_2954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2942_, v_as_2943_, v_sz_boxed_2952_, v_i_boxed_2953_, v_b_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec_ref(v_as_2943_);
lean_dec_ref(v_a_2942_);
return v_res_2954_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_2955_, lean_object* v_a_2956_, lean_object* v_x_2957_){
_start:
{
uint8_t v___x_2958_; 
v___x_2958_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_2956_, v_x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2959_, lean_object* v_a_2960_, lean_object* v_x_2961_){
_start:
{
uint8_t v_res_2962_; lean_object* v_r_2963_; 
v_res_2962_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_2959_, v_a_2960_, v_x_2961_);
lean_dec(v_x_2961_);
lean_dec_ref(v_a_2960_);
v_r_2963_ = lean_box(v_res_2962_);
return v_r_2963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_2964_, lean_object* v_data_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_2967_, lean_object* v_i_2968_, lean_object* v_source_2969_, lean_object* v_target_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_2968_, v_source_2969_, v_target_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_2973_, v_x_2974_);
return v___x_2975_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = l_Lean_maxRecDepthErrorMessage;
v___x_2982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
return v___x_2982_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_2984_ = l_Lean_MessageData_ofFormat(v___x_2983_);
return v___x_2984_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_2986_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_2987_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v___x_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_2988_){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2991_, 0, v_ref_2988_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2993_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_2996_, lean_object* v_ref_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2997_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_3005_, lean_object* v_ref_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_3005_, v_ref_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_3014_, lean_object* v_mvarId_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v_fileName_3022_; lean_object* v_fileMap_3023_; lean_object* v_options_3024_; lean_object* v_currRecDepth_3025_; lean_object* v_maxRecDepth_3026_; lean_object* v_ref_3027_; lean_object* v_currNamespace_3028_; lean_object* v_openDecls_3029_; lean_object* v_initHeartbeats_3030_; lean_object* v_maxHeartbeats_3031_; lean_object* v_quotContext_3032_; lean_object* v_currMacroScope_3033_; uint8_t v_diag_3034_; lean_object* v_cancelTk_x3f_3035_; uint8_t v_suppressElabErrors_3036_; lean_object* v_inheritedTraceOptions_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3071_; 
v_fileName_3022_ = lean_ctor_get(v_a_3019_, 0);
v_fileMap_3023_ = lean_ctor_get(v_a_3019_, 1);
v_options_3024_ = lean_ctor_get(v_a_3019_, 2);
v_currRecDepth_3025_ = lean_ctor_get(v_a_3019_, 3);
v_maxRecDepth_3026_ = lean_ctor_get(v_a_3019_, 4);
v_ref_3027_ = lean_ctor_get(v_a_3019_, 5);
v_currNamespace_3028_ = lean_ctor_get(v_a_3019_, 6);
v_openDecls_3029_ = lean_ctor_get(v_a_3019_, 7);
v_initHeartbeats_3030_ = lean_ctor_get(v_a_3019_, 8);
v_maxHeartbeats_3031_ = lean_ctor_get(v_a_3019_, 9);
v_quotContext_3032_ = lean_ctor_get(v_a_3019_, 10);
v_currMacroScope_3033_ = lean_ctor_get(v_a_3019_, 11);
v_diag_3034_ = lean_ctor_get_uint8(v_a_3019_, sizeof(void*)*14);
v_cancelTk_x3f_3035_ = lean_ctor_get(v_a_3019_, 12);
v_suppressElabErrors_3036_ = lean_ctor_get_uint8(v_a_3019_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3037_ = lean_ctor_get(v_a_3019_, 13);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_a_3019_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3039_ = v_a_3019_;
v_isShared_3040_ = v_isSharedCheck_3071_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_inheritedTraceOptions_3037_);
lean_inc(v_cancelTk_x3f_3035_);
lean_inc(v_currMacroScope_3033_);
lean_inc(v_quotContext_3032_);
lean_inc(v_maxHeartbeats_3031_);
lean_inc(v_initHeartbeats_3030_);
lean_inc(v_openDecls_3029_);
lean_inc(v_currNamespace_3028_);
lean_inc(v_ref_3027_);
lean_inc(v_maxRecDepth_3026_);
lean_inc(v_currRecDepth_3025_);
lean_inc(v_options_3024_);
lean_inc(v_fileMap_3023_);
lean_inc(v_fileName_3022_);
lean_dec(v_a_3019_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3071_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
uint8_t v___x_3041_; 
v___x_3041_ = lean_nat_dec_eq(v_currRecDepth_3025_, v_maxRecDepth_3026_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3042_ = lean_unsigned_to_nat(1u);
v___x_3043_ = lean_nat_add(v_currRecDepth_3025_, v___x_3042_);
lean_dec(v_currRecDepth_3025_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 3, v___x_3043_);
v___x_3045_ = v___x_3039_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_fileName_3022_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_fileMap_3023_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_options_3024_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v_maxRecDepth_3026_);
lean_ctor_set(v_reuseFailAlloc_3069_, 5, v_ref_3027_);
lean_ctor_set(v_reuseFailAlloc_3069_, 6, v_currNamespace_3028_);
lean_ctor_set(v_reuseFailAlloc_3069_, 7, v_openDecls_3029_);
lean_ctor_set(v_reuseFailAlloc_3069_, 8, v_initHeartbeats_3030_);
lean_ctor_set(v_reuseFailAlloc_3069_, 9, v_maxHeartbeats_3031_);
lean_ctor_set(v_reuseFailAlloc_3069_, 10, v_quotContext_3032_);
lean_ctor_set(v_reuseFailAlloc_3069_, 11, v_currMacroScope_3033_);
lean_ctor_set(v_reuseFailAlloc_3069_, 12, v_cancelTk_x3f_3035_);
lean_ctor_set(v_reuseFailAlloc_3069_, 13, v_inheritedTraceOptions_3037_);
lean_ctor_set_uint8(v_reuseFailAlloc_3069_, sizeof(void*)*14, v_diag_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3069_, sizeof(void*)*14 + 1, v_suppressElabErrors_3036_);
v___x_3045_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3046_; 
lean_inc_ref(v_x_3014_);
lean_inc(v_a_3020_);
lean_inc_ref(v___x_3045_);
lean_inc(v_a_3018_);
lean_inc_ref(v_a_3017_);
lean_inc(v_mvarId_3015_);
v___x_3046_ = lean_apply_6(v_x_3014_, v_mvarId_3015_, v_a_3017_, v_a_3018_, v___x_3045_, v_a_3020_, lean_box(0));
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3060_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3060_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3060_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
if (lean_obj_tag(v_a_3047_) == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
lean_dec_ref(v___x_3045_);
lean_dec(v_a_3020_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec_ref(v_x_3014_);
v___x_3051_ = lean_st_ref_take(v_a_3016_);
v___x_3052_ = lean_array_push(v___x_3051_, v_mvarId_3015_);
v___x_3053_ = lean_st_ref_set(v_a_3016_, v___x_3052_);
v___x_3054_ = lean_box(0);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3054_);
v___x_3056_ = v___x_3049_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
else
{
lean_object* v_val_3058_; lean_object* v___x_3059_; 
lean_del_object(v___x_3049_);
lean_dec(v_mvarId_3015_);
v_val_3058_ = lean_ctor_get(v_a_3047_, 0);
lean_inc(v_val_3058_);
lean_dec_ref(v_a_3047_);
v___x_3059_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3014_, v_val_3058_, v_a_3016_, v_a_3017_, v_a_3018_, v___x_3045_, v_a_3020_);
return v___x_3059_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v___x_3045_);
lean_dec(v_a_3020_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_mvarId_3015_);
lean_dec_ref(v_x_3014_);
v_a_3061_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3046_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3046_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
else
{
lean_object* v___x_3070_; 
lean_del_object(v___x_3039_);
lean_dec_ref(v_inheritedTraceOptions_3037_);
lean_dec(v_cancelTk_x3f_3035_);
lean_dec(v_currMacroScope_3033_);
lean_dec(v_quotContext_3032_);
lean_dec(v_maxHeartbeats_3031_);
lean_dec(v_initHeartbeats_3030_);
lean_dec(v_openDecls_3029_);
lean_dec(v_currNamespace_3028_);
lean_dec(v_maxRecDepth_3026_);
lean_dec(v_currRecDepth_3025_);
lean_dec_ref(v_options_3024_);
lean_dec_ref(v_fileMap_3023_);
lean_dec_ref(v_fileName_3022_);
lean_dec(v_a_3020_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_mvarId_3015_);
lean_dec_ref(v_x_3014_);
v___x_3070_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3027_);
return v___x_3070_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3072_, lean_object* v_as_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
if (lean_obj_tag(v_as_3073_) == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec_ref(v_x_3072_);
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
return v___x_3081_;
}
else
{
lean_object* v_head_3082_; lean_object* v_tail_3083_; lean_object* v___x_3084_; 
v_head_3082_ = lean_ctor_get(v_as_3073_, 0);
lean_inc(v_head_3082_);
v_tail_3083_ = lean_ctor_get(v_as_3073_, 1);
lean_inc(v_tail_3083_);
lean_dec_ref(v_as_3073_);
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
lean_inc_ref(v_x_3072_);
v___x_3084_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3072_, v_head_3082_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_dec_ref(v___x_3084_);
v_as_3073_ = v_tail_3083_;
goto _start;
}
else
{
lean_dec(v_tail_3083_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec_ref(v_x_3072_);
return v___x_3084_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3086_, lean_object* v_as_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3086_, v_as_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
lean_dec(v___y_3088_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3095_, lean_object* v_mvarId_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3095_, v_mvarId_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
lean_dec(v_a_3097_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3104_, lean_object* v_x_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3112_ = lean_st_mk_ref(v___x_3111_);
v___x_3113_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3105_, v_mvarId_3104_, v___x_3112_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3122_; 
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; 
v_unused_3123_ = lean_ctor_get(v___x_3113_, 0);
lean_dec(v_unused_3123_);
v___x_3115_ = v___x_3113_;
v_isShared_3116_ = v_isSharedCheck_3122_;
goto v_resetjp_3114_;
}
else
{
lean_dec(v___x_3113_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3122_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3117_ = lean_st_ref_get(v___x_3112_);
lean_dec(v___x_3112_);
v___x_3118_ = lean_array_to_list(v___x_3117_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3118_);
v___x_3120_ = v___x_3115_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec(v___x_3112_);
v_a_3124_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3113_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3113_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3132_, lean_object* v_x_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Meta_saturate(v_mvarId_3132_, v_x_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3140_, lean_object* v_msg_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
if (lean_obj_tag(v_mvarIds_3140_) == 1)
{
lean_object* v_tail_3147_; 
v_tail_3147_ = lean_ctor_get(v_mvarIds_3140_, 1);
if (lean_obj_tag(v_tail_3147_) == 0)
{
lean_object* v_head_3148_; lean_object* v___x_3149_; 
lean_dec_ref(v_msg_3141_);
v_head_3148_ = lean_ctor_get(v_mvarIds_3140_, 0);
lean_inc(v_head_3148_);
v___x_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3149_, 0, v_head_3148_);
return v___x_3149_;
}
else
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
return v___x_3150_;
}
}
else
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3152_, lean_object* v_msg_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_Meta_exactlyOne(v_mvarIds_3152_, v_msg_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_mvarIds_3152_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3160_, lean_object* v_msg_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
if (lean_obj_tag(v_mvarIds_3160_) == 0)
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_dec_ref(v_msg_3161_);
v___x_3167_ = lean_box(0);
v___x_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
return v___x_3168_;
}
else
{
lean_object* v_tail_3169_; 
v_tail_3169_ = lean_ctor_get(v_mvarIds_3160_, 1);
if (lean_obj_tag(v_tail_3169_) == 0)
{
lean_object* v_head_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_dec_ref(v_msg_3161_);
v_head_3170_ = lean_ctor_get(v_mvarIds_3160_, 0);
lean_inc(v_head_3170_);
v___x_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3171_, 0, v_head_3170_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
else
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3174_, lean_object* v_msg_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3174_, v_msg_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_mvarIds_3174_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3182_, size_t v_sz_3183_, size_t v_i_3184_, lean_object* v_b_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v___x_3191_; 
v___x_3191_ = lean_usize_dec_lt(v_i_3184_, v_sz_3183_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; 
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v_b_3185_);
return v___x_3192_;
}
else
{
lean_object* v_snd_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3223_; 
v_snd_3193_ = lean_ctor_get(v_b_3185_, 1);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_b_3185_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; 
v_unused_3224_ = lean_ctor_get(v_b_3185_, 0);
lean_dec(v_unused_3224_);
v___x_3195_ = v_b_3185_;
v_isShared_3196_ = v_isSharedCheck_3223_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_snd_3193_);
lean_dec(v_b_3185_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3223_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v_a_3199_; lean_object* v_a_3206_; 
v___x_3197_ = lean_box(0);
v_a_3206_ = lean_array_uget_borrowed(v_as_3182_, v_i_3184_);
if (lean_obj_tag(v_a_3206_) == 0)
{
v_a_3199_ = v_snd_3193_;
goto v___jp_3198_;
}
else
{
lean_object* v_val_3207_; uint8_t v___x_3208_; 
v_val_3207_ = lean_ctor_get(v_a_3206_, 0);
v___x_3208_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = l_Lean_LocalDecl_type(v_val_3207_);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
v___x_3210_ = l_Lean_Meta_isProp(v___x_3209_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; uint8_t v___x_3212_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref(v___x_3210_);
v___x_3212_ = lean_unbox(v_a_3211_);
lean_dec(v_a_3211_);
if (v___x_3212_ == 0)
{
v_a_3199_ = v_snd_3193_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = l_Lean_LocalDecl_fvarId(v_val_3207_);
v___x_3214_ = lean_array_push(v_snd_3193_, v___x_3213_);
v_a_3199_ = v___x_3214_;
goto v___jp_3198_;
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_del_object(v___x_3195_);
lean_dec(v_snd_3193_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
v_a_3215_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3210_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3210_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
v_a_3199_ = v_snd_3193_;
goto v___jp_3198_;
}
}
v___jp_3198_:
{
lean_object* v___x_3201_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 1, v_a_3199_);
lean_ctor_set(v___x_3195_, 0, v___x_3197_);
v___x_3201_ = v___x_3195_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_a_3199_);
v___x_3201_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
size_t v___x_3202_; size_t v___x_3203_; 
v___x_3202_ = ((size_t)1ULL);
v___x_3203_ = lean_usize_add(v_i_3184_, v___x_3202_);
v_i_3184_ = v___x_3203_;
v_b_3185_ = v___x_3201_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3225_, lean_object* v_sz_3226_, lean_object* v_i_3227_, lean_object* v_b_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
size_t v_sz_boxed_3234_; size_t v_i_boxed_3235_; lean_object* v_res_3236_; 
v_sz_boxed_3234_ = lean_unbox_usize(v_sz_3226_);
lean_dec(v_sz_3226_);
v_i_boxed_3235_ = lean_unbox_usize(v_i_3227_);
lean_dec(v_i_3227_);
v_res_3236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3225_, v_sz_boxed_3234_, v_i_boxed_3235_, v_b_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec_ref(v_as_3225_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3237_, size_t v_sz_3238_, size_t v_i_3239_, lean_object* v_b_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
uint8_t v___x_3246_; 
v___x_3246_ = lean_usize_dec_lt(v_i_3239_, v_sz_3238_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; 
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_b_3240_);
return v___x_3247_;
}
else
{
lean_object* v_snd_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3278_; 
v_snd_3248_ = lean_ctor_get(v_b_3240_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_b_3240_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; 
v_unused_3279_ = lean_ctor_get(v_b_3240_, 0);
lean_dec(v_unused_3279_);
v___x_3250_ = v_b_3240_;
v_isShared_3251_ = v_isSharedCheck_3278_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_snd_3248_);
lean_dec(v_b_3240_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3278_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3252_; lean_object* v_a_3254_; lean_object* v_a_3261_; 
v___x_3252_ = lean_box(0);
v_a_3261_ = lean_array_uget_borrowed(v_as_3237_, v_i_3239_);
if (lean_obj_tag(v_a_3261_) == 0)
{
v_a_3254_ = v_snd_3248_;
goto v___jp_3253_;
}
else
{
lean_object* v_val_3262_; uint8_t v___x_3263_; 
v_val_3262_ = lean_ctor_get(v_a_3261_, 0);
v___x_3263_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3262_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = l_Lean_LocalDecl_type(v_val_3262_);
lean_inc(v___y_3244_);
lean_inc_ref(v___y_3243_);
lean_inc(v___y_3242_);
lean_inc_ref(v___y_3241_);
v___x_3265_ = l_Lean_Meta_isProp(v___x_3264_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; uint8_t v___x_3267_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref(v___x_3265_);
v___x_3267_ = lean_unbox(v_a_3266_);
lean_dec(v_a_3266_);
if (v___x_3267_ == 0)
{
v_a_3254_ = v_snd_3248_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = l_Lean_LocalDecl_fvarId(v_val_3262_);
v___x_3269_ = lean_array_push(v_snd_3248_, v___x_3268_);
v_a_3254_ = v___x_3269_;
goto v___jp_3253_;
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_del_object(v___x_3250_);
lean_dec(v_snd_3248_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
v_a_3270_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3265_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3265_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
v_a_3254_ = v_snd_3248_;
goto v___jp_3253_;
}
}
v___jp_3253_:
{
lean_object* v___x_3256_; 
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 1, v_a_3254_);
lean_ctor_set(v___x_3250_, 0, v___x_3252_);
v___x_3256_ = v___x_3250_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_a_3254_);
v___x_3256_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
size_t v___x_3257_; size_t v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = ((size_t)1ULL);
v___x_3258_ = lean_usize_add(v_i_3239_, v___x_3257_);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3237_, v_sz_3238_, v___x_3258_, v___x_3256_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
return v___x_3259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3280_, lean_object* v_sz_3281_, lean_object* v_i_3282_, lean_object* v_b_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
size_t v_sz_boxed_3289_; size_t v_i_boxed_3290_; lean_object* v_res_3291_; 
v_sz_boxed_3289_ = lean_unbox_usize(v_sz_3281_);
lean_dec(v_sz_3281_);
v_i_boxed_3290_ = lean_unbox_usize(v_i_3282_);
lean_dec(v_i_3282_);
v_res_3291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3280_, v_sz_boxed_3289_, v_i_boxed_3290_, v_b_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec_ref(v_as_3280_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_inh_3292_, lean_object* v_n_3293_, lean_object* v_b_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
if (lean_obj_tag(v_n_3293_) == 0)
{
lean_object* v_cs_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3334_; 
v_cs_3300_ = lean_ctor_get(v_n_3293_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_n_3293_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3302_ = v_n_3293_;
v_isShared_3303_ = v_isSharedCheck_3334_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_cs_3300_);
lean_dec(v_n_3293_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3334_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; size_t v_sz_3306_; size_t v___x_3307_; lean_object* v___x_3308_; 
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v_b_3294_);
v_sz_3306_ = lean_array_size(v_cs_3300_);
v___x_3307_ = ((size_t)0ULL);
v___x_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_inh_3292_, v_cs_3300_, v_sz_3306_, v___x_3307_, v___x_3305_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec_ref(v_cs_3300_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3325_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3325_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3325_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v_fst_3313_; 
v_fst_3313_ = lean_ctor_get(v_a_3309_, 0);
if (lean_obj_tag(v_fst_3313_) == 0)
{
lean_object* v_snd_3314_; lean_object* v___x_3316_; 
v_snd_3314_ = lean_ctor_get(v_a_3309_, 1);
lean_inc(v_snd_3314_);
lean_dec(v_a_3309_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set_tag(v___x_3302_, 1);
lean_ctor_set(v___x_3302_, 0, v_snd_3314_);
v___x_3316_ = v___x_3302_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_snd_3314_);
v___x_3316_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3318_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3316_);
v___x_3318_ = v___x_3311_;
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
lean_object* v_val_3321_; lean_object* v___x_3323_; 
lean_inc_ref(v_fst_3313_);
lean_dec(v_a_3309_);
lean_del_object(v___x_3302_);
v_val_3321_ = lean_ctor_get(v_fst_3313_, 0);
lean_inc(v_val_3321_);
lean_dec_ref(v_fst_3313_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v_val_3321_);
v___x_3323_ = v___x_3311_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_val_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_del_object(v___x_3302_);
v_a_3326_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3308_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3308_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
}
else
{
lean_object* v_vs_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3369_; 
v_vs_3335_ = lean_ctor_get(v_n_3293_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_n_3293_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3337_ = v_n_3293_;
v_isShared_3338_ = v_isSharedCheck_3369_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_vs_3335_);
lean_dec(v_n_3293_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3369_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; size_t v_sz_3341_; size_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3339_ = lean_box(0);
v___x_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
lean_ctor_set(v___x_3340_, 1, v_b_3294_);
v_sz_3341_ = lean_array_size(v_vs_3335_);
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3335_, v_sz_3341_, v___x_3342_, v___x_3340_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec_ref(v_vs_3335_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3360_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3360_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3360_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_fst_3348_; 
v_fst_3348_ = lean_ctor_get(v_a_3344_, 0);
if (lean_obj_tag(v_fst_3348_) == 0)
{
lean_object* v_snd_3349_; lean_object* v___x_3351_; 
v_snd_3349_ = lean_ctor_get(v_a_3344_, 1);
lean_inc(v_snd_3349_);
lean_dec(v_a_3344_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v_snd_3349_);
v___x_3351_ = v___x_3337_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_snd_3349_);
v___x_3351_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3353_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3351_);
v___x_3353_ = v___x_3346_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
else
{
lean_object* v_val_3356_; lean_object* v___x_3358_; 
lean_inc_ref(v_fst_3348_);
lean_dec(v_a_3344_);
lean_del_object(v___x_3337_);
v_val_3356_ = lean_ctor_get(v_fst_3348_, 0);
lean_inc(v_val_3356_);
lean_dec_ref(v_fst_3348_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v_val_3356_);
v___x_3358_ = v___x_3346_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_val_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_del_object(v___x_3337_);
v_a_3361_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3343_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3343_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_inh_3370_, lean_object* v_as_3371_, size_t v_sz_3372_, size_t v_i_3373_, lean_object* v_b_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_usize_dec_lt(v_i_3373_, v_sz_3372_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_b_3374_);
return v___x_3381_;
}
else
{
lean_object* v_snd_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3416_; 
v_snd_3382_ = lean_ctor_get(v_b_3374_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_b_3374_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; 
v_unused_3417_ = lean_ctor_get(v_b_3374_, 0);
lean_dec(v_unused_3417_);
v___x_3384_ = v_b_3374_;
v_isShared_3385_ = v_isSharedCheck_3416_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_snd_3382_);
lean_dec(v_b_3374_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3416_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_array_uget_borrowed(v_as_3371_, v_i_3373_);
lean_inc(v___y_3378_);
lean_inc_ref(v___y_3377_);
lean_inc(v___y_3376_);
lean_inc_ref(v___y_3375_);
lean_inc(v_snd_3382_);
lean_inc(v_a_3386_);
v___x_3387_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_inh_3370_, v_a_3386_, v_snd_3382_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3407_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3407_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3407_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
if (lean_obj_tag(v_a_3388_) == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
v___x_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3392_, 0, v_a_3388_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3392_);
v___x_3394_ = v___x_3384_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_snd_3382_);
v___x_3394_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3396_; 
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3394_);
v___x_3396_ = v___x_3390_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
lean_del_object(v___x_3390_);
lean_dec(v_snd_3382_);
v_a_3399_ = lean_ctor_get(v_a_3388_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v_a_3388_);
v___x_3400_ = lean_box(0);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 1, v_a_3399_);
lean_ctor_set(v___x_3384_, 0, v___x_3400_);
v___x_3402_ = v___x_3384_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_a_3399_);
v___x_3402_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
size_t v___x_3403_; size_t v___x_3404_; 
v___x_3403_ = ((size_t)1ULL);
v___x_3404_ = lean_usize_add(v_i_3373_, v___x_3403_);
v_i_3373_ = v___x_3404_;
v_b_3374_ = v___x_3402_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_del_object(v___x_3384_);
lean_dec(v_snd_3382_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
v_a_3408_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3387_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3387_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_inh_3418_, lean_object* v_as_3419_, lean_object* v_sz_3420_, lean_object* v_i_3421_, lean_object* v_b_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
size_t v_sz_boxed_3428_; size_t v_i_boxed_3429_; lean_object* v_res_3430_; 
v_sz_boxed_3428_ = lean_unbox_usize(v_sz_3420_);
lean_dec(v_sz_3420_);
v_i_boxed_3429_ = lean_unbox_usize(v_i_3421_);
lean_dec(v_i_3421_);
v_res_3430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_inh_3418_, v_as_3419_, v_sz_boxed_3428_, v_i_boxed_3429_, v_b_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v_as_3419_);
lean_dec_ref(v_inh_3418_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_inh_3431_, lean_object* v_n_3432_, lean_object* v_b_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_inh_3431_, v_n_3432_, v_b_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec_ref(v_inh_3431_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3440_, size_t v_sz_3441_, size_t v_i_3442_, lean_object* v_b_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
uint8_t v___x_3449_; 
v___x_3449_ = lean_usize_dec_lt(v_i_3442_, v_sz_3441_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; 
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v_b_3443_);
return v___x_3450_;
}
else
{
lean_object* v_snd_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3481_; 
v_snd_3451_ = lean_ctor_get(v_b_3443_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_b_3443_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; 
v_unused_3482_ = lean_ctor_get(v_b_3443_, 0);
lean_dec(v_unused_3482_);
v___x_3453_ = v_b_3443_;
v_isShared_3454_ = v_isSharedCheck_3481_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_snd_3451_);
lean_dec(v_b_3443_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3481_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v_a_3457_; lean_object* v_a_3464_; 
v___x_3455_ = lean_box(0);
v_a_3464_ = lean_array_uget_borrowed(v_as_3440_, v_i_3442_);
if (lean_obj_tag(v_a_3464_) == 0)
{
v_a_3457_ = v_snd_3451_;
goto v___jp_3456_;
}
else
{
lean_object* v_val_3465_; uint8_t v___x_3466_; 
v_val_3465_ = lean_ctor_get(v_a_3464_, 0);
v___x_3466_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = l_Lean_LocalDecl_type(v_val_3465_);
lean_inc(v___y_3447_);
lean_inc_ref(v___y_3446_);
lean_inc(v___y_3445_);
lean_inc_ref(v___y_3444_);
v___x_3468_ = l_Lean_Meta_isProp(v___x_3467_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; uint8_t v___x_3470_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3469_);
lean_dec_ref(v___x_3468_);
v___x_3470_ = lean_unbox(v_a_3469_);
lean_dec(v_a_3469_);
if (v___x_3470_ == 0)
{
v_a_3457_ = v_snd_3451_;
goto v___jp_3456_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = l_Lean_LocalDecl_fvarId(v_val_3465_);
v___x_3472_ = lean_array_push(v_snd_3451_, v___x_3471_);
v_a_3457_ = v___x_3472_;
goto v___jp_3456_;
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_del_object(v___x_3453_);
lean_dec(v_snd_3451_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
v_a_3473_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3468_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3468_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
v_a_3457_ = v_snd_3451_;
goto v___jp_3456_;
}
}
v___jp_3456_:
{
lean_object* v___x_3459_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v_a_3457_);
lean_ctor_set(v___x_3453_, 0, v___x_3455_);
v___x_3459_ = v___x_3453_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_a_3457_);
v___x_3459_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
size_t v___x_3460_; size_t v___x_3461_; 
v___x_3460_ = ((size_t)1ULL);
v___x_3461_ = lean_usize_add(v_i_3442_, v___x_3460_);
v_i_3442_ = v___x_3461_;
v_b_3443_ = v___x_3459_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3483_, lean_object* v_sz_3484_, lean_object* v_i_3485_, lean_object* v_b_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
size_t v_sz_boxed_3492_; size_t v_i_boxed_3493_; lean_object* v_res_3494_; 
v_sz_boxed_3492_ = lean_unbox_usize(v_sz_3484_);
lean_dec(v_sz_3484_);
v_i_boxed_3493_ = lean_unbox_usize(v_i_3485_);
lean_dec(v_i_3485_);
v_res_3494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3483_, v_sz_boxed_3492_, v_i_boxed_3493_, v_b_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec_ref(v_as_3483_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3495_, size_t v_sz_3496_, size_t v_i_3497_, lean_object* v_b_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
uint8_t v___x_3504_; 
v___x_3504_ = lean_usize_dec_lt(v_i_3497_, v_sz_3496_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v_b_3498_);
return v___x_3505_;
}
else
{
lean_object* v_snd_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3536_; 
v_snd_3506_ = lean_ctor_get(v_b_3498_, 1);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_b_3498_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; 
v_unused_3537_ = lean_ctor_get(v_b_3498_, 0);
lean_dec(v_unused_3537_);
v___x_3508_ = v_b_3498_;
v_isShared_3509_ = v_isSharedCheck_3536_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_snd_3506_);
lean_dec(v_b_3498_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3536_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v_a_3512_; lean_object* v_a_3519_; 
v___x_3510_ = lean_box(0);
v_a_3519_ = lean_array_uget_borrowed(v_as_3495_, v_i_3497_);
if (lean_obj_tag(v_a_3519_) == 0)
{
v_a_3512_ = v_snd_3506_;
goto v___jp_3511_;
}
else
{
lean_object* v_val_3520_; uint8_t v___x_3521_; 
v_val_3520_ = lean_ctor_get(v_a_3519_, 0);
v___x_3521_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3520_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = l_Lean_LocalDecl_type(v_val_3520_);
lean_inc(v___y_3502_);
lean_inc_ref(v___y_3501_);
lean_inc(v___y_3500_);
lean_inc_ref(v___y_3499_);
v___x_3523_ = l_Lean_Meta_isProp(v___x_3522_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; uint8_t v___x_3525_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref(v___x_3523_);
v___x_3525_ = lean_unbox(v_a_3524_);
lean_dec(v_a_3524_);
if (v___x_3525_ == 0)
{
v_a_3512_ = v_snd_3506_;
goto v___jp_3511_;
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = l_Lean_LocalDecl_fvarId(v_val_3520_);
v___x_3527_ = lean_array_push(v_snd_3506_, v___x_3526_);
v_a_3512_ = v___x_3527_;
goto v___jp_3511_;
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_del_object(v___x_3508_);
lean_dec(v_snd_3506_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
v_a_3528_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3523_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3523_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
v_a_3512_ = v_snd_3506_;
goto v___jp_3511_;
}
}
v___jp_3511_:
{
lean_object* v___x_3514_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v_a_3512_);
lean_ctor_set(v___x_3508_, 0, v___x_3510_);
v___x_3514_ = v___x_3508_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_a_3512_);
v___x_3514_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
size_t v___x_3515_; size_t v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = ((size_t)1ULL);
v___x_3516_ = lean_usize_add(v_i_3497_, v___x_3515_);
v___x_3517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3495_, v_sz_3496_, v___x_3516_, v___x_3514_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
return v___x_3517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3538_, lean_object* v_sz_3539_, lean_object* v_i_3540_, lean_object* v_b_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
size_t v_sz_boxed_3547_; size_t v_i_boxed_3548_; lean_object* v_res_3549_; 
v_sz_boxed_3547_ = lean_unbox_usize(v_sz_3539_);
lean_dec(v_sz_3539_);
v_i_boxed_3548_ = lean_unbox_usize(v_i_3540_);
lean_dec(v_i_3540_);
v_res_3549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3538_, v_sz_boxed_3547_, v_i_boxed_3548_, v_b_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec_ref(v_as_3538_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3550_, lean_object* v_init_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_root_3557_; lean_object* v_tail_3558_; lean_object* v___x_3559_; 
v_root_3557_ = lean_ctor_get(v_t_3550_, 0);
lean_inc_ref(v_root_3557_);
v_tail_3558_ = lean_ctor_get(v_t_3550_, 1);
lean_inc_ref(v_tail_3558_);
lean_dec_ref(v_t_3550_);
lean_inc(v___y_3555_);
lean_inc_ref(v___y_3554_);
lean_inc(v___y_3553_);
lean_inc_ref(v___y_3552_);
lean_inc_ref(v_init_3551_);
v___x_3559_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3551_, v_root_3557_, v_init_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec_ref(v_init_3551_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3596_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3562_ = v___x_3559_;
v_isShared_3563_ = v_isSharedCheck_3596_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3559_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3596_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
if (lean_obj_tag(v_a_3560_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; 
lean_dec_ref(v_tail_3558_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
v_a_3564_ = lean_ctor_get(v_a_3560_, 0);
lean_inc(v_a_3564_);
lean_dec_ref(v_a_3560_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v_a_3564_);
v___x_3566_ = v___x_3562_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; size_t v_sz_3571_; size_t v___x_3572_; lean_object* v___x_3573_; 
lean_del_object(v___x_3562_);
v_a_3568_ = lean_ctor_get(v_a_3560_, 0);
lean_inc(v_a_3568_);
lean_dec_ref(v_a_3560_);
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
lean_ctor_set(v___x_3570_, 1, v_a_3568_);
v_sz_3571_ = lean_array_size(v_tail_3558_);
v___x_3572_ = ((size_t)0ULL);
v___x_3573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3558_, v_sz_3571_, v___x_3572_, v___x_3570_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec_ref(v_tail_3558_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3587_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3587_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3587_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v_fst_3578_; 
v_fst_3578_ = lean_ctor_get(v_a_3574_, 0);
if (lean_obj_tag(v_fst_3578_) == 0)
{
lean_object* v_snd_3579_; lean_object* v___x_3581_; 
v_snd_3579_ = lean_ctor_get(v_a_3574_, 1);
lean_inc(v_snd_3579_);
lean_dec(v_a_3574_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v_snd_3579_);
v___x_3581_ = v___x_3576_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_snd_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
else
{
lean_object* v_val_3583_; lean_object* v___x_3585_; 
lean_inc_ref(v_fst_3578_);
lean_dec(v_a_3574_);
v_val_3583_ = lean_ctor_get(v_fst_3578_, 0);
lean_inc(v_val_3583_);
lean_dec_ref(v_fst_3578_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v_val_3583_);
v___x_3585_ = v___x_3576_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_val_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
v_a_3588_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3573_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3573_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v_tail_3558_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
v_a_3597_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3559_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3559_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3605_, lean_object* v_init_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3605_, v_init_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v_lctx_3618_; lean_object* v_decls_3619_; lean_object* v_result_3620_; lean_object* v___x_3621_; 
v_lctx_3618_ = lean_ctor_get(v_a_3613_, 2);
v_decls_3619_ = lean_ctor_get(v_lctx_3618_, 1);
lean_inc_ref(v_decls_3619_);
v_result_3620_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3621_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3619_, v_result_3620_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_Meta_getPropHyps(v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v_res_3627_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3632_ = l_Lean_MessageData_ofFormat(v___x_3631_);
return v___x_3632_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3635_, lean_object* v___x_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
lean_inc(v___x_3636_);
lean_inc(v_mvarId_3635_);
v___x_3642_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3635_, v___x_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v___x_3643_; 
lean_dec_ref(v___x_3642_);
lean_inc(v_mvarId_3635_);
v___x_3643_ = l_Lean_MVarId_getType(v_mvarId_3635_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref(v___x_3643_);
v___x_3645_ = lean_box(0);
lean_inc(v___y_3640_);
lean_inc_ref(v___y_3639_);
lean_inc(v___y_3638_);
lean_inc_ref(v___y_3637_);
v___x_3646_ = l_Lean_Meta_synthInstance(v_a_3644_, v___x_3645_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref(v___x_3646_);
lean_inc(v_mvarId_3635_);
v___x_3648_ = l_Lean_mkMVar(v_mvarId_3635_);
lean_inc(v___y_3640_);
lean_inc_ref(v___y_3639_);
lean_inc(v___y_3638_);
lean_inc_ref(v___y_3637_);
v___x_3649_ = l_Lean_Meta_isExprDefEq(v___x_3648_, v_a_3647_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3661_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3661_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3661_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
uint8_t v___x_3654_; 
v___x_3654_ = lean_unbox(v_a_3650_);
lean_dec(v_a_3650_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_del_object(v___x_3652_);
v___x_3655_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3656_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3636_, v_mvarId_3635_, v___x_3655_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
return v___x_3656_;
}
else
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___x_3636_);
lean_dec(v_mvarId_3635_);
v___x_3657_ = lean_box(0);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3657_);
v___x_3659_ = v___x_3652_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___x_3636_);
lean_dec(v_mvarId_3635_);
v_a_3662_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3649_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3649_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___x_3636_);
lean_dec(v_mvarId_3635_);
v_a_3670_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3646_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3646_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___x_3636_);
lean_dec(v_mvarId_3635_);
v_a_3678_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3643_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3643_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___x_3636_);
lean_dec(v_mvarId_3635_);
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3686_, lean_object* v___x_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3686_, v___x_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v___x_3703_; lean_object* v___f_3704_; lean_object* v___x_3705_; 
v___x_3703_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3697_);
v___f_3704_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3704_, 0, v_mvarId_3697_);
lean_closure_set(v___f_3704_, 1, v___x_3703_);
v___x_3705_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3697_, v___f_3704_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_MVarId_inferInstance(v_mvarId_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object* v_x_3713_){
_start:
{
switch(lean_obj_tag(v_x_3713_))
{
case 0:
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_unsigned_to_nat(0u);
return v___x_3714_;
}
case 1:
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_unsigned_to_nat(1u);
return v___x_3715_;
}
default: 
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_unsigned_to_nat(2u);
return v___x_3716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object* v_x_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_Meta_TacticResultCNM_ctorIdx(v_x_3717_);
lean_dec(v_x_3717_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3719_, lean_object* v_k_3720_){
_start:
{
if (lean_obj_tag(v_t_3719_) == 2)
{
lean_object* v_mvarId_3721_; lean_object* v___x_3722_; 
v_mvarId_3721_ = lean_ctor_get(v_t_3719_, 0);
lean_inc(v_mvarId_3721_);
lean_dec_ref(v_t_3719_);
v___x_3722_ = lean_apply_1(v_k_3720_, v_mvarId_3721_);
return v___x_3722_;
}
else
{
lean_dec(v_t_3719_);
return v_k_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3723_, lean_object* v_ctorIdx_3724_, lean_object* v_t_3725_, lean_object* v_h_3726_, lean_object* v_k_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3725_, v_k_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3729_, lean_object* v_ctorIdx_3730_, lean_object* v_t_3731_, lean_object* v_h_3732_, lean_object* v_k_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3729_, v_ctorIdx_3730_, v_t_3731_, v_h_3732_, v_k_3733_);
lean_dec(v_ctorIdx_3730_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3735_, lean_object* v_closed_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3735_, v_closed_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3738_, lean_object* v_t_3739_, lean_object* v_h_3740_, lean_object* v_closed_3741_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3739_, v_closed_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3743_, lean_object* v_noChange_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3743_, v_noChange_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3746_, lean_object* v_t_3747_, lean_object* v_h_3748_, lean_object* v_noChange_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3747_, v_noChange_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3751_, lean_object* v_modified_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3751_, v_modified_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3754_, lean_object* v_t_3755_, lean_object* v_h_3756_, lean_object* v_modified_3757_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3755_, v_modified_3757_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_){
_start:
{
lean_object* v___y_3769_; uint8_t v___y_3770_; lean_object* v_a_3775_; lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_MVarId_getType(v_g_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3781_ = lean_unsigned_to_nat(1u);
v___x_3782_ = lean_mk_empty_array_with_capacity(v___x_3781_);
v___x_3783_ = lean_array_push(v___x_3782_, v_a_3779_);
lean_inc(v_a_3766_);
lean_inc_ref(v_a_3765_);
lean_inc(v_a_3764_);
lean_inc_ref(v_a_3763_);
v___x_3784_ = l_Lean_Meta_mkAppM(v___x_3780_, v___x_3783_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref(v___x_3784_);
v___x_3786_ = lean_box(0);
v___x_3787_ = l_Lean_Meta_synthInstance(v_a_3785_, v___x_3786_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3796_; 
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; 
v_unused_3797_ = lean_ctor_get(v___x_3787_, 0);
lean_dec(v_unused_3797_);
v___x_3789_ = v___x_3787_;
v_isShared_3790_ = v_isSharedCheck_3796_;
goto v_resetjp_3788_;
}
else
{
lean_dec(v___x_3787_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3796_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
uint8_t v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3794_; 
v___x_3791_ = 1;
v___x_3792_ = lean_box(v___x_3791_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3792_);
v___x_3794_ = v___x_3789_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
else
{
lean_object* v_a_3798_; 
v_a_3798_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3787_);
v_a_3775_ = v_a_3798_;
goto v___jp_3774_;
}
}
else
{
lean_object* v_a_3799_; 
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
v_a_3799_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3799_);
lean_dec_ref(v___x_3784_);
v_a_3775_ = v_a_3799_;
goto v___jp_3774_;
}
}
else
{
lean_object* v_a_3800_; 
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
v_a_3800_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3800_);
lean_dec_ref(v___x_3778_);
v_a_3775_ = v_a_3800_;
goto v___jp_3774_;
}
v___jp_3768_:
{
if (v___y_3770_ == 0)
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
lean_dec_ref(v___y_3769_);
v___x_3771_ = lean_box(v___y_3770_);
v___x_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
return v___x_3772_;
}
else
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___y_3769_);
return v___x_3773_;
}
}
v___jp_3774_:
{
uint8_t v___x_3776_; 
v___x_3776_ = l_Lean_Exception_isInterrupt(v_a_3775_);
if (v___x_3776_ == 0)
{
uint8_t v___x_3777_; 
lean_inc_ref(v_a_3775_);
v___x_3777_ = l_Lean_Exception_isRuntime(v_a_3775_);
v___y_3769_ = v_a_3775_;
v___y_3770_ = v___x_3777_;
goto v___jp_3768_;
}
else
{
v___y_3769_ = v_a_3775_;
v___y_3770_ = v___x_3776_;
goto v___jp_3768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_MVarId_isSubsingleton(v_g_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3824_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3825_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3826_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3827_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3824_, v___x_3825_, v___x_3826_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3829_;
}
}
lean_object* runtime_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_debug_terminalTacticsAsSorry = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_debug_terminalTacticsAsSorry);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_tactic_skipAssignedInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_tactic_skipAssignedInstances);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Util(builtin);
}
#ifdef __cplusplus
}
#endif
